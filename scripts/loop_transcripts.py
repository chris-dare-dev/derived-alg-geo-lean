#!/usr/bin/env python3
"""Archive agent session transcripts, and read loop runs back out of them.

WHY THIS EXISTS. The loop is judged by one thing: a handed-over issue or
milestone finishes without the owner stepping in. When a run does stop, the
evidence of why is in the runtime's own transcript, and that evidence is hard
to use where it lies:

* It is scattered. Codex writes `<home>/sessions/**/rollout-*.jsonl`, moves
  archived threads to `<home>/archived_sessions/`, and this machine runs more
  than one Codex home (`~/.codex`, `~/.codex-accounts/<account>/`). Claude Code
  writes `~/.claude/projects/<slug>/<session>.jsonl`, with its subagents under
  `<session>/subagents/`.
* It is enormous and split. A run is a root thread plus every reviewer and
  scout it spawned, each in its own file. Measured on 2026-09-24: one Codex
  root thread had reached 196 MB with 114 subagent threads beside it.
* It is not kept. Claude Code deletes transcripts after `cleanupPeriodDays`
  (30 by default), and nothing records which Codex thread was which run.

`sync` copies every transcript that touches this repository into one local
archive, groups each root thread with its subagents into a *run*, and writes a
digest a person or an agent can read: the owner's messages in full, every point
the run stopped and what it said there, every question it asked, where its tool
calls went, and one line per subagent. `list`, `stops`, `profile` and `show`
read the archive back, across runs, after the originals are gone.

NEVER IN GIT. This repository is public, and a transcript carries every tool
output the agent saw. The archive defaults to `~/.loop-runs/transcripts`
(override with `--archive` or `LOOP_TRANSCRIPTS_DIR`), is created owner-only,
and keeps lossless gzip copies of the originals. Digests, caches and command
tables redact credential-shaped strings; the raw copies deliberately do not.

WHAT A STOP IS. A turn ends -- `task_complete` in Codex, the last assistant
text before new input in Claude Code. If the owner's next message is what
starts the next turn, the run *stopped for the owner*, and the gap is time the
loop sat idle. If the next turn started without the owner -- a Codex goal
auto-continuing, a background agent reporting back -- the stop was
*auto-continued*: the agent wanted to stop and the runtime pushed it on, which
is still a protocol signal worth reading. The last turn of a transcript *ends*
it, or is still waiting. Only a root thread's stops count; a subagent's turn
end is a return to its parent.

FORKED THREADS REPLAY THEIR PARENT. A Codex subagent spawned with its parent's
history begins with a second `session_meta` and a copy of the parent's turns,
owner messages included. Only items stamped with the thread's own id, and the
turns that contain them, are the thread's own; reading the replay as the
subagent's work would count every owner message once per subagent. The
subagent's task arrives encrypted; only its name is readable.

CATEGORIES ARE A TRIAGE AID. Commands are classified by the program they run
and the paths they touch -- `controller`, `openspec` and `loop-state` are the
protocol; `lean-edit`, `lean-build` and `lean-read` are the mathematics. The
rules are `categorize_command` and `categorize_paths`, and they are meant to be
argued with: each run's command table keeps every command's text, so any
classification can be checked. Stop tags are keyword matches, not verdicts.
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import re
import shutil
import subprocess
import sys
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Callable, Iterable, Iterator

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from loop_tokens import Usage, claude_home, coerce_int, parse_timestamp  # noqa: E402

try:
    from _output import force_utf8_output
except ImportError:  # pragma: no cover - direct invocation from another cwd
    def force_utf8_output() -> None:
        """Best-effort UTF-8 output fallback for standalone invocation."""


ARCHIVE_SCHEMA = "derived-alg-geo-lean.loop-run/v1/transcript-archive"
RUN_SCHEMA = "derived-alg-geo-lean.loop-run/v1/transcript-run"
#: Bump when a reader or the event model changes: every archived thread is
#: then re-read, from its source or from its raw copy, on the next sync.
PARSER_VERSION = 1
#: Bump when `analyze` or a renderer changes: every run is then rewritten
#: from its cached threads, without re-reading any transcript.
ANALYSIS_VERSION = 3
DEFAULT_ARCHIVE = Path.home() / ".loop-runs" / "transcripts"
RUNTIMES = ("codex", "claude")

PROTOCOL = ("controller", "openspec", "loop-state")
MATHEMATICS = ("lean-edit", "lean-build", "lean-read")


class TranscriptError(RuntimeError):
    """A user-actionable error in archiving or reporting."""


# --------------------------------------------------------------------------
# Small helpers
# --------------------------------------------------------------------------


def iso(value: datetime | None) -> str:
    if value is None:
        return ""
    return value.astimezone(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def seconds_between(start: str, end: str) -> float:
    a, b = parse_timestamp(start), parse_timestamp(end)
    if a is None or b is None:
        return 0.0
    return max((b - a).total_seconds(), 0.0)


def human(seconds: float | None) -> str:
    if seconds is None:
        return "-"
    seconds = int(round(seconds))
    if seconds < 60:
        return f"{seconds}s"
    hours, minutes = divmod(seconds // 60, 60)
    if hours < 24:
        return f"{hours}h{minutes:02d}m" if hours else f"{minutes}m"
    days, hours = divmod(hours, 24)
    return f"{days}d{hours:02d}h"


def clock(stamp: str) -> str:
    """`2026-09-22T22:05:23Z` -> `09-22 22:05`."""

    return f"{stamp[5:10]} {stamp[11:16]}" if len(stamp) >= 16 else stamp or "?"


def one_line(text: str, limit: int) -> str:
    flat = " ".join(str(text).split())
    return flat if len(flat) <= limit else flat[: max(limit - 1, 0)] + "…"


def quote(text: str) -> str:
    lines = str(text).strip().splitlines()
    return "\n".join("> " + line if line.strip() else ">" for line in lines) or ">"


def cell(text: str, limit: int) -> str:
    return one_line(text, limit).replace("|", "/")


# Credential shapes. A match is replaced wholesale or, for `key = value`
# shapes, only in its value. Raw archive copies are never redacted.
_SECRETS = (
    re.compile(r"\b(?:ghp|gho|ghu|ghs|ghr)_[A-Za-z0-9]{30,}"),
    re.compile(r"\bgithub_pat_[A-Za-z0-9_]{40,}"),
    re.compile(r"\bsk-(?:ant-|proj-)?[A-Za-z0-9_-]{20,}"),
    re.compile(r"\b(?:AKIA|ASIA)[0-9A-Z]{16}\b"),
    re.compile(r"\bpul-[0-9a-f]{40}\b"),
    re.compile(r"\bxox[abprs]-[A-Za-z0-9-]{10,}"),
    re.compile(r"-----BEGIN [A-Z ]*PRIVATE KEY-----.*?-----END [A-Z ]*PRIVATE KEY-----", re.S),
    re.compile(r"(?i)\bbearer\s+[A-Za-z0-9._~+/=-]{20,}"),
)
_KEYED_SECRET = re.compile(
    r"(?i)\b((?:password|passwd|secret|api[_-]?key|access[_-]?key|auth[_-]?token)\s*[=:]\s*)"
    r"(['\"]?)[^\s'\"]{8,}\2"
)


def redact(text: str) -> str:
    if not text:
        return text
    for pattern in _SECRETS:
        text = pattern.sub("[REDACTED]", text)
    return _KEYED_SECRET.sub(lambda match: match.group(1) + "[REDACTED]", text)


def raw_lines(path: Path) -> Iterator[str]:
    """Lines of a transcript, plain or gzip-archived, tolerating a partial write."""

    opener: Callable[..., Any] = gzip.open if path.suffix == ".gz" else open
    try:
        handle = opener(path, "rt", encoding="utf-8", errors="replace")
    except OSError:
        return
    with handle:
        try:
            for line in handle:
                if line.strip():
                    yield line
        except (OSError, EOFError):
            return  # a truncated gzip tail; everything before it was read


def json_lines(path: Path) -> Iterator[dict[str, Any]]:
    for line in raw_lines(path):
        try:
            entry = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(entry, dict):
            yield entry


# --------------------------------------------------------------------------
# Classification
# --------------------------------------------------------------------------

_SEGMENT = re.compile(r"\s*(?:&&|\|\||;|\||\n)\s*")
_ASSIGNMENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*=")
_PREFIX_WORDS = {"env", "time", "nice", "command", "exec", "sudo", "nohup", "(", "{", "then", "do", "!", "if", "while"}

_CONTROLLER = re.compile(
    r"loop_engine\.py|loop_recovery\.py|loop_tokens\.py|loop_transcripts\.py|"
    r"validate_loop_specs|pr_queue\.py|loop-authority|skills/run-loop"
)
_OPENSPEC_PATH = re.compile(r"(?:^|[\s/'\"=:])openspec/|\.agents/skills/openspec")
_OPENSPEC_RUNNER = re.compile(r"\b(?:npx|pnpm|dlx|bunx)\b.*\bopenspec\b")
_LOOP_STATE = re.compile(r"\.loop-runs|loop-specs/|\bledgers?\b|friction")
_LEAN_SOURCE = re.compile(r"\.lean\b|DerivedAlgGeo/|Mathlib/|\.lake/packages")
_GATES = re.compile(r"scripts/check_|scripts/[\w./-]+\.(?:py|sh)\b|-m unittest|pytest")
_INSTRUCTIONS = re.compile(r"AGENTS\.md|CLAUDE\.md|SKILL\.md|CONTRIBUTING\.md|(?:^|[\s/'\"])docs/")
_CI_WATCH = re.compile(r"\bgh\s+run\s+watch\b|\bgh\s+pr\s+checks\b.*--watch")
_NOTABLE_GH = re.compile(
    r"\bgh\s+(?:pr\s+(?:create|merge|ready|edit|close|comment|review|reopen)|"
    r"issue\s+(?:create|edit|close|comment|reopen)|api\s+.*-X\s*(?:POST|PATCH|PUT|DELETE)|"
    r"workflow\s+run|run\s+rerun|label\s+)"
)
_NOTABLE_GIT = re.compile(r"\bgit\s+(?:push|commit|rebase|merge|reset|cherry-pick|worktree\s+add)\b")


def invocations(command: str) -> Iterator[list[str]]:
    """The words of each simple command in a shell line, program first.

    Leading assignments and wrappers (`env`, `sudo`, `timeout 60`, ...) are
    dropped, so `GH_TOKEN=x gh pr merge 12` starts with `gh`. A heredoc's body
    lines start with whatever the body says, which keeps text that merely
    mentions a command from counting as running it.
    """

    for segment in _SEGMENT.split(command):
        words = segment.strip().split()
        while words and (_ASSIGNMENT.match(words[0]) or words[0] in _PREFIX_WORDS):
            words.pop(0)
        if words and words[0] == "timeout":
            words = words[2:]
        if words:
            yield [os.path.basename(words[0].strip("'\"()")), *words[1:]]


def programs(command: str) -> list[str]:
    """The program each simple command in a shell line runs, by basename."""

    return [words[0] for words in invocations(command)]


def categorize_command(command: str) -> str:
    """Bucket a shell command by what it spends its time on.

    Earlier rules win: reading the controller's source is `controller` even
    through `git show`, and `cd <repo> && lake build` is `lean-build` although
    it also runs `cd`.
    """

    progs = set(programs(command))
    if _CONTROLLER.search(command):
        return "controller"
    if "openspec" in progs or _OPENSPEC_PATH.search(command) or _OPENSPEC_RUNNER.search(command):
        return "openspec"
    if _LOOP_STATE.search(command):
        return "loop-state"
    if progs & {"lake", "lean"} or "precheck.sh" in command or "seed_worktree_cache" in command:
        return "lean-build"
    if _CI_WATCH.search(command) or "sleep" in progs:
        return "ci-wait"
    if "gh" in progs:
        return "github"
    if _LEAN_SOURCE.search(command):
        return "lean-read"
    if _GATES.search(command):
        return "gates"
    if _INSTRUCTIONS.search(command):
        return "instructions"
    if "git" in progs:
        return "git"
    return "other"


def categorize_paths(paths: Iterable[str], *, reading: bool = False) -> str:
    """Bucket a file edit, or with `reading`, a file read, by the paths it touches."""

    joined = " " + " ".join(paths)
    if _CONTROLLER.search(joined):
        return "controller"
    if _OPENSPEC_PATH.search(joined):
        return "openspec"
    if _LOOP_STATE.search(joined):
        return "loop-state"
    if re.search(r"\.lean\b", joined) or (reading and _LEAN_SOURCE.search(joined)):
        return "lean-read" if reading else "lean-edit"
    if _INSTRUCTIONS.search(joined):
        return "instructions"
    if "scripts/" in joined or ".github/" in joined:
        return "gates"
    return "other"


STOP_TAGS = (
    ("authority", re.compile(r"(?i)\bmay i\b|authori[sz]|permission|not (?:allowed|permitted)|\bgrants?\b|approv")),
    ("merge-first", re.compile(r"(?i)please merge|merge (?:it|#?\d+|the)|planning pr|bootstrap pr|on `?main`? (?:first|before)|until .* merges")),
    ("controller", re.compile(r"(?i)manifest|preflight|\bledger|digest|loop_engine|round cap|review (?:slot|round)|terminal|exact[- ]base")),
    ("openspec", re.compile(r"(?i)openspec|proposal|tasks\.md|design\.md")),
    ("scope", re.compile(r"(?i)should i\b|do you (?:want|mean)|which (?:one|route|option)|confirm whether|clarif|\bor do you\b")),
    ("owner-only", re.compile(r"(?i)\bsudo\b|password|credential|\blog ?in\b|2fa")),
    ("ci", re.compile(r"(?i)\bci\b|checks? (?:are |is )?(?:pending|running|queued|green|red)|workflow run")),
    ("blocked", re.compile(r"(?i)\bblocked\b|\bblocker")),
    ("done", re.compile(r"(?i)\b(?:merged|completed?|finished|closed)\b")),
)


def stop_tags(stop_text: str, asks: Iterable[str] = ()) -> list[str]:
    """Keyword tags for a stop, read from its questions and its closing lines.

    A final message is usually a report that mentions everything the turn
    touched; what it is waiting on sits in the last lines, and in any question
    it asked. Tagging the whole report tags every stop with everything.
    """

    text = stop_text.strip()[-600:] + "\n" + "\n".join(asks)
    return [name for name, pattern in STOP_TAGS if pattern.search(text)]


# --------------------------------------------------------------------------
# The normalized model
# --------------------------------------------------------------------------


@dataclass
class Event:
    """One thing that happened in a thread.

    `kind` is one of: owner, task, commentary, final, ask, stop, abort, tool,
    spawn, notice, compaction. A tool event carries a category, its duration in
    seconds when the runtime recorded one, and its exit code when it failed. An
    ask carries, as `dur`, how long the owner took when the runtime blocked on
    the answer.
    """

    t: str
    kind: str
    text: str = ""
    cat: str = ""
    dur: float | None = None
    exit: int | None = None


@dataclass
class Thread:
    runtime: str
    id: str
    parent: str | None
    role: str
    title: str
    source: str
    start: str = ""
    end: str = ""
    origin: str = ""
    cwd: str = ""
    branch: str = ""
    client: str = ""
    model: str = ""
    repo_hits: int = 0
    usage: dict[str, int] = field(default_factory=dict)
    events: list[Event] = field(default_factory=list)

    @property
    def is_root(self) -> bool:
        return self.parent is None

    def add(self, stamp: str, kind: str, text: str = "", **extra: Any) -> Event:
        event = Event(t=stamp, kind=kind, text=redact(text), **extra)
        self.events.append(event)
        return event

    def finish(self) -> None:
        self.events.sort(key=lambda event: event.t)
        if self.events:
            self.start = self.start or self.events[0].t
            self.end = max(self.events[-1].t, self.start)
        else:
            self.end = self.start
        if not self.title:
            first = next((e.text for e in self.events if e.kind in ("owner", "task")), "")
            self.title = one_line(first, 80)

    def to_json(self) -> dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_json(cls, data: dict[str, Any]) -> "Thread":
        events = [Event(**entry) for entry in data.get("events", [])]
        return cls(**{k: v for k, v in data.items() if k != "events"}, events=events)


class RepoMatcher:
    """Counts how often working directories, commands and paths name this repository."""

    def __init__(self, needles: Iterable[str]):
        self.needles = [needle for needle in needles if needle]

    def hits(self, text: str) -> int:
        return sum(text.count(needle) for needle in self.needles) if text else 0


def usage_from(record: dict[str, Any], *, inclusive_input: bool) -> Usage:
    """One response's usage on the disjoint buckets of `loop_tokens.Usage`.

    Codex's `input_tokens` includes its cached prefix; Claude's does not.
    """

    if inclusive_input:
        total = coerce_int(record.get("input_tokens"))
        cached = coerce_int(record.get("cached_input_tokens"))
        return Usage(max(total - cached, 0), cached, coerce_int(record.get("cache_write_input_tokens")),
                     coerce_int(record.get("output_tokens")), coerce_int(record.get("reasoning_output_tokens")))
    details = record.get("output_tokens_details")
    return Usage(coerce_int(record.get("input_tokens")), coerce_int(record.get("cache_read_input_tokens")),
                 coerce_int(record.get("cache_creation_input_tokens")), coerce_int(record.get("output_tokens")),
                 coerce_int(details.get("thinking_tokens")) if isinstance(details, dict) else 0)


# --------------------------------------------------------------------------
# Codex reader
# --------------------------------------------------------------------------

_CODEX_HEAD = re.compile(r'"type":\s*"(\w+)"(?:,\s*"payload":\s*\{\s*"type":\s*"(\w+)")?')
_CODEX_SKIP_TYPES = {"world_state", "compacted", "inter_agent_communication_metadata"}
_CODEX_SKIP_PAIRS = {("response_item", "reasoning"), ("response_item", "custom_tool_call_output"),
                     ("response_item", "custom_tool_call"), ("event_msg", "token_count")}
_CALL_ID = re.compile(r'"call_id":\s*"([^"]+)"')
_STAMP = re.compile(r'"timestamp":\s*"([^"]+)"')
_UUID_TAIL = re.compile(r"([0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12})\.jsonl(?:\.gz)?$")
_WAIT_TOOLS = {"sleep", "wait", "wait_agent"}
_AGENT_TOOLS = {"spawn_agent", "send_message", "followup_task", "list_agents", "interrupt_agent"}


def codex_homes(explicit: list[Path] | None = None) -> list[Path]:
    """Every Codex home on this machine, without duplicates."""

    if explicit:
        candidates = list(explicit)
    else:
        candidates = []
        if os.environ.get("CODEX_HOME"):
            candidates.append(Path(os.environ["CODEX_HOME"]))
        candidates.append(Path.home() / ".codex")
        accounts = Path.home() / ".codex-accounts"
        if accounts.is_dir():
            candidates.extend(sorted(p for p in accounts.iterdir() if p.is_dir()))
    homes: list[Path] = []
    for home in candidates:
        try:
            resolved = home.expanduser().resolve()
        except OSError:
            continue
        if resolved in homes:
            continue
        if (resolved / "sessions").is_dir() or (resolved / "archived_sessions").is_dir():
            homes.append(resolved)
    return homes


def codex_titles(home: Path) -> dict[str, str]:
    titles: dict[str, str] = {}
    for entry in json_lines(home / "session_index.jsonl"):
        if isinstance(entry.get("id"), str) and isinstance(entry.get("thread_name"), str):
            titles[entry["id"]] = entry["thread_name"]
    return titles


def codex_thread_id(path: Path) -> str:
    match = _UUID_TAIL.search(path.name)
    return match.group(1) if match else path.name.split(".")[0]


def _texts(content: Any) -> str:
    if isinstance(content, str):
        return content
    parts: list[str] = []
    if isinstance(content, list):
        for block in content:
            if not isinstance(block, dict):
                continue
            if isinstance(block.get("text"), str):
                parts.append(block["text"])
            elif block.get("type") in ("image", "input_image", "localImage"):
                parts.append("[image]")
    return "\n".join(parts)


def _duration(value: Any) -> float | None:
    if isinstance(value, dict):
        return coerce_int(value.get("secs")) + coerce_int(value.get("nanos")) / 1e9
    if isinstance(value, (int, float)) and not isinstance(value, bool):
        return float(value)
    return None


def _shell_text(command: Any) -> str:
    if isinstance(command, list):
        words = [str(word) for word in command]
        if len(words) >= 3 and words[1] in ("-lc", "-c"):
            return words[2]
        return " ".join(words)
    return str(command or "")


def _failure_tail(output: Any, limit: int = 240) -> str:
    lines = [line for line in str(output or "").strip().splitlines() if line.strip()]
    return one_line(" | ".join(lines[-3:]), limit) if lines else ""


def _ask_text(arguments: Any) -> str:
    try:
        data = json.loads(arguments) if isinstance(arguments, str) else arguments
    except json.JSONDecodeError:
        return str(arguments)
    rendered: list[str] = []
    questions = data.get("questions") if isinstance(data, dict) else None
    for question in questions if isinstance(questions, list) else []:
        if not isinstance(question, dict):
            continue
        text = str(question.get("question") or question.get("title") or "")
        options = question.get("options")
        if isinstance(options, list) and options:
            text += " [options: " + " | ".join(str(option) for option in options) + "]"
        rendered.append(text)
    return "\n".join(rendered) or str(arguments)


def read_codex_thread(path: Path, thread_id: str, titles: dict[str, str], matcher: RepoMatcher) -> Thread:
    thread = Thread(runtime="codex", id=thread_id, parent=None, role="root",
                    title=titles.get(thread_id, ""), source=str(path))
    metas = 0
    replayed = False  # a forked subagent: its parent's history comes first
    own_started = False
    own_turns: set[str] = set()
    pending: dict[str, Event] = {}
    seen_usage: set[str] = set()
    usage = Usage()

    for line in raw_lines(path):
        head = _CODEX_HEAD.search(line, 0, 400)
        if not head:
            continue
        kind, sub = head.group(1), head.group(2)
        if kind in _CODEX_SKIP_TYPES or (kind, sub) in _CODEX_SKIP_PAIRS:
            continue
        if kind == "response_item" and sub == "function_call_output":
            match = _CALL_ID.search(line, 0, 400)
            event = pending.pop(match.group(1), None) if match else None
            if event is not None:
                if event.kind == "ask" and "failed to parse function arguments" in line[:1200]:
                    thread.events.remove(event)  # a malformed call the agent retried; not a second question
                else:
                    stamp = _STAMP.search(line, 0, 200)
                    end = iso(parse_timestamp(stamp.group(1))) if stamp else ""
                    if event.kind == "tool":
                        event.dur = seconds_between(event.t, end) if end else None
            continue
        try:
            entry = json.loads(line)
        except json.JSONDecodeError:
            continue
        payload = entry.get("payload")
        if not isinstance(payload, dict):
            continue
        stamp = iso(parse_timestamp(entry.get("timestamp")))

        if kind == "session_meta":
            metas += 1
            if metas > 1:
                replayed = True
                continue
            thread.start = iso(parse_timestamp(payload.get("timestamp"))) or stamp
            thread.cwd = str(payload.get("cwd") or "")
            # `codex exec` threads are headless: their first message is a
            # prompt from whatever launched them, not from the owner.
            thread.origin = "exec" if payload.get("source") == "exec" else str(payload.get("thread_source") or "")
            parent = payload.get("parent_thread_id")
            if isinstance(parent, str) and parent:
                thread.parent = parent
                thread.role = str(payload.get("agent_path") or payload.get("agent_nickname") or "subagent")
            git = payload.get("git") if isinstance(payload.get("git"), dict) else {}
            thread.branch = str(git.get("branch") or "")
            thread.client = " ".join(str(payload.get(k) or "") for k in ("originator", "cli_version")).strip()
            thread.repo_hits += matcher.hits(thread.cwd) + matcher.hits(str(git.get("repository_url") or ""))
            continue
        if kind != "session_meta" and not replayed:
            own_started = True
        if kind == "turn_context":
            if own_started and isinstance(payload.get("model"), str):
                thread.model = payload["model"]
            continue
        if kind == "token_usage_record":
            owner = payload.get("thread_id")
            if (owner and owner != thread_id) or (not owner and not own_started):
                continue
            key = str(payload.get("response_id") or f"{thread_id}:{entry.get('ordinal')}")
            record = payload.get("usage")
            if key not in seen_usage and isinstance(record, dict):
                seen_usage.add(key)
                usage = usage + usage_from(record, inclusive_input=True)
            continue
        if kind == "event_msg" and sub == "item_completed":
            if payload.get("thread_id") not in (None, thread_id):
                continue
            own_started = True
            if isinstance(payload.get("turn_id"), str):
                own_turns.add(payload["turn_id"])
            item = payload.get("item")
            if isinstance(item, dict):
                _codex_item(item, stamp, thread, matcher)
            continue
        addressed_here = kind == "response_item" and sub == "agent_message" and payload.get("recipient") == thread.role
        if not own_started and not addressed_here:
            continue  # the parent's replayed history; a task addressed to this thread is its own
        if kind == "event_msg" and sub in ("task_complete", "turn_aborted"):
            if replayed and payload.get("turn_id") not in own_turns:
                continue
            if sub == "task_complete":
                thread.add(stamp, "stop", str(payload.get("last_agent_message") or ""))
            else:
                thread.add(stamp, "abort", str(payload.get("reason") or "aborted"))
        elif kind == "event_msg" and sub == "thread_goal_updated":
            goal = payload.get("goal") if isinstance(payload.get("goal"), dict) else payload
            if isinstance(goal, dict) and goal.get("status"):
                thread.add(stamp, "notice", f"goal {goal['status']}: {one_line(str(goal.get('objective') or ''), 160)}")
        elif kind == "response_item" and sub == "agent_message":
            # Inter-agent traffic: the header is readable, the payload encrypted.
            header = _texts(payload.get("content"))
            fields = dict(re.findall(r"(Message Type|Task name|Sender):\s*(\S+)", header))
            sender = fields.get("Sender") or str(payload.get("author") or "?")
            if thread.is_root:
                thread.add(stamp, "notice", f"message from {sender}")
            elif fields.get("Message Type") == "NEW_TASK" or not any(e.kind == "task" for e in thread.events):
                thread.add(stamp, "task", f"{fields.get('Task name') or thread.role} (from {sender})")
            else:
                thread.add(stamp, "notice", f"message from {sender}")
        elif kind == "response_item" and sub == "function_call":
            name = str(payload.get("name") or "")
            if name == "request_user_input_async":
                event = thread.add(stamp, "ask", _ask_text(payload.get("arguments")))
            elif name in _WAIT_TOOLS:
                event = thread.add(stamp, "tool", name, cat="waiting")
            elif name in _AGENT_TOOLS:
                event = thread.add(stamp, "tool", name, cat="agents")
            else:
                event = thread.add(stamp, "tool", "browser js" if name == "js" else name, cat="other")
            if isinstance(payload.get("call_id"), str):
                pending[payload["call_id"]] = event

    thread.usage = usage.as_dict()
    thread.finish()
    return thread


def _codex_item(item: dict[str, Any], stamp: str, thread: Thread, matcher: RepoMatcher) -> None:
    kind = item.get("type")
    if kind == "UserMessage":
        text = _texts(item.get("content"))
        heartbeat = re.match(r"\s*<heartbeat>.*?<automation_id>(.*?)</automation_id>", text, re.S)
        if heartbeat:
            # A scheduled automation re-prompting the thread: it keeps a run
            # going, and it is not the owner. The owner's own messages come
            # from the desktop client and carry its `client_id`.
            thread.add(stamp, "notice", f"heartbeat from automation {heartbeat.group(1).strip()}")
        elif not thread.is_root or (thread.origin == "exec" and not any(e.kind == "task" for e in thread.events)):
            thread.add(stamp, "task", text)
        else:
            thread.add(stamp, "owner", text)
    elif kind == "AgentMessage":
        text = _texts(item.get("content"))
        if text.strip():
            thread.add(stamp, "final" if item.get("phase") == "final_answer" else "commentary", text)
    elif kind == "CommandExecution":
        command = _shell_text(item.get("command"))
        thread.repo_hits += matcher.hits(command) + matcher.hits(str(item.get("cwd") or ""))
        exit_code = item.get("exit_code")
        event = thread.add(stamp, "tool", command, cat=categorize_command(command), dur=_duration(item.get("duration")),
                           exit=exit_code if isinstance(exit_code, int) and not isinstance(exit_code, bool) else None)
        if event.exit not in (None, 0):
            event.text += "  ⟶ " + redact(_failure_tail(item.get("aggregated_output") or item.get("stderr")))
    elif kind == "FileChange":
        changes = item.get("changes") if isinstance(item.get("changes"), dict) else {}
        paths = sorted(changes)
        thread.repo_hits += sum(matcher.hits(p) for p in paths)
        described = []
        for path in paths:
            change = changes[path] if isinstance(changes[path], dict) else {}
            described.append(f"{change.get('type', 'edit')} {path}")
        thread.add(stamp, "tool", "edit " + "; ".join(described), cat=categorize_paths(paths))
    elif kind == "McpToolCall":
        name = f"{item.get('server', '')}.{item.get('tool', '')}"
        thread.add(stamp, "tool", name, cat="github" if "github" in name else "other", dur=_duration(item.get("duration")))
    elif kind == "Extension":
        action = item.get("action") if isinstance(item.get("action"), dict) else {}
        what = item.get("query") or action.get("url") or ""
        thread.add(stamp, "tool", f"{item.get('kind', 'extension')}: {what}", cat="web")
    elif kind == "SubAgentActivity" and item.get("kind") == "started":
        thread.add(stamp, "spawn", str(item.get("agent_path") or item.get("agent_thread_id") or "subagent"))
    elif kind == "ContextCompaction":
        thread.add(stamp, "compaction")


# --------------------------------------------------------------------------
# Claude Code reader
# --------------------------------------------------------------------------

_CLAUDE_SKIPPED_INPUT = ("<system-reminder>", "<local-command-stdout>", "<local-command-caveat>",
                         "<local-command-stderr>", "Caveat: The messages below")
_EXIT_CODE = re.compile(r"^Exit code (\d+)")


def claude_sources(home: Path) -> list[tuple[Path, str | None]]:
    """(transcript, parent session) for every Claude Code session and subagent file."""

    projects = home / "projects"
    if not projects.is_dir():
        return []
    found: list[tuple[Path, str | None]] = []
    for project in sorted(p for p in projects.iterdir() if p.is_dir()):
        found.extend((path, None) for path in sorted(project.glob("*.jsonl")))
        found.extend((path, path.parent.parent.name) for path in sorted(project.glob("*/subagents/*.jsonl")))
    return found


def claude_thread_id(path: Path, parent: str | None) -> str:
    stem = path.name.split(".")[0]
    return stem if parent is None else f"{parent}:{stem}"


def read_claude_thread(path: Path, thread_id: str, parent: str | None, matcher: RepoMatcher, *,
                       project: str = "", meta: dict[str, Any] | None = None) -> Thread:
    thread = Thread(runtime="claude", id=thread_id, parent=parent, role="root" if parent is None else "subagent",
                    title="", source=str(path), origin="session" if parent is None else "subagent")
    thread.repo_hits += matcher.hits(project)
    if meta:
        thread.role = str(meta.get("agentType") or thread.role)
        thread.title = one_line(str(meta.get("description") or ""), 80)
    titles = {"custom-title": "", "ai-title": ""}
    pending: dict[str, Event] = {}
    seen_usage: set[str] = set()
    usage = Usage()

    for entry in json_lines(path):
        kind = entry.get("type")
        if kind == "custom-title" and isinstance(entry.get("customTitle"), str):
            titles["custom-title"] = entry["customTitle"]
            continue
        if kind == "ai-title" and isinstance(entry.get("aiTitle"), str):
            titles["ai-title"] = entry["aiTitle"]
            continue
        stamp = iso(parse_timestamp(entry.get("timestamp")))
        if not stamp or (parent is None and entry.get("isSidechain")):
            continue  # an older layout kept subagent turns inline; they are not the root's own
        if not thread.cwd and isinstance(entry.get("cwd"), str):
            thread.cwd = entry["cwd"]
            thread.repo_hits += matcher.hits(thread.cwd)
        if not thread.branch and isinstance(entry.get("gitBranch"), str):
            thread.branch = entry["gitBranch"]
        if not thread.client and isinstance(entry.get("version"), str):
            thread.client = f"claude-code {entry['version']}"
        if kind == "system" and entry.get("subtype") == "compact_boundary":
            thread.add(stamp, "compaction")
            continue
        message = entry.get("message")
        if not isinstance(message, dict):
            continue
        if kind == "assistant":
            if isinstance(message.get("model"), str) and not message["model"].startswith("<"):
                thread.model = message["model"]
            key = entry.get("requestId") or message.get("id")
            if isinstance(key, str) and key not in seen_usage and isinstance(message.get("usage"), dict):
                seen_usage.add(key)
                usage = usage + usage_from(message["usage"], inclusive_input=False)
            for block in message.get("content") or []:
                if not isinstance(block, dict):
                    continue
                if block.get("type") == "text" and str(block.get("text") or "").strip():
                    thread.add(stamp, "commentary", block["text"])
                elif block.get("type") == "tool_use":
                    event = _claude_tool(block, stamp, thread, matcher)
                    if event is not None and isinstance(block.get("id"), str):
                        pending[block["id"]] = event
            continue
        if kind != "user" or entry.get("isMeta"):
            continue
        content = message.get("content")
        texts: list[str] = [content] if isinstance(content, str) else []
        for block in content if isinstance(content, list) else []:
            if not isinstance(block, dict):
                continue
            if block.get("type") == "tool_result":
                event = pending.pop(str(block.get("tool_use_id")), None)
                if event is not None:
                    _claude_result(event, block, stamp)
            elif block.get("type") == "text":
                texts.append(str(block.get("text") or ""))
            elif block.get("type") == "image":
                texts.append("[image]")
        text = "\n".join(t for t in texts if t.strip()).strip()
        if not text or text.startswith(_CLAUDE_SKIPPED_INPUT):
            continue
        if parent is not None:
            if not any(e.kind == "task" for e in thread.events):
                thread.add(stamp, "task", text)
        elif text.startswith("[Request interrupted"):
            thread.add(stamp, "abort", "interrupted by owner")
        elif text.startswith(("<task-notification>", "<ci-monitor-event>")):
            thread.add(stamp, "notice", one_line(re.sub(r"<[^>]+>", " ", text), 200))
        elif text.startswith("<command-name>"):
            name = re.search(r"<command-name>(.*?)</command-name>", text)
            args = re.search(r"<command-args>(.*?)</command-args>", text, re.S)
            thread.add(stamp, "owner", f"{name.group(1) if name else '/command'} {args.group(1).strip() if args else ''}".strip())
        else:
            thread.add(stamp, "owner", text)

    thread.title = thread.title or titles["custom-title"] or titles["ai-title"]
    thread.usage = usage.as_dict()
    if thread.is_root:
        _insert_claude_stops(thread)
    thread.finish()
    return thread


def _claude_result(event: Event, block: dict[str, Any], stamp: str) -> None:
    event.dur = seconds_between(event.t, stamp)
    result = _texts(block.get("content"))
    if event.kind == "ask":
        event.text += "\n→ owner answered: " + redact(one_line(result, 400))
        return
    code = _EXIT_CODE.match(result.strip())
    if code:
        event.exit = int(code.group(1))
    elif block.get("is_error"):
        event.exit = 1
    if event.exit not in (None, 0):
        event.text += "  ⟶ " + redact(_failure_tail(result))


def _claude_tool(block: dict[str, Any], stamp: str, thread: Thread, matcher: RepoMatcher) -> Event | None:
    name = str(block.get("name") or "")
    data = block.get("input") if isinstance(block.get("input"), dict) else {}
    if name == "Bash":
        command = str(data.get("command") or "")
        thread.repo_hits += matcher.hits(command)
        return thread.add(stamp, "tool", command, cat=categorize_command(command))
    if name in ("Edit", "Write", "MultiEdit", "NotebookEdit"):
        target = str(data.get("file_path") or data.get("notebook_path") or "")
        thread.repo_hits += matcher.hits(target)
        return thread.add(stamp, "tool", f"edit {target}", cat=categorize_paths([target]))
    if name in ("Read", "Grep", "Glob"):
        target = str(data.get("file_path") or data.get("path") or data.get("pattern") or "")
        thread.repo_hits += matcher.hits(target)
        return thread.add(stamp, "tool", f"{name.lower()} {target}", cat=categorize_paths([target], reading=True))
    if name in ("Agent", "Task"):
        label = f"{data.get('subagent_type') or 'agent'}: {data.get('description') or ''}"
        thread.add(stamp, "spawn", label)
        return thread.add(stamp, "tool", "spawn " + label, cat="agents")
    if name == "AskUserQuestion":
        rendered = []
        for question in data.get("questions") if isinstance(data.get("questions"), list) else []:
            if isinstance(question, dict):
                options = [str(o.get("label")) for o in question.get("options") or [] if isinstance(o, dict)]
                rendered.append(str(question.get("question") or "") + (" [options: " + " | ".join(options) + "]" if options else ""))
        return thread.add(stamp, "ask", "\n".join(rendered) or "AskUserQuestion")
    if name == "ExitPlanMode":
        return thread.add(stamp, "ask", "plan approval requested")
    if name in ("Monitor", "ScheduleWakeup", "TaskOutput"):
        return thread.add(stamp, "tool", name, cat="waiting")
    if name in ("SendMessage", "TaskStop", "ListAgents"):
        return thread.add(stamp, "tool", name, cat="agents")
    if name == "Skill":
        return thread.add(stamp, "tool", f"skill {data.get('skill') or ''}", cat="instructions")
    if "github" in name.lower() or name.startswith("mcp__ccd_pr"):
        return thread.add(stamp, "tool", name, cat="github")
    return thread.add(stamp, "tool", name, cat="other")


def _insert_claude_stops(thread: Thread) -> None:
    """Mark where each Claude Code turn handed control back.

    Claude Code writes no turn-end record, so a turn is taken to end at its
    last assistant text before the next input -- an owner message or a
    background notification -- or at the end of the transcript. An owner
    interrupt ends a turn without a stop: the agent did not choose to stop.
    """

    result: list[Event] = []
    last_text: Event | None = None
    active = False
    for event in thread.events:
        if event.kind in ("owner", "notice") and active:
            result.append(Event(t=last_text.t if last_text else event.t, kind="stop",
                                text=last_text.text if last_text else ""))
        if event.kind in ("owner", "notice", "abort"):
            active, last_text = False, None
        elif event.kind in ("commentary", "tool", "ask", "spawn"):
            active = True
            if event.kind == "commentary":
                last_text = event
        result.append(event)
    if active:
        result.append(Event(t=last_text.t if last_text else result[-1].t, kind="stop",
                            text=last_text.text if last_text else ""))
    thread.events = result


# --------------------------------------------------------------------------
# Runs
# --------------------------------------------------------------------------


def run_key(runtime: str, root_id: str, start: str) -> str:
    tail = re.sub(r"[^0-9A-Za-z-]", "", root_id)[-12:]
    return f"{(start or '0000-00-00')[:10]}-{runtime}-{tail}"


@dataclass
class Run:
    root: Thread
    children: list[Thread]

    @property
    def key(self) -> str:
        return run_key(self.root.runtime, self.root.id, self.root.start)

    @property
    def threads(self) -> list[Thread]:
        return [self.root, *self.children]


def root_of(thread_id: str, parents: dict[str, str | None]) -> str:
    seen = {thread_id}
    current = thread_id
    while True:
        parent = parents.get(current)
        if not parent or parent not in parents or parent in seen:
            return current
        seen.add(parent)
        current = parent


def analyze(run: Run) -> dict[str, Any]:
    """The run-level facts that a digest and the cross-run reports are built from."""

    root = run.root
    events = root.events
    stops: list[dict[str, Any]] = []
    interjections: list[dict[str, str]] = []
    asks: list[Event] = []
    ask_waits: list[float] = []  # asks the runtime blocked on until the owner answered
    last_input = root.start
    stretch_start = root.start
    stretches: list[float] = []
    turn_open = False
    for index, event in enumerate(events):
        if event.kind == "owner":
            if turn_open:
                interjections.append({"t": event.t, "text": event.text})
            turn_open = True
            last_input = event.t
        elif event.kind == "abort":
            turn_open = False
        elif event.kind == "ask":
            asks.append(event)
            if event.dur:
                ask_waits.append(event.dur)
            turn_open = True
        elif event.kind == "stop":
            turn_open = False
            following = next((e for e in events[index + 1:] if e.kind != "stop"), None)
            reply, revived_by = "", ""
            if following is None:
                answered = "end"
            elif following.kind == "owner":
                answered, reply = "owner", following.text
            else:
                answered = "auto"
                revived_by = ("heartbeat" if following.kind == "notice" and "heartbeat" in following.text
                              else "notification" if following.kind == "notice" else "runtime")
            texts = [a.text for a in asks]
            stops.append({
                "t": event.t, "answered_by": answered, "revived_by": revived_by,
                "wait_s": seconds_between(event.t, following.t) if following is not None else None,
                "worked_s": seconds_between(last_input, event.t), "text": event.text,
                "asks": texts, "reply": reply, "tags": stop_tags(event.text, texts),
            })
            asks = []
            last_input = event.t
            if answered != "auto":
                stretches.append(seconds_between(stretch_start, event.t))
                if following is not None:
                    stretch_start = following.t
        elif event.kind in ("tool", "commentary", "final", "spawn"):
            turn_open = True
    if not stops or stops[-1]["answered_by"] != "end":
        stretches.append(seconds_between(stretch_start, root.end))  # still running when the transcript was read

    profile: dict[str, dict[str, float]] = {}
    first_lean_edit = ""
    failures = 0
    created: set[str] = set()
    merged: set[str] = set()
    for thread in run.threads:
        for event in thread.events:
            if event.kind != "tool":
                continue
            if event.exit in (None, 0):
                for words in invocations(event.text):
                    if len(words) >= 3 and words[:2] == ["gh", "pr"] and words[2] in ("create", "merge"):
                        number = next((w.lstrip("#") for w in words[3:] if w.lstrip("#").isdigit()), None)
                        (created if words[2] == "create" else merged).add(number or f"{thread.id}@{event.t}")
            bucket = profile.setdefault(event.cat or "other", {"calls": 0, "seconds": 0.0})
            bucket["calls"] += 1
            bucket["seconds"] += event.dur or 0.0
            failures += event.exit not in (None, 0)
            if event.cat == "lean-edit" and (not first_lean_edit or event.t < first_lean_edit):
                first_lean_edit = event.t
    end = max((t.end for t in run.threads if t.end), default=root.end)
    calls = sum(int(b["calls"]) for b in profile.values())
    share = lambda names: sum(int(profile.get(n, {}).get("calls", 0)) for n in names) / calls if calls else 0.0  # noqa: E731
    narrative = "\n".join(e.text for e in events if e.kind in ("stop", "final", "commentary"))
    prs = sorted({int(n) for n in re.findall(r"/pull/(\d+)", narrative)} | {int(n) for n in re.findall(r"\bPR #(\d+)", narrative)})
    usage = Usage()
    for thread in run.threads:
        u = thread.usage or {}
        usage = usage + Usage(u.get("input_uncached", 0), u.get("input_cached", 0), u.get("cache_write", 0),
                              u.get("output", 0), u.get("reasoning_subset_of_output", 0))
    owner_stops = [s for s in stops if s["answered_by"] == "owner"]
    return {
        "schema": RUN_SCHEMA, "parser": PARSER_VERSION, "analysis": ANALYSIS_VERSION, "key": run.key, "runtime": root.runtime,
        "root_id": root.id, "title": root.title, "origin": root.origin, "client": root.client, "model": root.model,
        "cwd": root.cwd, "branch": root.branch, "start": root.start, "end": end,
        "span_s": seconds_between(root.start, end), "threads": len(run.threads), "subagents": len(run.children),
        "owner_messages": sum(1 for e in events if e.kind == "owner"),
        "owner_interrupts": sum(1 for e in events if e.kind == "abort"),
        "stops": stops,
        "stops_for_owner": len(owner_stops),
        "stops_auto": sum(1 for s in stops if s["answered_by"] == "auto"),
        "asks": sum(len(s["asks"]) for s in stops) + len(asks),
        "open_asks": [a.text for a in asks],
        "interjections": interjections,
        "waiting_on_owner_s": sum(s["wait_s"] or 0.0 for s in owner_stops) + sum(ask_waits),
        "longest_wait_s": max([s["wait_s"] or 0.0 for s in owner_stops] + ask_waits, default=0.0),
        "idle_until_revived_s": sum(s["wait_s"] or 0.0 for s in stops if s["answered_by"] == "auto"),
        "revived_by_heartbeat": sum(1 for s in stops if s["revived_by"] == "heartbeat"),
        "heartbeats": sum(1 for e in events if e.kind == "notice" and "heartbeat" in e.text),
        "longest_autonomous_s": max(stretches, default=seconds_between(root.start, end)),
        "compactions": sum(1 for t in run.threads for e in t.events if e.kind == "compaction"),
        "tool_calls": calls, "failed_calls": failures,
        "protocol_share": share(PROTOCOL), "mathematics_share": share(MATHEMATICS),
        "first_lean_edit": first_lean_edit,
        "first_lean_edit_after_s": seconds_between(root.start, first_lean_edit) if first_lean_edit else None,
        "profile": profile, "prs": prs, "prs_created": len(created), "prs_merged": len(merged),
        "usage": usage.as_dict(),
        "subagent_summaries": [_subagent_summary(t) for t in sorted(run.children, key=lambda t: t.start)],
    }


def _subagent_summary(thread: Thread) -> dict[str, Any]:
    final = next((e.text for e in reversed(thread.events) if e.kind in ("final", "stop") and e.text.strip()), "")
    final = final or next((e.text for e in reversed(thread.events) if e.kind == "commentary"), "")
    return {
        "id": thread.id, "role": thread.role, "title": thread.title, "start": thread.start,
        "span_s": seconds_between(thread.start, thread.end),
        "tool_calls": sum(1 for e in thread.events if e.kind == "tool"),
        "outcome": one_line(final, 300),
    }


# --------------------------------------------------------------------------
# Rendering
# --------------------------------------------------------------------------


def render_digest(run: Run, facts: dict[str, Any]) -> str:
    root = run.root
    first_edit = facts["first_lean_edit_after_s"]
    ends = sum(1 for s in facts["stops"] if s["answered_by"] == "end")
    rows = [
        ("Span", f"{clock(facts['start'])} → {clock(facts['end'])} UTC ({human(facts['span_s'])})"),
        ("Client / model", f"{facts['client'] or '-'} / {facts['model'] or '-'}"),
        ("Working directory", f"`{facts['cwd'] or '-'}`" + (f" on `{facts['branch']}`" if facts["branch"] else "")),
        ("Threads", f"1 root + {facts['subagents']} subagents"),
        ("Owner messages", f"{facts['owner_messages']} ({len(facts['interjections'])} mid-turn, "
                           f"{facts['owner_interrupts']} interrupts)"),
        ("Stops", f"{facts['stops_for_owner']} waited for the owner, {facts['stops_auto']} auto-continued "
                  f"({facts['revived_by_heartbeat']} only by a heartbeat), {ends} ended the transcript"),
        ("Questions asked", str(facts["asks"])),
        ("Idle waiting on owner", f"{human(facts['waiting_on_owner_s'])} total, longest {human(facts['longest_wait_s'])}"),
        ("Idle until auto-revived", f"{human(facts['idle_until_revived_s'])} ({facts['heartbeats']} heartbeats received)"),
        ("Longest autonomous stretch", human(facts["longest_autonomous_s"])),
        ("First Lean edit", "never" if first_edit is None else f"+{human(first_edit)} after the start"),
        ("Tool calls", f"{facts['tool_calls']} ({facts['failed_calls']} failed); protocol {facts['protocol_share']:.0%}, "
                       f"mathematics {facts['mathematics_share']:.0%}"),
        ("Context compactions", str(facts["compactions"])),
        ("Billed tokens", f"{facts['usage']['billed_total']:,} ({facts['usage']['output']:,} output)"),
        ("PRs", f"{facts['prs_created']} created and {facts['prs_merged']} merged by `gh`; mentioned: "
                + (", ".join(f"#{n}" for n in facts["prs"]) or "-")),
    ]
    lines = [f"# {root.title or '(untitled)'}", "",
             f"{root.runtime} run `{root.id}` · archive key `{run.key}` · parser v{PARSER_VERSION}", "",
             "| | |", "|---|---|", *(f"| {name} | {value} |" for name, value in rows), ""]

    lines += ["## Where the tool calls went", "", "| category | calls | recorded time |", "|---|---:|---:|"]
    for name, bucket in sorted(facts["profile"].items(), key=lambda item: -item[1]["calls"]):
        lines.append(f"| {name} | {int(bucket['calls'])} | {human(bucket['seconds'])} |")
    lines += ["", "Protocol = controller + openspec + loop-state; mathematics = lean-edit + lean-build + lean-read. "
              "Recorded time is what the runtime timed; idle time between turns is not in it.", ""]

    lines += ["## Stops", ""]
    if not facts["stops"]:
        lines += ["None recorded.", ""]
    for number, stop in enumerate(facts["stops"], 1):
        how = {"owner": f"waited {human(stop['wait_s'])} for the owner",
               "auto": f"revived by {stop.get('revived_by') or 'runtime'} after {human(stop['wait_s'])}",
               "end": "end of transcript"}[stop["answered_by"]]
        tags = f" · tags: {', '.join(stop['tags'])}" if stop["tags"] else ""
        lines += [f"### {number}. {clock(stop['t'])} — {how} (worked {human(stop['worked_s'])}){tags}", "",
                  quote(stop["text"] or "(no final message)"), ""]
        lines += [f"- **Asked:** {one_line(ask, 800)}" for ask in stop["asks"]]
        if stop["asks"]:
            lines.append("")
        if stop["reply"]:
            lines += ["**Owner replied:**", "", quote(stop["reply"]), ""]
    if facts["open_asks"]:
        lines += ["**Questions still open at the end:**", "", *(f"- {one_line(a, 800)}" for a in facts["open_asks"]), ""]
    if facts["interjections"]:
        lines += ["## Owner messages sent mid-turn", ""]
        lines += [f"- `{clock(i['t'])}` {one_line(i['text'], 600)}" for i in facts["interjections"]]
        lines.append("")

    lines += ["## Timeline", "", *_timeline(root.events), ""]

    if facts["subagent_summaries"]:
        lines += ["## Subagents", "", "| started | role | ran | calls | outcome |", "|---|---|---:|---:|---|"]
        for sub in facts["subagent_summaries"]:
            role = cell(sub["role"] + (f" — {sub['title']}" if sub["title"] else ""), 70)
            lines.append(f"| {clock(sub['start'])} | {role} | {human(sub['span_s'])} | {sub['tool_calls']} | {cell(sub['outcome'], 240)} |")
        lines.append("")
    lines += [f"Every command of the run and its subagents: `{run.key}.commands.tsv`.", ""]
    return "\n".join(lines)


def _is_notable(event: Event) -> bool:
    """Commands worth naming in a digest block, not just counting."""

    if event.exit not in (None, 0) or event.cat in PROTOCOL + ("lean-build", "ci-wait", "lean-edit"):
        return True
    return bool(_NOTABLE_GH.search(event.text) or _NOTABLE_GIT.search(event.text))


def _timeline(events: list[Event]) -> list[str]:
    lines: list[str] = []
    block: list[Event] = []

    def flush() -> None:
        if not block:
            return
        counts: dict[str, int] = {}
        for event in block:
            counts[event.cat or "other"] = counts.get(event.cat or "other", 0) + 1
        summary = ", ".join(f"{name} {n}" for name, n in sorted(counts.items(), key=lambda item: -item[1]))
        span = clock(block[0].t) if block[0].t[:16] == block[-1].t[:16] else f"{clock(block[0].t)}–{block[-1].t[11:16]}"
        lines.append(f"- `{span}` {len(block)} calls, {human(sum(e.dur or 0.0 for e in block))} — {summary}")
        notable: list[str] = []
        for event in block:
            entry = ("✗ " if event.exit not in (None, 0) else "") + one_line(event.text, 170).replace("`", "'")
            if _is_notable(event) and entry not in notable:
                notable.append(entry)
        lines.extend(f"  - `{entry}`" for entry in notable[:8])
        if len(notable) > 8:
            lines.append(f"  - …and {len(notable) - 8} more")
        block.clear()

    for event in events:
        if event.kind == "tool":
            block.append(event)
            continue
        flush()
        at = f"`{clock(event.t)}`"
        if event.kind == "owner":
            lines += ["", f"### Owner, {clock(event.t)}", "", quote(event.text), ""]
        elif event.kind == "commentary":
            lines.append(f"- {at} {one_line(event.text, 420)}")
        elif event.kind == "final":
            lines.append(f"- {at} **Answer:** {one_line(event.text, 420)}")
        elif event.kind == "ask":
            lines.append(f"- {at} **ASKED:** {one_line(event.text, 700)}")
        elif event.kind == "stop":
            lines.append(f"- {at} **STOP:** {one_line(event.text, 300)}")
        elif event.kind == "abort":
            lines.append(f"- {at} **INTERRUPTED:** {event.text}")
        elif event.kind == "spawn":
            lines.append(f"- {at} spawned `{one_line(event.text, 120)}`")
        elif event.kind == "notice":
            lines.append(f"- {at} _{one_line(event.text, 200)}_")
        elif event.kind == "compaction":
            lines.append(f"- {at} _context compacted_")
        elif event.kind == "task":
            lines.append(f"- {at} task: {one_line(event.text, 300)}")
    flush()
    return lines


def render_commands(run: Run) -> str:
    rows = []
    for thread in run.threads:
        for event in thread.events:
            if event.kind == "tool":
                rows.append("\t".join([
                    event.t, thread.id[-12:], one_line(thread.role, 40), event.cat,
                    "" if event.dur is None else f"{event.dur:.1f}", "" if event.exit is None else str(event.exit),
                    one_line(event.text, 400).replace("\t", " "),
                ]))
    return "\n".join(["t\tthread\trole\tcategory\tseconds\texit\tcommand", *sorted(rows)]) + "\n"


def runtime_label(summary: dict[str, Any]) -> str:
    return summary["runtime"] + ("/exec" if summary.get("origin") == "exec" else "")


def render_index(summaries: list[dict[str, Any]]) -> str:
    lines = [
        "# Loop run transcripts", "",
        f"{len(summaries)} runs, newest first; times UTC. `stops` = waited for the owner / auto-continued. "
        "`idle` = waiting on the owner / waiting to be auto-revived (a heartbeat, a notification). "
        "`auto` = longest stretch without owner input. "
        "`protocol` = share of tool calls on the controller, OpenSpec and loop state. "
        "`exec` runs are headless: their prompt came from another agent, not the owner.", "",
        "| start | runtime | run | span | subagents | owner msgs | stops | asks | idle | auto | first Lean edit | protocol | PRs merged | digest |",
        "|---|---|---|---:|---:|---:|---|---:|---|---:|---:|---:|---:|---|",
    ]
    for s in sorted(summaries, key=lambda item: item["start"], reverse=True):
        first = "never" if s["first_lean_edit_after_s"] is None else "+" + human(s["first_lean_edit_after_s"])
        lines.append(
            f"| {clock(s['start'])} | {runtime_label(s)} | {cell(s['title'] or '(untitled)', 60)} | {human(s['span_s'])} | "
            f"{s['subagents']} | {s['owner_messages']} | {s['stops_for_owner']}/{s['stops_auto']} | {s['asks']} | "
            f"{human(s['waiting_on_owner_s'])} / {human(s.get('idle_until_revived_s'))} | "
            f"{human(s['longest_autonomous_s'])} | {first} | {s['protocol_share']:.0%} | {s.get('prs_merged', 0)} | "
            f"[digest](runs/{s['key']}.md) |"
        )
    return "\n".join(lines) + "\n"


ARCHIVE_README = """# Loop run transcript archive

Written by `scripts/loop_transcripts.py sync` in derived-alg-geo-lean. It holds
agent transcripts, so it never belongs in that repository, which is public.

- `index.md`, `index.jsonl` -- one row per run.
- `runs/<key>.md` -- the digest: owner messages, every stop with the agent's
  last words and the owner's reply, the questions asked, a timeline, and one
  line per subagent.
- `runs/<key>.json` -- the same facts, machine-readable.
- `runs/<key>.commands.tsv` -- every tool call of the run and its subagents.
- `raw/<runtime>/<thread>.jsonl.gz` -- lossless copies of the original
  transcripts, including any secret they contain. Not redacted.
- `cache/` -- parsed threads. Safe to delete; the next sync rebuilds them.
- `analysis/` -- written dissections of these runs. Sync never touches it.

Read it back with `python3 scripts/loop_transcripts.py list | stops | profile | show <key>`.
"""


# --------------------------------------------------------------------------
# Archive
# --------------------------------------------------------------------------


@dataclass
class Source:
    runtime: str
    path: Path
    thread_id: str
    home: Path
    parent: str | None = None

    @property
    def project(self) -> str:
        """The Claude Code project directory, which is named after the working directory."""

        if self.runtime != "claude":
            return ""
        return self.path.parent.name if self.parent is None else self.path.parent.parent.parent.name

    def meta(self) -> dict[str, Any] | None:
        if self.runtime != "claude" or self.parent is None:
            return None
        try:
            data = json.loads(self.path.with_name(self.path.name.split(".")[0] + ".meta.json").read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return None
        return data if isinstance(data, dict) else None


def resolve_archive(explicit: Path | None) -> Path:
    if explicit is not None:
        return explicit.expanduser().resolve()
    env = os.environ.get("LOOP_TRANSCRIPTS_DIR")
    return Path(env).expanduser().resolve() if env else DEFAULT_ARCHIVE


def default_needles(cwd: Path) -> list[str]:
    """The repository's name, as it appears in paths, remotes and worktree names."""

    try:
        url = subprocess.run(["git", "-C", str(cwd), "config", "--get", "remote.origin.url"],
                             capture_output=True, text=True, timeout=10).stdout.strip()
    except (OSError, subprocess.SubprocessError):
        url = ""
    name = re.sub(r"\.git$", "", re.split(r"[/:]", url.rstrip("/"))[-1]) if url else ""
    return [name or SCRIPT_DIR.parent.name]


def discover(codex: list[Path], claude: Path | None) -> list[Source]:
    sources: list[Source] = []
    for home in codex:
        for folder in ("sessions", "archived_sessions"):
            if (home / folder).is_dir():
                sources.extend(Source("codex", path, codex_thread_id(path), home)
                               for path in sorted((home / folder).rglob("rollout-*.jsonl")))
    if claude is not None:
        sources.extend(Source("claude", path, claude_thread_id(path, parent), claude, parent)
                       for path, parent in claude_sources(claude))
    return sources


class Archive:
    def __init__(self, root: Path):
        self.root = root
        self.state_path = root / "state.json"

    def ensure(self) -> None:
        for folder in (self.root, self.root / "runs", self.root / "raw", self.root / "cache"):
            folder.mkdir(parents=True, exist_ok=True)
            os.chmod(folder, 0o700)

    def load_state(self) -> dict[str, Any]:
        try:
            data = json.loads(self.state_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            data = {}
        if not isinstance(data, dict) or data.get("schema") != ARCHIVE_SCHEMA:
            data = {"schema": ARCHIVE_SCHEMA, "threads": {}}
        data.setdefault("threads", {})
        return data

    def write(self, path: Path, text: str) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        os.chmod(path.parent, 0o700)
        temporary = path.with_name(path.name + ".tmp")
        temporary.write_text(text, encoding="utf-8")
        os.chmod(temporary, 0o600)
        os.replace(temporary, path)

    def _name(self, thread_id: str) -> str:
        return thread_id.replace(":", "__")

    def raw_path(self, runtime: str, thread_id: str) -> Path:
        return self.root / "raw" / runtime / f"{self._name(thread_id)}.jsonl.gz"

    def cache_path(self, runtime: str, thread_id: str) -> Path:
        return self.root / "cache" / runtime / f"{self._name(thread_id)}.json"

    def copy_raw(self, source: Source) -> None:
        target = self.raw_path(source.runtime, source.thread_id)
        target.parent.mkdir(parents=True, exist_ok=True)
        os.chmod(target.parent, 0o700)
        temporary = target.with_name(target.name + ".tmp")
        with source.path.open("rb") as reader, gzip.open(temporary, "wb", compresslevel=6) as writer:
            shutil.copyfileobj(reader, writer, length=1 << 20)
        os.chmod(temporary, 0o600)
        os.replace(temporary, target)
        meta = source.meta()
        if meta is not None:
            self.write(target.with_name(f"{self._name(source.thread_id)}.meta.json"), json.dumps(meta))

    def load_thread(self, runtime: str, thread_id: str) -> Thread | None:
        try:
            return Thread.from_json(json.loads(self.cache_path(runtime, thread_id).read_text(encoding="utf-8")))
        except (OSError, json.JSONDecodeError, TypeError):
            return None

    def save_thread(self, thread: Thread) -> None:
        self.write(self.cache_path(thread.runtime, thread.id), json.dumps(thread.to_json(), ensure_ascii=False))

    def summaries(self) -> list[dict[str, Any]]:
        found = []
        for path in sorted((self.root / "runs").glob("*.json")):
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                continue
            if isinstance(data, dict) and data.get("schema") == RUN_SCHEMA:
                found.append(data)
        return found


class Reader:
    """Parses sources, and archived raw copies whose source is gone."""

    def __init__(self, archive: Archive, matcher: RepoMatcher):
        self.archive = archive
        self.matcher = matcher
        self.titles: dict[Path, dict[str, str]] = {}

    def source(self, source: Source) -> Thread:
        if source.runtime == "codex":
            if source.home not in self.titles:
                self.titles[source.home] = codex_titles(source.home)
            return read_codex_thread(source.path, source.thread_id, self.titles[source.home], self.matcher)
        return read_claude_thread(source.path, source.thread_id, source.parent, self.matcher,
                                  project=source.project, meta=source.meta())

    def archived(self, thread_id: str, entry: dict[str, Any]) -> Thread | None:
        raw = self.archive.raw_path(entry["runtime"], thread_id)
        if not raw.is_file():
            return None
        if entry["runtime"] == "codex":
            thread = read_codex_thread(raw, thread_id, {thread_id: entry.get("title", "")}, self.matcher)
        else:
            try:
                meta = json.loads(raw.with_name(raw.name.replace(".jsonl.gz", ".meta.json")).read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError):
                meta = None
            thread = read_claude_thread(raw, thread_id, entry.get("parent"), self.matcher,
                                        project=entry.get("project", ""), meta=meta)
        thread.source = entry.get("source", thread.source)
        return thread


def _fingerprint(path: Path) -> list[int] | None:
    try:
        stat = path.stat()
    except OSError:
        return None
    return [stat.st_size, stat.st_mtime_ns]


def _analysis_current(path: Path) -> bool:
    try:
        return json.loads(path.read_text(encoding="utf-8")).get("analysis") == ANALYSIS_VERSION
    except (OSError, json.JSONDecodeError):
        return False


def sync(archive: Archive, sources: list[Source], matcher: RepoMatcher, *, include_all: bool = False,
         keep_raw: bool = True, log: Callable[..., Any] = print) -> dict[str, int]:
    """Bring the archive up to date with every transcript source.

    A source is re-read only when its size or modification time changed, or
    the parser version did. A thread whose source has since been deleted keeps
    its archived copy and stays in its run: outliving the originals is what
    the archive is for.
    """

    archive.ensure()
    state = archive.load_state()
    registry: dict[str, dict[str, Any]] = state["threads"]
    reader = Reader(archive, matcher)
    by_id: dict[str, Source] = {}
    for source in sources:  # a thread moved to archived_sessions/ keeps its id
        current = by_id.get(source.thread_id)
        mine, theirs = _fingerprint(source.path), _fingerprint(current.path) if current else None
        if mine is not None and (theirs is None or mine[1] > theirs[1]):
            by_id[source.thread_id] = source
    parsed: dict[str, Thread] = {}
    counts = {"sources": len(by_id), "read": 0, "runs": 0, "rendered": 0, "skipped": 0}

    def record(thread: Thread, source_path: str, fingerprint: list[int] | None, previous: dict[str, Any] | None) -> None:
        parsed[thread.id] = thread
        counts["read"] += 1
        registry[thread.id] = {
            "runtime": thread.runtime, "source": source_path, "fingerprint": fingerprint, "parser": PARSER_VERSION,
            "parent": thread.parent, "repo_hits": thread.repo_hits, "start": thread.start, "title": thread.title,
            "project": by_id[thread.id].project if thread.id in by_id else (previous or {}).get("project", ""),
            "archived": bool(previous and previous.get("archived")),
        }

    for thread_id, source in by_id.items():
        fingerprint = _fingerprint(source.path)
        entry = registry.get(thread_id)
        if entry and entry.get("fingerprint") == fingerprint and entry.get("parser") == PARSER_VERSION:
            continue
        record(reader.source(source), str(source.path), fingerprint, entry)
    for thread_id, entry in list(registry.items()):
        if thread_id not in by_id and entry.get("parser") != PARSER_VERSION and entry.get("archived"):
            thread = reader.archived(thread_id, entry)
            if thread is not None:
                record(thread, entry.get("source", ""), entry.get("fingerprint"), entry)

    parents = {tid: entry.get("parent") for tid, entry in registry.items()}
    members: dict[str, list[str]] = {}
    for tid in registry:
        members.setdefault(root_of(tid, parents), []).append(tid)

    for root_id, tids in sorted(members.items()):
        root_entry = registry[root_id]
        if not include_all and not any(registry[t].get("repo_hits", 0) > 0 for t in tids):
            counts["skipped"] += 1
            continue
        counts["runs"] += 1
        key = run_key(root_entry["runtime"], root_id, root_entry.get("start", ""))
        if not any(t in parsed for t in tids) and _analysis_current(archive.root / "runs" / f"{key}.json"):
            continue
        threads: list[Thread] = []
        for tid in tids:
            entry = registry[tid]
            thread = parsed.get(tid) or (archive.load_thread(entry["runtime"], tid) if entry.get("archived") else None)
            if thread is None and tid in by_id:
                thread = parsed[tid] = reader.source(by_id[tid])
            if thread is None:
                continue
            if tid in parsed or not entry.get("archived"):
                if keep_raw and tid in by_id:
                    archive.copy_raw(by_id[tid])
                archive.save_thread(thread)
                entry["archived"] = True
            threads.append(thread)
        root = next((t for t in threads if t.id == root_id), None)
        if root is None or (not root.events and len(threads) == 1):
            continue  # an empty session: a title record and nothing else
        run = Run(root=root, children=sorted((t for t in threads if t.id != root_id), key=lambda t: t.start))
        facts = analyze(run)
        archive.write(archive.root / "runs" / f"{run.key}.md", render_digest(run, facts))
        archive.write(archive.root / "runs" / f"{run.key}.commands.tsv", render_commands(run))
        archive.write(archive.root / "runs" / f"{run.key}.json", json.dumps(facts, ensure_ascii=False, indent=1))
        counts["rendered"] += 1
        log(f"  {run.key}  {one_line(root.title or '(untitled)', 70)}")

    summaries = archive.summaries()
    brief = ("stops", "profile", "subagent_summaries", "interjections", "open_asks")
    archive.write(archive.root / "index.jsonl",
                  "".join(json.dumps({k: v for k, v in s.items() if k not in brief}, ensure_ascii=False) + "\n"
                          for s in sorted(summaries, key=lambda s: s["start"])))
    archive.write(archive.root / "index.md", render_index(summaries))
    archive.write(archive.root / "README.md", ARCHIVE_README)
    archive.write(archive.state_path, json.dumps(state, indent=1, sort_keys=True))
    return counts


# --------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------


def _since(value: str | None) -> datetime | None:
    if not value:
        return None
    parsed = parse_timestamp(value if "T" in value else value + "T00:00:00Z")
    if parsed is None:
        raise TranscriptError(f"could not parse --since {value!r}")
    return parsed


def select_runs(archive: Archive, *, since: str | None = None, run: str | None = None,
                runtime: str | None = None) -> list[dict[str, Any]]:
    summaries = archive.summaries()
    if not summaries:
        raise TranscriptError(f"no runs archived in {archive.root}; run `loop_transcripts.py sync` first")
    lower = _since(since)
    chosen = []
    for summary in summaries:
        if runtime and summary["runtime"] != runtime:
            continue
        if lower is not None and (parse_timestamp(summary["end"]) or lower) < lower:
            continue
        if run and run not in summary["key"] and run not in summary["root_id"] \
                and run.lower() not in (summary["title"] or "").lower():
            continue
        chosen.append(summary)
    return sorted(chosen, key=lambda s: s["start"])


def command_sync(args: argparse.Namespace) -> int:
    archive = Archive(resolve_archive(args.archive))
    needles = args.match or default_needles(Path.cwd())
    codex = codex_homes(args.codex_home)
    claude = None if args.no_claude else claude_home(args.claude_home)
    log: Callable[..., Any] = (lambda *_: None) if args.quiet else print
    log(f"archive: {archive.root}")
    log(f"codex homes: {', '.join(map(str, codex)) or '(none)'}; claude home: {claude or '(skipped)'}")
    log("keeping every run (--all)" if args.all else f"keeping runs that touch: {', '.join(needles)}")
    counts = sync(archive, discover(codex, claude), RepoMatcher(needles), include_all=args.all,
                  keep_raw=not args.no_raw, log=log)
    log(f"{counts['sources']} transcripts, {counts['read']} read; {counts['runs']} runs kept "
        f"({counts['rendered']} rewritten), {counts['skipped']} unrelated runs skipped")
    return 0


def command_list(args: argparse.Namespace) -> int:
    archive = Archive(resolve_archive(args.archive))
    runs = select_runs(archive, since=args.since, runtime=args.runtime)
    columns = ("key", "runtime", "origin", "title", "start", "end", "span_s", "owner_messages", "stops_for_owner",
               "stops_auto", "asks", "waiting_on_owner_s", "idle_until_revived_s", "longest_autonomous_s",
               "protocol_share", "first_lean_edit_after_s", "prs_created", "prs_merged")
    if args.json:
        print(json.dumps([{k: s.get(k) for k in columns} for s in runs], indent=1, ensure_ascii=False))
        return 0
    print(f"{'start':11} {'key':30} {'runtime':11} {'span':>6} {'own':>4} {'stops':>6} {'asks':>4} {'idle':>13} "
          f"{'auto':>6} {'proto':>5} {'merged':>6}  title")
    for s in runs:
        idle = f"{human(s['waiting_on_owner_s'])}/{human(s.get('idle_until_revived_s'))}"
        print(f"{clock(s['start']):11} {s['key']:30} {runtime_label(s):11} {human(s['span_s']):>6} {s['owner_messages']:>4} "
              f"{str(s['stops_for_owner']) + '/' + str(s['stops_auto']):>6} {s['asks']:>4} {idle:>13} "
              f"{human(s['longest_autonomous_s']):>6} {s['protocol_share']:>5.0%} {s.get('prs_merged', 0):>6}  "
              f"{one_line(s['title'] or '', 60)}")
    print(f"\n{len(runs)} runs in {archive.root}. own = owner messages; stops = for owner/auto-continued; "
          "idle = waiting on owner/waiting to be auto-revived; auto = longest stretch without owner input; "
          "proto = protocol share of tool calls; merged = PRs merged with `gh pr merge`")
    return 0


def command_stops(args: argparse.Namespace) -> int:
    archive = Archive(resolve_archive(args.archive))
    runs = select_runs(archive, since=args.since, run=args.run, runtime=args.runtime)
    wanted = {"owner", "end"} if args.owner_only else {"owner", "auto", "end"}
    since = _since(args.since)

    def chosen(summary: dict[str, Any]) -> list[dict[str, Any]]:
        return [x for x in summary["stops"] if x["answered_by"] in wanted
                and (since is None or (parse_timestamp(x["t"]) or since) >= since)]

    if args.json:
        print(json.dumps([{"key": s["key"], "title": s["title"], "stops": chosen(s)} for s in runs],
                         indent=1, ensure_ascii=False))
        return 0
    tags: dict[str, int] = {}
    total = 0
    for s in runs:
        stops = chosen(s)
        if not stops:
            continue
        print("=" * 100)
        print(f"{s['key']}  {s['title']}")
        print(f"owner messages {s['owner_messages']} · stops for owner {s['stops_for_owner']} · auto {s['stops_auto']} · "
              f"asks {s['asks']} · idle {human(s['waiting_on_owner_s'])}")
        for stop in stops:
            total += 1
            for tag in stop["tags"] or ["untagged"]:
                tags[tag] = tags.get(tag, 0) + 1
            how = {"owner": f"OWNER after {human(stop['wait_s'])}",
                   "auto": f"auto: {stop.get('revived_by') or 'runtime'} after {human(stop['wait_s'])}",
                   "end": "END"}[stop["answered_by"]]
            print(f"\n--- {clock(stop['t'])}  [{how}]  worked {human(stop['worked_s'])}  tags: {', '.join(stop['tags']) or '-'}")
            print("    " + one_line(stop["text"] or "(no final message)", args.chars))
            for ask in stop["asks"]:
                print("    ASKED: " + one_line(ask, args.chars))
            if stop["reply"]:
                print("    OWNER: " + one_line(stop["reply"], args.chars))
    print("\n" + "=" * 100)
    print(f"{total} stops across {len(runs)} runs; keyword tags: "
          + (", ".join(f"{k} {v}" for k, v in sorted(tags.items(), key=lambda kv: -kv[1])) or "-"))
    return 0


def command_profile(args: argparse.Namespace) -> int:
    archive = Archive(resolve_archive(args.archive))
    runs = select_runs(archive, since=args.since, run=args.run, runtime=args.runtime)
    combined: dict[str, dict[str, float]] = {}
    for s in runs:
        for name, bucket in s["profile"].items():
            target = combined.setdefault(name, {"calls": 0, "seconds": 0.0})
            target["calls"] += bucket["calls"]
            target["seconds"] += bucket["seconds"]
    if args.json:
        print(json.dumps({"runs": [s["key"] for s in runs], "profile": combined}, indent=1))
        return 0
    calls = sum(b["calls"] for b in combined.values()) or 1
    seconds = sum(b["seconds"] for b in combined.values()) or 1.0
    print(f"{len(runs)} runs; {int(calls)} tool calls\n")
    print(f"{'category':14} {'calls':>7} {'share':>6} {'recorded time':>14} {'share':>6}")
    for name, bucket in sorted(combined.items(), key=lambda item: -item[1]["calls"]):
        print(f"{name:14} {int(bucket['calls']):>7} {bucket['calls'] / calls:>6.0%} {human(bucket['seconds']):>14} "
              f"{bucket['seconds'] / seconds:>6.0%}")
    print("\nper run:")
    for s in runs:
        first = "never" if s["first_lean_edit_after_s"] is None else "+" + human(s["first_lean_edit_after_s"])
        print(f"  {s['key']:30} protocol {s['protocol_share']:>4.0%}  mathematics {s['mathematics_share']:>4.0%}  "
              f"first Lean edit {first:>8}  {one_line(s['title'] or '', 50)}")
    return 0


def command_show(args: argparse.Namespace) -> int:
    archive = Archive(resolve_archive(args.archive))
    runs = select_runs(archive, run=args.run)
    if len(runs) != 1:
        raise TranscriptError(f"{len(runs)} runs match {args.run!r}: " + ", ".join(s["key"] for s in runs[:10]))
    path = archive.root / "runs" / (runs[0]["key"] + (".commands.tsv" if args.commands else ".md"))
    if args.path:
        print(path)
    else:
        sys.stdout.write(path.read_text(encoding="utf-8"))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--archive", type=Path, help=f"archive directory (default: $LOOP_TRANSCRIPTS_DIR or {DEFAULT_ARCHIVE})")
    sub = parser.add_subparsers(dest="command", required=True)

    s = sub.add_parser("sync", help="copy new or grown transcripts into the archive and rewrite their digests")
    s.add_argument("--codex-home", type=Path, action="append",
                   help="a Codex home to read (repeatable; default: $CODEX_HOME, ~/.codex and ~/.codex-accounts/*)")
    s.add_argument("--claude-home", type=Path, help="Claude Code home (default: $CLAUDE_CONFIG_DIR or ~/.claude)")
    s.add_argument("--no-claude", action="store_true", help="do not read Claude Code transcripts")
    s.add_argument("--match", action="append",
                   help="keep runs whose paths or commands contain this text (repeatable; default: the origin repository's name)")
    s.add_argument("--all", action="store_true", help="keep every run, whether or not it touches this repository")
    s.add_argument("--no-raw", action="store_true", help="write digests only; keep no raw copies")
    s.add_argument("--quiet", action="store_true", help="print nothing on success, for a timer")

    for name, text in (("list", "one line per archived run"), ("stops", "every stop, across runs"),
                       ("profile", "where tool calls went, across runs")):
        p = sub.add_parser(name, help=text)
        p.add_argument("--since", help="only runs still active on or after this date or ISO-8601 time"
                       + ("; and only the stops made since then" if name == "stops" else ""))
        p.add_argument("--runtime", choices=RUNTIMES)
        p.add_argument("--json", action="store_true")
        if name != "list":
            p.add_argument("--run", help="a run key, root id, or title substring")
        if name == "stops":
            p.add_argument("--owner-only", action="store_true", help="only stops the owner had to answer, and run ends")
            p.add_argument("--chars", type=int, default=600, help="characters of each message to print (default: 600)")

    show = sub.add_parser("show", help="print one run's digest")
    show.add_argument("run", help="a run key, root id, or title substring naming exactly one run")
    show.add_argument("--commands", action="store_true", help="print the command table instead")
    show.add_argument("--path", action="store_true", help="print the file's path, not its content")
    return parser


def main(argv: list[str] | None = None) -> int:
    force_utf8_output()
    args = build_parser().parse_args(argv)
    handlers = {"sync": command_sync, "list": command_list, "stops": command_stops,
                "profile": command_profile, "show": command_show}
    try:
        return handlers[args.command](args)
    except TranscriptError as exc:
        print(f"FAIL {exc}")
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
