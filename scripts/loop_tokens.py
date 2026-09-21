#!/usr/bin/env python3
"""Provider-neutral token accounting for bounded loop runs.

WHY THIS EXISTS. A bounded run under `.claude/loop-specs/` spends most of its
budget on things nobody watches while they happen: four independent reviewers
per frozen chunk, up to five review/improve rounds, and a re-read of the same
diff in each one. The review ledger records *verdicts*; nothing recorded what
those verdicts cost. This reads the cost back out of the transcripts both
agent runtimes already write, so a finished run can say what it spent without
either runtime having been instrumented in advance.

TWO PROVIDERS, ONE UNIT. The runtimes disagree about what "input tokens"
means, and the disagreement is silent -- both report a plausible number under
the same name:

* Claude Code writes `~/.claude/projects/<slug>/<session>.jsonl`. Usage rides
  on `type: "assistant"` lines as `message.usage`, and `input_tokens` counts
  only the *uncached* prefix; cache reads and writes are separate siblings.
* Codex writes `~/.codex/sessions/<Y>/<M>/<D>/rollout-*.jsonl`. Usage rides on
  `type: "token_usage_record"` lines as `payload.usage`, and its `input_tokens`
  is *inclusive* of `cached_input_tokens`.

Adding the two `input_tokens` fields together is therefore meaningless. This
module normalizes both onto disjoint buckets -- uncached input, cached input,
cache write, output -- so a total is a total. `reasoning` is reported
separately but is a *subset* of `output`, never added to it.

DEDUPLICATION IS NOT OPTIONAL. One Claude API response is frequently written
as several transcript lines (text and tool_use split across records), and each
line repeats the *same* usage object. Measured on a real local transcript: 75
assistant lines carrying usage, 36 distinct `requestId`s, every repeat byte
identical. Summing lines overcounts by more than 2x. Records are therefore
keyed -- `requestId` for Claude, `response_id` for Codex -- and each key is
counted once, which also makes resumed and forked sessions safe to scan.

Codex's `payload.usage` is a per-response delta, not a running total: summing
the deltas of a 65-record session reproduced that session's final
`thread_token_usage.total_tokens` exactly. The cumulative `turn_token_usage`
and `thread_token_usage` fields are deliberately ignored.

WHAT A TOTAL MEANS. These are *billed* tokens, not unique context. A cached
conversation re-reads its prefix on every request, so the cached-input column
grows with turn count and is the right number for cost and the wrong number
for "how much material did this run look at".

THIS TOOL WRITES NOTHING INTO THE LEDGER. The review ledger is the integrity
record of who reviewed what; a cost annotation has no business mutating it.
`ledger --out` writes a separate report file instead.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator

try:
    from _output import force_utf8_output
except ImportError:  # pragma: no cover - direct invocation from another cwd
    def force_utf8_output() -> None:
        """Best-effort UTF-8 output fallback for standalone invocation."""


REPORT_SCHEMA = "derived-alg-geo-lean.loop-run/v1/token-report"
LEDGER_SCHEMA = "derived-alg-geo-lean.loop-run/v1/ledger"
PROVIDERS = ("claude", "codex")


class TokenError(RuntimeError):
    """A user-actionable error in token collection or reporting."""


# --------------------------------------------------------------------------
# Normalized records
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Usage:
    """Disjoint token buckets, comparable across providers.

    `reasoning` is a subset of `output` and is excluded from `billed`.
    """

    input_uncached: int = 0
    input_cached: int = 0
    cache_write: int = 0
    output: int = 0
    reasoning: int = 0

    @property
    def billed(self) -> int:
        return self.input_uncached + self.input_cached + self.cache_write + self.output

    def __add__(self, other: "Usage") -> "Usage":
        return Usage(
            self.input_uncached + other.input_uncached,
            self.input_cached + other.input_cached,
            self.cache_write + other.cache_write,
            self.output + other.output,
            self.reasoning + other.reasoning,
        )

    def as_dict(self) -> dict[str, int]:
        return {
            "input_uncached": self.input_uncached,
            "input_cached": self.input_cached,
            "cache_write": self.cache_write,
            "output": self.output,
            "reasoning_subset_of_output": self.reasoning,
            "billed_total": self.billed,
        }


@dataclass(frozen=True)
class Record:
    """One deduplicated model response, with the context needed to attribute it."""

    provider: str
    key: str
    timestamp: datetime
    cwd: str
    session: str
    model: str
    agent: str
    usage: Usage


def parse_timestamp(value: Any) -> datetime | None:
    """Parse an ISO-8601 transcript timestamp into an aware UTC datetime."""

    if not isinstance(value, str) or not value:
        return None
    text = value.strip()
    if text.endswith(("z", "Z")):
        text = text[:-1] + "+00:00"
    try:
        parsed = datetime.fromisoformat(text)
    except ValueError:
        return None
    if parsed.tzinfo is None:
        parsed = parsed.replace(tzinfo=timezone.utc)
    return parsed.astimezone(timezone.utc)


def coerce_int(value: Any) -> int:
    return value if isinstance(value, int) and not isinstance(value, bool) else 0


def iter_jsonl(path: Path) -> Iterator[dict[str, Any]]:
    """Yield JSON objects from a transcript, tolerating a live partial write.

    A session that is still running can leave a truncated final line. Skipping
    unparseable lines is correct here: the alternative is refusing to report on
    the run currently being measured.
    """

    try:
        handle = path.open(encoding="utf-8", errors="replace")
    except OSError:
        return
    with handle:
        for line in handle:
            line = line.strip()
            if not line:
                continue
            try:
                payload = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(payload, dict):
                yield payload


# --------------------------------------------------------------------------
# Provider readers
# --------------------------------------------------------------------------


def claude_home(explicit: Path | None = None) -> Path:
    if explicit is not None:
        return explicit
    env = os.environ.get("CLAUDE_CONFIG_DIR")
    return Path(env) if env else Path.home() / ".claude"


def codex_home(explicit: Path | None = None) -> Path:
    if explicit is not None:
        return explicit
    env = os.environ.get("CODEX_HOME")
    return Path(env) if env else Path.home() / ".codex"


def read_claude(home: Path) -> Iterator[Record]:
    """Read Claude Code transcripts.

    Sidechain lines are subagent turns -- the four reviewers a loop round
    dispatches -- and are counted, because the run paid for them. `agentName`
    identifies which reviewer, when present.
    """

    projects = home / "projects"
    if not projects.is_dir():
        return
    for path in sorted(projects.rglob("*.jsonl")):
        for entry in iter_jsonl(path):
            if entry.get("type") != "assistant":
                continue
            message = entry.get("message")
            if not isinstance(message, dict):
                continue
            usage = message.get("usage")
            if not isinstance(usage, dict):
                continue
            key = entry.get("requestId") or message.get("id")
            if not isinstance(key, str) or not key:
                continue
            timestamp = parse_timestamp(entry.get("timestamp"))
            if timestamp is None:
                continue
            details = usage.get("output_tokens_details")
            reasoning = coerce_int(details.get("thinking_tokens")) if isinstance(details, dict) else 0
            agent = entry.get("agentName")
            if not isinstance(agent, str) or not agent:
                agent = "subagent" if entry.get("isSidechain") else ""
            yield Record(
                provider="claude",
                key=key,
                timestamp=timestamp,
                cwd=str(entry.get("cwd") or ""),
                session=str(entry.get("sessionId") or path.stem),
                model=str(message.get("model") or ""),
                agent=agent,
                usage=Usage(
                    input_uncached=coerce_int(usage.get("input_tokens")),
                    input_cached=coerce_int(usage.get("cache_read_input_tokens")),
                    cache_write=coerce_int(usage.get("cache_creation_input_tokens")),
                    output=coerce_int(usage.get("output_tokens")),
                    reasoning=reasoning,
                ),
            )


def read_codex(home: Path) -> Iterator[Record]:
    """Read Codex rollout transcripts.

    Codex reports a session's working directory once in `session_meta` and can
    change it later in a `turn_context`, so the directory in force is tracked
    as the file is read and attached to each usage record.
    """

    sessions = home / "sessions"
    if not sessions.is_dir():
        return
    for path in sorted(sessions.rglob("rollout-*.jsonl")):
        cwd = ""
        model = ""
        session = path.stem
        for entry in iter_jsonl(path):
            kind = entry.get("type")
            payload = entry.get("payload")
            if not isinstance(payload, dict):
                continue
            if kind in {"session_meta", "turn_context"}:
                if isinstance(payload.get("cwd"), str):
                    cwd = payload["cwd"]
                if isinstance(payload.get("model"), str):
                    model = payload["model"]
                if kind == "session_meta" and isinstance(payload.get("session_id"), str):
                    session = payload["session_id"]
                continue
            if kind != "token_usage_record":
                continue
            usage = payload.get("usage")
            if not isinstance(usage, dict):
                continue
            key = payload.get("response_id")
            if not isinstance(key, str) or not key:
                # Fall back to a positional key so an unidentified response is
                # still counted exactly once within its own thread.
                key = f"{payload.get('thread_id', session)}:{entry.get('ordinal')}"
            timestamp = parse_timestamp(entry.get("timestamp"))
            if timestamp is None:
                continue
            total_input = coerce_int(usage.get("input_tokens"))
            cached_input = coerce_int(usage.get("cached_input_tokens"))
            yield Record(
                provider="codex",
                key=key,
                timestamp=timestamp,
                cwd=cwd,
                session=session,
                model=model,
                agent="",
                usage=Usage(
                    # Codex's input_tokens includes the cached prefix; Claude's
                    # does not. Subtracting here is what makes the two columns
                    # mean the same thing.
                    input_uncached=max(total_input - cached_input, 0),
                    input_cached=cached_input,
                    cache_write=coerce_int(usage.get("cache_write_input_tokens")),
                    output=coerce_int(usage.get("output_tokens")),
                    reasoning=coerce_int(usage.get("reasoning_output_tokens")),
                ),
            )


def collect(
    providers: Iterable[str],
    *,
    claude_dir: Path | None = None,
    codex_dir: Path | None = None,
) -> list[Record]:
    """Read every requested provider and drop duplicate responses."""

    wanted = set(providers)
    unknown = wanted - set(PROVIDERS)
    if unknown:
        raise TokenError(f"unknown provider(s): {', '.join(sorted(unknown))}")
    records: list[Record] = []
    if "claude" in wanted:
        records.extend(read_claude(claude_home(claude_dir)))
    if "codex" in wanted:
        records.extend(read_codex(codex_home(codex_dir)))
    return deduplicate(records)


def deduplicate(records: Iterable[Record]) -> list[Record]:
    seen: set[tuple[str, str]] = set()
    unique: list[Record] = []
    for record in records:
        identity = (record.provider, record.key)
        if identity in seen:
            continue
        seen.add(identity)
        unique.append(record)
    unique.sort(key=lambda item: item.timestamp)
    return unique


# --------------------------------------------------------------------------
# Filtering and aggregation
# --------------------------------------------------------------------------


def within_directory(record_cwd: str, root: Path) -> bool:
    """True when a record's working directory is the root or below it."""

    if not record_cwd:
        return False
    try:
        candidate = Path(record_cwd).resolve()
    except (OSError, ValueError):
        return False
    return candidate == root or root in candidate.parents


def select(
    records: Iterable[Record],
    *,
    since: datetime | None = None,
    until: datetime | None = None,
    root: Path | None = None,
    session: str | None = None,
) -> list[Record]:
    chosen = []
    for record in records:
        if since is not None and record.timestamp < since:
            continue
        if until is not None and record.timestamp > until:
            continue
        if root is not None and not within_directory(record.cwd, root):
            continue
        if session is not None and record.session != session:
            continue
        chosen.append(record)
    return chosen


def total(records: Iterable[Record]) -> Usage:
    result = Usage()
    for record in records:
        result = result + record.usage
    return result


GROUPERS = {
    "provider": lambda record: record.provider,
    "session": lambda record: f"{record.provider}:{record.session}",
    "model": lambda record: record.model or "(unreported)",
    "agent": lambda record: record.agent or "(main thread)",
    "day": lambda record: record.timestamp.date().isoformat(),
}


def group(records: Iterable[Record], key: str) -> dict[str, list[Record]]:
    if key not in GROUPERS:
        raise TokenError(f"unknown grouping {key!r}; choose from {', '.join(sorted(GROUPERS))}")
    grouper = GROUPERS[key]
    buckets: dict[str, list[Record]] = {}
    for record in records:
        buckets.setdefault(grouper(record), []).append(record)
    return buckets


# --------------------------------------------------------------------------
# Ledger windows
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Window:
    """The period a frozen chunk's ledger was open, and what it is called."""

    chunk_id: str
    issue: int | None
    status: str
    start: datetime
    end: datetime
    open_ended: bool
    source: Path


def load_ledger(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise TokenError(f"could not read ledger {path}: {exc}") from exc
    if not isinstance(data, dict) or data.get("schema") != LEDGER_SCHEMA:
        raise TokenError(f"not a loop review ledger: {path}")
    return data


def ledger_window(path: Path, data: dict[str, Any], fallback_end: datetime) -> Window:
    """Derive a chunk's time window from the ledger's own timestamps.

    The ledger records `created_at` when the chunk is frozen and `recorded_at`
    on every review and adjudication. The window runs from the freeze to the
    last recorded event; a chunk still under review has no last event yet, so
    it stays open-ended and is reported as such rather than silently closed.
    """

    start = parse_timestamp(data.get("created_at"))
    if start is None:
        raise TokenError(f"ledger has no usable created_at: {path}")
    stamps: list[datetime] = []
    rounds = data.get("rounds")
    if isinstance(rounds, list):
        for entry in rounds:
            if not isinstance(entry, dict):
                continue
            reviews = entry.get("reviews")
            if isinstance(reviews, list):
                for review in reviews:
                    if isinstance(review, dict):
                        stamp = parse_timestamp(review.get("recorded_at"))
                        if stamp is not None:
                            stamps.append(stamp)
            adjudication = entry.get("adjudication")
            if isinstance(adjudication, dict):
                stamp = parse_timestamp(adjudication.get("recorded_at"))
                if stamp is not None:
                    stamps.append(stamp)
    chunk = data.get("chunk") if isinstance(data.get("chunk"), dict) else {}
    issue = data.get("issue") if isinstance(data.get("issue"), dict) else {}
    end = max(stamps) if stamps else fallback_end
    if end < start:
        end = fallback_end
    return Window(
        chunk_id=str(chunk.get("id") or path.stem),
        issue=issue.get("number") if isinstance(issue.get("number"), int) else None,
        status=str(data.get("status") or "unknown"),
        start=start,
        end=end,
        open_ended=not stamps,
        source=path,
    )


def discover_ledgers(state_dir: Path) -> list[Path]:
    if not state_dir.is_dir():
        raise TokenError(
            f"no ledger directory at {state_dir}. A run records its ledgers there; "
            "pass --state-dir if this run used another location"
        )
    found = sorted(p for p in state_dir.glob("*.json") if not p.name.endswith(".tokens.json"))
    if not found:
        raise TokenError(f"no ledger files in {state_dir}")
    return found


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------


def thousands(value: int) -> str:
    return f"{value:,}"


def usage_row(label: str, count: int, usage: Usage, width: int) -> str:
    return (
        f"{label:<{width}}  {count:>6}  {thousands(usage.input_uncached):>13}"
        f"  {thousands(usage.input_cached):>13}  {thousands(usage.cache_write):>12}"
        f"  {thousands(usage.output):>10}  {thousands(usage.billed):>14}"
    )


def usage_header(width: int) -> str:
    head = (
        f"{'':<{width}}  {'calls':>6}  {'input(new)':>13}  {'input(cached)':>13}"
        f"  {'cache-write':>12}  {'output':>10}  {'billed total':>14}"
    )
    return head + "\n" + "-" * len(head)


def print_breakdown(buckets: dict[str, list[Record]], label: str) -> None:
    if not buckets:
        return
    width = max(len(label), max(len(name) for name in buckets))
    width = max(width, 12)
    print(usage_header(width))
    for name in sorted(buckets, key=lambda n: total(buckets[n]).billed, reverse=True):
        rows = buckets[name]
        print(usage_row(name, len(rows), total(rows), width))
    every = [record for rows in buckets.values() for record in rows]
    print("-" * len(usage_header(width).splitlines()[0]))
    print(usage_row("TOTAL", len(every), total(every), width))


def report_payload(records: list[Record], grouping: str, scope: dict[str, Any]) -> dict[str, Any]:
    buckets = group(records, grouping)
    return {
        "schema": REPORT_SCHEMA,
        "generated_at": datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z"),
        "scope": scope,
        "note": (
            "Billed tokens, deduplicated per model response. Cached input is re-read "
            "on every request, so it measures cost, not unique context. Reasoning is "
            "a subset of output and is not added to the total."
        ),
        "calls": len(records),
        "total": total(records).as_dict(),
        "grouped_by": grouping,
        "groups": {
            name: {"calls": len(rows), **total(rows).as_dict()}
            for name, rows in sorted(buckets.items())
        },
    }


def command_report(args: argparse.Namespace) -> int:
    providers = PROVIDERS if args.provider == "all" else (args.provider,)
    records = collect(providers, claude_dir=args.claude_home, codex_dir=args.codex_home)
    root = None if args.all_directories else args.cwd.resolve()
    since = parse_timestamp(args.since) if args.since else None
    until = parse_timestamp(args.until) if args.until else None
    if args.since and since is None:
        raise TokenError(f"could not parse --since {args.since!r} as an ISO-8601 timestamp")
    if args.until and until is None:
        raise TokenError(f"could not parse --until {args.until!r} as an ISO-8601 timestamp")
    chosen = select(records, since=since, until=until, root=root, session=args.session)
    scope = {
        "providers": list(providers),
        "directory": None if root is None else str(root),
        "since": since.isoformat().replace("+00:00", "Z") if since else None,
        "until": until.isoformat().replace("+00:00", "Z") if until else None,
        "session": args.session,
    }
    if args.json:
        print(json.dumps(report_payload(chosen, args.by, scope), indent=2, sort_keys=True))
        return 0
    if not chosen:
        print("No token records matched. Scope:")
        for key, value in scope.items():
            print(f"  {key}: {value}")
        print(
            "\nIf this repository was worked on from another machine, its transcripts "
            "live in that machine's ~/.claude and ~/.codex and were never committed."
        )
        return 0
    span_start = chosen[0].timestamp.isoformat().replace("+00:00", "Z")
    span_end = chosen[-1].timestamp.isoformat().replace("+00:00", "Z")
    print(f"Scope: {'all directories' if root is None else root}")
    print(f"Span:  {span_start} .. {span_end}")
    print()
    print_breakdown(group(chosen, args.by), args.by)
    return 0


def command_ledger(args: argparse.Namespace) -> int:
    paths = [p.resolve() for p in args.state] if args.state else discover_ledgers(args.state_dir.resolve())
    fallback_end = parse_timestamp(args.until) if args.until else datetime.now(timezone.utc)
    if args.until and fallback_end is None:
        raise TokenError(f"could not parse --until {args.until!r} as an ISO-8601 timestamp")
    windows = [ledger_window(path, load_ledger(path), fallback_end) for path in paths]
    providers = PROVIDERS if args.provider == "all" else (args.provider,)
    records = collect(providers, claude_dir=args.claude_home, codex_dir=args.codex_home)
    root = None if args.all_directories else args.cwd.resolve()
    scoped = select(records, root=root)

    per_chunk: list[dict[str, Any]] = []
    union: list[Record] = []
    for window in windows:
        rows = select(scoped, since=window.start, until=window.end)
        union.extend(rows)
        per_chunk.append(
            {
                "chunk_id": window.chunk_id,
                "issue": window.issue,
                "status": window.status,
                "ledger": str(window.source),
                "window_start": window.start.isoformat().replace("+00:00", "Z"),
                "window_end": window.end.isoformat().replace("+00:00", "Z"),
                "window_open_ended": window.open_ended,
                "calls": len(rows),
                **total(rows).as_dict(),
            }
        )
    combined = deduplicate(union)
    chunk_sum = sum(int(entry["billed_total"]) for entry in per_chunk)
    run_total = total(combined)
    overlap = chunk_sum - run_total.billed

    payload = {
        "schema": REPORT_SCHEMA,
        "generated_at": datetime.now(timezone.utc)
        .replace(microsecond=0)
        .isoformat()
        .replace("+00:00", "Z"),
        "scope": {
            "providers": list(providers),
            "directory": None if root is None else str(root),
            "ledgers": [str(p) for p in paths],
        },
        "note": (
            "Chunk windows can overlap when chunks are worked concurrently, so the run "
            "total is the deduplicated union of their records, not the sum of the rows."
        ),
        "chunks": per_chunk,
        "run_total": {"calls": len(combined), **run_total.as_dict()},
        "double_counted_if_summed": overlap,
    }

    if args.out:
        out = args.out.resolve()
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"wrote {out}")
    if args.json:
        print(json.dumps(payload, indent=2, sort_keys=True))
        return 0

    width = max([len("chunk")] + [len(entry["chunk_id"]) for entry in per_chunk])
    print(usage_header(width))
    for entry in per_chunk:
        usage = Usage(
            int(entry["input_uncached"]),
            int(entry["input_cached"]),
            int(entry["cache_write"]),
            int(entry["output"]),
            int(entry["reasoning_subset_of_output"]),
        )
        suffix = " (still open)" if entry["window_open_ended"] else ""
        print(usage_row(str(entry["chunk_id"]) + suffix, int(entry["calls"]), usage, width))
    print("-" * len(usage_header(width).splitlines()[0]))
    print(usage_row("RUN TOTAL", len(combined), run_total, width))
    if overlap:
        print(
            f"\n{thousands(overlap)} tokens appear in more than one chunk window; "
            "the run total counts them once."
        )
    if any(entry["window_open_ended"] for entry in per_chunk):
        print(
            "\nA chunk with no recorded review is open-ended: its window runs to "
            "--until, or to now."
        )
    return 0


def add_source_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "--provider",
        choices=(*PROVIDERS, "all"),
        default="all",
        help="which agent runtime's transcripts to read (default: all)",
    )
    parser.add_argument("--claude-home", type=Path, help="override ~/.claude")
    parser.add_argument("--codex-home", type=Path, help="override ~/.codex")
    parser.add_argument(
        "--cwd",
        type=Path,
        default=Path.cwd(),
        help="only count work done in this directory or below (default: current directory)",
    )
    parser.add_argument(
        "--all-directories",
        action="store_true",
        help="do not filter by working directory",
    )
    parser.add_argument("--json", action="store_true", help="emit a machine-readable report")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)

    report = sub.add_parser("report", help="total tokens over a time window and directory")
    add_source_arguments(report)
    report.add_argument("--since", help="ISO-8601 lower bound, e.g. 2026-09-19T00:00:00Z")
    report.add_argument("--until", help="ISO-8601 upper bound")
    report.add_argument("--session", help="restrict to one session or thread id")
    report.add_argument(
        "--by",
        choices=sorted(GROUPERS),
        default="provider",
        help="grouping for the breakdown (default: provider)",
    )

    ledger = sub.add_parser("ledger", help="attribute tokens to a run's frozen chunks")
    add_source_arguments(ledger)
    ledger.add_argument(
        "--state-dir",
        type=Path,
        default=Path(".loop-runs"),
        help="directory holding the run's review ledgers (default: .loop-runs)",
    )
    ledger.add_argument("--state", type=Path, nargs="+", help="explicit ledger files instead of a directory")
    ledger.add_argument("--until", help="ISO-8601 end for chunks with no recorded review")
    ledger.add_argument("--out", type=Path, help="write the JSON report to this file")

    return parser


def main(argv: list[str] | None = None) -> int:
    force_utf8_output()
    args = build_parser().parse_args(argv)
    try:
        if args.command == "report":
            return command_report(args)
        if args.command == "ledger":
            return command_ledger(args)
    except TokenError as exc:
        print(f"FAIL {exc}")
        return 1
    except (OSError, ValueError, TypeError) as exc:
        print(f"FAIL unexpected token accounting error: {exc}")
        return 1
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
