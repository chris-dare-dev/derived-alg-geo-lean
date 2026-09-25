from __future__ import annotations

import contextlib
import gzip
import io
import json
import stat
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import loop_transcripts as lt  # noqa: E402


REPO = "/work/derived-alg-geo-lean"
ROOT = "01a0cb25-289c-7e90-99b4-328ee966be2e"
CHILD = "01a0cb5b-c43b-7fd2-b3fd-9c0ab04ba093"
OTHER = "01a0cfd6-8c2e-7000-8000-000000000001"
SESSION = "a70f32a9-fa4f-4b53-91e5-26dd0a83017a"
TOKEN = "ghp_" + "A" * 36


def codex_line(stamp: str, kind: str, payload: dict, ordinal: int = 0) -> dict:
    # Key order matters: Codex writes timestamp, ordinal, type, payload.
    return {"timestamp": stamp, "ordinal": ordinal, "type": kind, "payload": payload}


def item(stamp: str, thread: str, turn: str, body: dict) -> dict:
    return codex_line(stamp, "event_msg", {"type": "item_completed", "thread_id": thread, "turn_id": turn, "item": body})


def owner(stamp: str, thread: str, turn: str, text: str, *, client: bool = True) -> dict:
    body = {"type": "UserMessage", "id": "u", "content": [{"type": "text", "text": text}]}
    if client:
        body["client_id"] = "desktop"
    return item(stamp, thread, turn, body)


def agent(stamp: str, thread: str, turn: str, text: str, phase: str = "commentary") -> dict:
    return item(stamp, thread, turn, {"type": "AgentMessage", "id": "a", "phase": phase,
                                      "content": [{"type": "Text", "text": text}]})


def command(stamp: str, thread: str, turn: str, cmd: str, *, exit_code: int = 0, output: str = "",
            cwd: str = REPO) -> dict:
    return item(stamp, thread, turn, {
        "type": "CommandExecution", "id": "c", "command": ["/bin/bash", "-lc", cmd], "cwd": f"file://{cwd}",
        "status": "completed", "exit_code": exit_code, "duration": {"secs": 2, "nanos": 500_000_000},
        "aggregated_output": output,
    })


def complete(stamp: str, turn: str, text: str) -> dict:
    return codex_line(stamp, "event_msg", {"type": "task_complete", "turn_id": turn, "last_agent_message": text})


def call(stamp: str, name: str, call_id: str, arguments: dict) -> dict:
    return codex_line(stamp, "response_item", {"type": "function_call", "name": name, "call_id": call_id,
                                                "arguments": json.dumps(arguments)})


def call_output(stamp: str, call_id: str, output: str) -> dict:
    return codex_line(stamp, "response_item", {"type": "function_call_output", "call_id": call_id, "output": output})


def usage(stamp: str, thread: str, response: str, total: int, cached: int, out: int) -> dict:
    return codex_line(stamp, "token_usage_record", {
        "thread_id": thread, "response_id": response,
        "usage": {"input_tokens": total, "cached_input_tokens": cached, "output_tokens": out, "reasoning_output_tokens": 1},
    })


def meta(stamp: str, thread: str, *, parent: str | None = None, cwd: str = REPO, source: str = "vscode") -> dict:
    payload = {"id": thread, "session_id": parent or thread, "timestamp": stamp, "cwd": cwd,
               "originator": "Codex Desktop", "cli_version": "0.155.1", "source": source,
               "thread_source": "subagent" if parent else "user", "git": {"branch": "main"}}
    if parent:
        payload.update(parent_thread_id=parent, agent_path="/root/altitude_scout", agent_nickname="Kepler")
    return codex_line(stamp, "session_meta", payload)


def write_jsonl(path: Path, entries: list[dict], *, compact: bool = True) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    separators = (",", ":") if compact else (", ", ": ")
    path.write_text("".join(json.dumps(entry, separators=separators) + "\n" for entry in entries), encoding="utf-8")


def build_codex(home: Path) -> None:
    day = home / "sessions" / "2026" / "09" / "22"
    write_jsonl(day / f"rollout-2026-09-22T22-00-00-{ROOT}.jsonl", [
        meta("2026-09-22T22:00:00Z", ROOT),
        codex_line("2026-09-22T22:00:01Z", "turn_context", {"model": "gpt-6-luna", "cwd": REPO}),
        owner("2026-09-22T22:00:02Z", ROOT, "t1", "Tackle issue #919."),
        agent("2026-09-22T22:00:03Z", ROOT, "t1", "Reading the issue and the controller."),
        command("2026-09-22T22:00:04Z", ROOT, "t1", "python3 scripts/loop_engine.py preflight --spec x.yaml"),
        item("2026-09-22T22:00:05Z", ROOT, "t1", {"type": "FileChange", "id": "f", "changes": {
            f"{REPO}/DerivedAlgGeo/CategoryTheory/Foo.lean": {"type": "update"}}}),
        command("2026-09-22T22:00:06Z", ROOT, "t1", "LEAN_NUM_THREADS=2 ~/.elan/bin/lake build DerivedAlgGeo.Foo",
                exit_code=1, output="building\nerror: unknown identifier 'bar'"),
        command("2026-09-22T22:00:07Z", ROOT, "t1", f"GH_TOKEN={TOKEN} gh pr create --title x"),
        command("2026-09-22T22:00:07Z", ROOT, "t1", "gh pr merge 1476 --squash", exit_code=1, output="not mergeable"),
        command("2026-09-22T22:00:07Z", ROOT, "t1", "gh pr merge 1478 --squash"),
        item("2026-09-22T22:00:08Z", ROOT, "t1", {"type": "SubAgentActivity", "id": "s", "kind": "started",
                                                   "agent_thread_id": CHILD, "agent_path": "/root/altitude_scout"}),
        call("2026-09-22T22:00:09Z", "request_user_input_async", "ask-1", {"questions": [{"title": "t", "question": "q"}]}),
        call_output("2026-09-22T22:00:09Z", "ask-1", "failed to parse function arguments: unknown field `question`"),
        call("2026-09-22T22:00:10Z", "request_user_input_async", "ask-2",
             {"questions": [{"title": "May I merge PR #1478?", "options": ["Yes", "No"]}]}),
        call_output("2026-09-22T22:00:10Z", "ask-2", '{"accepted":true}'),
        call("2026-09-22T22:00:11Z", "sleep", "sleep-1", {"duration_ms": 30000}),
        call_output("2026-09-22T22:00:41Z", "sleep-1", "slept"),
        usage("2026-09-22T22:00:42Z", ROOT, "r1", 1000, 800, 50),
        agent("2026-09-22T22:00:43Z", ROOT, "t1", "Waiting on you.", phase="final_answer"),
        complete("2026-09-22T22:00:44Z", "t1", "Implemented. Please merge PR #1478 so preflight can run."),
        owner("2026-09-22T22:30:44Z", ROOT, "t2", "Merged; continue."),
        agent("2026-09-22T22:30:45Z", ROOT, "t2", "Continuing."),
        complete("2026-09-22T22:31:00Z", "t2", "Blocked on the review round cap."),
        owner("2026-09-22T23:31:00Z", ROOT, "t3",
              "<heartbeat>\n<automation_id>continue-loop</automation_id>\n<instructions>go</instructions>", client=False),
        agent("2026-09-22T23:31:01Z", ROOT, "t3", "Resuming after the heartbeat."),
        complete("2026-09-22T23:32:00Z", "t3", "All issues merged."),
    ])
    # A forked subagent: its own meta, then its parent's replayed history, then its own work.
    write_jsonl(day / f"rollout-2026-09-22T22-00-08-{CHILD}.jsonl", [
        meta("2026-09-22T22:00:08Z", CHILD, parent=ROOT),
        meta("2026-09-22T22:00:00Z", ROOT),
        codex_line("2026-09-22T22:00:08Z", "event_msg", {"type": "task_started", "turn_id": "t1"}),
        codex_line("2026-09-22T22:00:08Z", "response_item", {"type": "message", "role": "user",
                                                              "content": [{"type": "input_text", "text": "Tackle issue #919."}]}),
        complete("2026-09-22T22:00:08Z", "t1", "a replayed parent stop"),
        codex_line("2026-09-22T22:00:08Z", "response_item", {
            "type": "agent_message", "author": "/root", "recipient": "/root/altitude_scout",
            "content": [{"type": "input_text", "text": "Message Type: NEW_TASK\nTask name: /root/altitude_scout\nSender: /root\nPayload:\n"},
                        {"type": "encrypted_content", "encrypted_content": "gAAAA"}]}),
        command("2026-09-22T22:00:09Z", CHILD, "c1", "rg -n 'Rouquier' .lake/packages/mathlib/Mathlib/"),
        agent("2026-09-22T22:00:20Z", CHILD, "c1", "Mathlib already has this in greater generality.", phase="final_answer"),
        usage("2026-09-22T22:00:20Z", CHILD, "r2", 500, 100, 20),
        complete("2026-09-22T22:00:21Z", "c1", "Mathlib already has this in greater generality."),
    ])
    write_jsonl(day / f"rollout-2026-09-22T12-00-00-{OTHER}.jsonl", [
        meta("2026-09-22T12:00:00Z", OTHER, cwd="/home/someone"),
        owner("2026-09-22T12:00:01Z", OTHER, "o1", "Restore my cloud credentials."),
        command("2026-09-22T12:00:02Z", OTHER, "o1", "aws configure list", cwd="/home/someone"),
        complete("2026-09-22T12:00:03Z", "o1", "Done."),
    ])
    write_jsonl(home / "session_index.jsonl", [{"id": ROOT, "thread_name": "ROU1 loop engineering"}])


def claude_line(kind: str, stamp: str, content, **extra) -> dict:
    entry = {"type": kind, "timestamp": stamp, "sessionId": SESSION, "cwd": REPO, "gitBranch": "main",
             "version": "2.1.280", "message": {"role": kind, "content": content}}
    entry.update(extra)
    return entry


def build_claude(home: Path) -> Path:
    project = home / "projects" / "-work-derived-alg-geo-lean"
    session = project / f"{SESSION}.jsonl"
    write_jsonl(session, [
        {"type": "custom-title", "customTitle": "Loop engineering autonomy analysis", "sessionId": SESSION},
        claude_line("user", "2026-09-22T22:22:00Z", "Why does the loop keep stopping?"),
        claude_line("assistant", "2026-09-22T22:22:05Z", [
            {"type": "text", "text": "Reading the controller."},
            {"type": "tool_use", "id": "tu1", "name": "Bash", "input": {"command": "sed -n 1,80p scripts/loop_engine.py"}},
        ], requestId="req1", **{"message": {"role": "assistant", "model": "claude-opus-5-5", "content": [
            {"type": "text", "text": "Reading the controller."},
            {"type": "tool_use", "id": "tu1", "name": "Bash", "input": {"command": "sed -n 1,80p scripts/loop_engine.py"}}],
            "usage": {"input_tokens": 10, "cache_read_input_tokens": 100, "cache_creation_input_tokens": 5, "output_tokens": 20}}}),
        claude_line("user", "2026-09-22T22:22:07Z", [{"type": "tool_result", "tool_use_id": "tu1", "content": "Exit code 2\nno such file"}]),
        claude_line("assistant", "2026-09-22T22:22:08Z", [
            {"type": "tool_use", "id": "tu2", "name": "Agent", "input": {"subagent_type": "general-purpose", "description": "Map stops"}}]),
        claude_line("user", "2026-09-22T22:22:09Z", [{"type": "tool_result", "tool_use_id": "tu2", "content": "launched"}]),
        claude_line("assistant", "2026-09-22T22:22:10Z", [{"type": "text", "text": "The mapping agent is running."}]),
        claude_line("user", "2026-09-22T22:30:00Z", "<task-notification>\n<status>completed</status>\n</task-notification>"),
        claude_line("assistant", "2026-09-22T22:30:05Z", [{"type": "text", "text": "Here is the analysis. Shall I fix 1-4?"}]),
        claude_line("user", "2026-09-22T22:40:05Z", "begin tackling 1-4 above"),
        claude_line("assistant", "2026-09-22T22:40:10Z", [
            {"type": "tool_use", "id": "tu3", "name": "AskUserQuestion", "input": {"questions": [
                {"question": "Which grants should the standing file carry?", "options": [{"label": "merge"}, {"label": "none"}]}]}}]),
        claude_line("user", "2026-09-22T22:45:10Z", [{"type": "tool_result", "tool_use_id": "tu3", "content": "merge"}]),
        claude_line("assistant", "2026-09-22T22:45:20Z", [
            {"type": "tool_use", "id": "tu4", "name": "Edit", "input": {"file_path": f"{REPO}/scripts/loop_engine.py"}}]),
        claude_line("user", "2026-09-22T22:45:21Z", [{"type": "tool_result", "tool_use_id": "tu4", "content": "ok"}]),
        claude_line("assistant", "2026-09-22T22:45:30Z", [{"type": "text", "text": "Implemented in draft PR #1473."}]),
    ])
    subagent = project / SESSION / "subagents" / "agent-a21d58ba745c6846d.jsonl"
    write_jsonl(subagent, [
        claude_line("user", "2026-09-22T22:22:09Z", "READ-ONLY: map every stop cause.", isSidechain=True),
        claude_line("assistant", "2026-09-22T22:23:00Z", [
            {"type": "tool_use", "id": "s1", "name": "Grep", "input": {"pattern": "preflight", "path": "scripts/loop_engine.py"}}],
            isSidechain=True),
        claude_line("user", "2026-09-22T22:23:01Z", [{"type": "tool_result", "tool_use_id": "s1", "content": "hits"}], isSidechain=True),
        claude_line("assistant", "2026-09-22T22:29:00Z", [{"type": "text", "text": "Seven stop causes, each mapped."}], isSidechain=True),
    ])
    subagent.with_name("agent-a21d58ba745c6846d.meta.json").write_text(
        json.dumps({"agentType": "general-purpose", "description": "Map protocol rules causing stops"}), encoding="utf-8")
    return session


class Fixture(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        base = Path(self.tmp.name)
        self.codex = base / "codex"
        self.claude = base / "claude"
        self.archive_dir = base / "archive"
        build_codex(self.codex)
        self.session = build_claude(self.claude)
        self.matcher = lt.RepoMatcher(["derived-alg-geo-lean"])

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def sources(self) -> list[lt.Source]:
        return lt.discover([self.codex], self.claude)

    def source(self, thread_id: str) -> lt.Source:
        return next(s for s in self.sources() if s.thread_id == thread_id)

    def read(self, thread_id: str) -> lt.Thread:
        return lt.Reader(lt.Archive(self.archive_dir), self.matcher).source(self.source(thread_id))

    def sync(self, **kwargs) -> dict:
        return lt.sync(lt.Archive(self.archive_dir), self.sources(), self.matcher, log=lambda *_: None, **kwargs)

    def run_json(self, root_id: str) -> dict:
        return next(s for s in lt.Archive(self.archive_dir).summaries() if s["root_id"] == root_id)


class CodexReaderTest(Fixture):
    def test_owner_messages_stops_and_asks(self) -> None:
        root = self.read(ROOT)
        facts = lt.analyze(lt.Run(root=root, children=[]))
        self.assertEqual(root.title, "ROU1 loop engineering")
        self.assertEqual(root.model, "gpt-6-luna")
        # The heartbeat carries no client id: it keeps the run going, but it is not the owner.
        self.assertEqual(facts["owner_messages"], 2)
        self.assertEqual(facts["heartbeats"], 1)
        # The malformed ask the agent retried is one question, not two.
        self.assertEqual(facts["asks"], 1)
        self.assertEqual([s["answered_by"] for s in facts["stops"]], ["owner", "auto", "end"])
        first, second, last = facts["stops"]
        self.assertEqual(first["wait_s"], 1800.0)
        self.assertIn("merge-first", first["tags"])
        self.assertIn("May I merge PR #1478?", first["asks"][0])
        self.assertEqual(second["revived_by"], "heartbeat")
        self.assertEqual(second["wait_s"], 3600.0)
        self.assertEqual(facts["waiting_on_owner_s"], 1800.0)
        self.assertEqual(facts["idle_until_revived_s"], 3600.0)
        self.assertEqual(facts["prs"], [1478])
        # A failed merge is not a merge.
        self.assertEqual((facts["prs_created"], facts["prs_merged"]), (1, 1))

    def test_commands_are_categorized_timed_and_redacted(self) -> None:
        tools = [e for e in self.read(ROOT).events if e.kind == "tool"]
        by_category = {e.cat: e for e in tools}
        self.assertIn("controller", by_category)
        self.assertIn("lean-edit", by_category)
        build = by_category["lean-build"]
        self.assertEqual(build.exit, 1)
        self.assertEqual(build.dur, 2.5)
        self.assertIn("unknown identifier", build.text)
        self.assertEqual(by_category["waiting"].dur, 30.0)
        github = next(e for e in tools if "gh pr create" in e.text)
        self.assertNotIn(TOKEN, github.text)
        self.assertIn("[REDACTED]", github.text)

    def test_usage_is_normalized_to_disjoint_buckets(self) -> None:
        root = self.read(ROOT)
        # Codex's input_tokens includes the cached prefix.
        self.assertEqual(root.usage["input_uncached"], 200)
        self.assertEqual(root.usage["input_cached"], 800)
        self.assertEqual(root.usage["billed_total"], 1050)

    def test_forked_subagent_does_not_inherit_its_parents_replay(self) -> None:
        child = self.read(CHILD)
        kinds = [e.kind for e in child.events]
        self.assertEqual(child.parent, ROOT)
        self.assertEqual(child.role, "/root/altitude_scout")
        self.assertNotIn("owner", kinds)
        self.assertEqual(kinds.count("stop"), 1)
        self.assertEqual(kinds.count("task"), 1)
        self.assertNotIn("a replayed parent stop", [e.text for e in child.events])
        self.assertEqual([e.cat for e in child.events if e.kind == "tool"], ["lean-read"])
        self.assertEqual(child.usage["billed_total"], 520)

    def test_whitespace_in_json_is_tolerated(self) -> None:
        path = next(self.codex.rglob(f"*{ROOT}.jsonl"))
        entries = [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines()]
        write_jsonl(path, entries, compact=False)
        self.assertEqual(lt.analyze(lt.Run(root=self.read(ROOT), children=[]))["owner_messages"], 2)


class ClaudeReaderTest(Fixture):
    def test_a_run_still_going_counts_its_current_stretch(self) -> None:
        root = self.read(ROOT)
        # Cut the transcript after the owner's reply, while the run is still working.
        root.events = [e for e in root.events if e.t < "2026-09-22T22:31:00Z"]
        root.events.append(lt.Event(t="2026-09-23T01:00:44Z", kind="tool", text="lake build X", cat="lean-build"))
        root.end = root.events[-1].t
        facts = lt.analyze(lt.Run(root=root, children=[]))
        self.assertEqual(facts["stops"][-1]["answered_by"], "owner")
        self.assertEqual(facts["longest_autonomous_s"], 9000.0)

    def test_turns_notifications_and_a_blocking_question(self) -> None:
        root = self.read(SESSION)
        facts = lt.analyze(lt.Run(root=root, children=[]))
        self.assertEqual(root.title, "Loop engineering autonomy analysis")
        self.assertEqual(facts["owner_messages"], 2)
        self.assertEqual([s["answered_by"] for s in facts["stops"]], ["auto", "owner", "end"])
        self.assertEqual(facts["stops"][0]["revived_by"], "notification")
        self.assertEqual(facts["stops"][1]["wait_s"], 600.0)
        ask = next(e for e in root.events if e.kind == "ask")
        self.assertEqual(ask.dur, 300.0)
        self.assertIn("owner answered: merge", ask.text)
        # A question the runtime blocked on is owner wait too.
        self.assertEqual(facts["waiting_on_owner_s"], 900.0)
        failed = next(e for e in root.events if e.kind == "tool" and e.cat == "controller" and e.exit)
        self.assertEqual(failed.exit, 2)
        self.assertEqual(root.usage["billed_total"], 135)

    def test_subagent_meta_names_its_role(self) -> None:
        child = self.read(f"{SESSION}:agent-a21d58ba745c6846d")
        self.assertEqual(child.parent, SESSION)
        self.assertEqual(child.role, "general-purpose")
        self.assertEqual(child.title, "Map protocol rules causing stops")
        self.assertEqual([e.kind for e in child.events][0], "task")


class SyncTest(Fixture):
    def test_keeps_related_runs_groups_subagents_and_skips_the_rest(self) -> None:
        counts = self.sync()
        self.assertEqual(counts["runs"], 2)
        self.assertEqual(counts["skipped"], 1)
        codex_run = self.run_json(ROOT)
        self.assertEqual(codex_run["subagents"], 1)
        self.assertEqual(self.run_json(SESSION)["subagents"], 1)
        roots = {s["root_id"] for s in lt.Archive(self.archive_dir).summaries()}
        self.assertNotIn(OTHER, roots)
        key = codex_run["key"]
        runs = self.archive_dir / "runs"
        for suffix in (".md", ".json", ".commands.tsv"):
            self.assertTrue((runs / f"{key}{suffix}").is_file(), suffix)
        self.assertFalse(any(self.archive_dir.rglob(f"*{OTHER}*")))
        index = (self.archive_dir / "index.md").read_text(encoding="utf-8")
        self.assertIn("ROU1 loop engineering", index)

    def test_raw_copies_are_lossless_and_everything_is_owner_only(self) -> None:
        self.sync()
        archive = lt.Archive(self.archive_dir)
        raw = archive.raw_path("codex", ROOT)
        original = next(self.codex.rglob(f"*{ROOT}.jsonl")).read_bytes()
        with gzip.open(raw, "rb") as handle:
            self.assertEqual(handle.read(), original)
        self.assertIn(TOKEN.encode(), original)
        for path in [self.archive_dir, *self.archive_dir.rglob("*")]:
            mode = stat.S_IMODE(path.stat().st_mode)
            self.assertEqual(mode, 0o700 if path.is_dir() else 0o600, path)
        derived = [p for p in self.archive_dir.rglob("*") if p.is_file() and "raw" not in p.parts]
        for path in derived:
            self.assertNotIn(TOKEN, path.read_text(encoding="utf-8"), path)

    def test_resync_reads_only_what_changed(self) -> None:
        self.sync()
        self.assertEqual(self.sync()["read"], 0)
        path = next(self.codex.rglob(f"*{ROOT}.jsonl"))
        with path.open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(owner("2026-09-23T00:00:00Z", ROOT, "t4", "One more thing."), separators=(",", ":")) + "\n")
        self.assertEqual(self.sync()["read"], 1)
        self.assertEqual(self.run_json(ROOT)["owner_messages"], 3)

    def test_a_run_outlives_its_deleted_source_and_reparses_from_raw(self) -> None:
        self.sync()
        self.session.unlink()
        self.sync()
        self.assertEqual(self.run_json(SESSION)["owner_messages"], 2)
        # A parser change re-reads the archived raw copy when the source is gone.
        state_path = self.archive_dir / "state.json"
        state = json.loads(state_path.read_text(encoding="utf-8"))
        state["threads"][SESSION]["parser"] = 0
        state_path.write_text(json.dumps(state), encoding="utf-8")
        self.assertEqual(self.sync()["read"], 1)
        self.assertEqual(self.run_json(SESSION)["owner_messages"], 2)

    def test_include_all_keeps_unrelated_runs(self) -> None:
        self.assertEqual(self.sync(include_all=True)["runs"], 3)


class ClassificationTest(unittest.TestCase):
    def test_commands(self) -> None:
        cases = {
            "python3 scripts/loop_engine.py preflight --spec x": "controller",
            "git show origin/main:scripts/loop_engine.py | sed -n 1,90p": "controller",
            "npx -y @fission-ai/openspec validate --strict": "openspec",
            "sed -n 1,40p openspec/changes/x/tasks.md": "openspec",
            "cat .loop-runs/x/ledger.json": "loop-state",
            "cd /work/derived-alg-geo-lean && LEAN_NUM_THREADS=2 ~/.elan/bin/lake build DerivedAlgGeo.X": "lean-build",
            "gh pr checks 1481 --watch": "ci-wait",
            "sleep 60": "ci-wait",
            "gh pr view 1481 --json state": "github",
            "rg -n 'theorem' DerivedAlgGeo/CategoryTheory": "lean-read",
            "sed -n 1,50p .lake/packages/mathlib/Mathlib/Order/Basic.lean": "lean-read",
            "python3 scripts/check_layering.py": "gates",
            "sed -n 1,200p AGENTS.md": "instructions",
            "cd /work/derived-alg-geo-lean && git status --short": "git",
            "ls -la": "other",
        }
        for text, expected in cases.items():
            with self.subTest(text=text):
                self.assertEqual(lt.categorize_command(text), expected)

    def test_paths(self) -> None:
        self.assertEqual(lt.categorize_paths(["/w/DerivedAlgGeo/X.lean"]), "lean-edit")
        self.assertEqual(lt.categorize_paths(["/w/DerivedAlgGeo/X.lean"], reading=True), "lean-read")
        self.assertEqual(lt.categorize_paths(["/w/openspec/changes/x/proposal.md"]), "openspec")
        self.assertEqual(lt.categorize_paths(["/w/.claude/loop-specs/x.yaml"]), "loop-state")
        self.assertEqual(lt.categorize_paths(["/w/scripts/loop_engine.py"]), "controller")

    def test_invocations_ignore_commands_that_are_only_mentioned(self) -> None:
        self.assertEqual(next(lt.invocations("GH_TOKEN=x gh pr merge 12 --squash"))[:4], ["gh", "pr", "merge", "12"])
        heredoc = "python3 - <<'PY'\nprint('gh pr merge 1478 --squash')\nPY"
        self.assertFalse(any(w[:3] == ["gh", "pr", "merge"] for w in lt.invocations(heredoc)))

    def test_stop_tags_read_the_closing_lines_not_the_whole_report(self) -> None:
        report = ("OpenSpec validation passed and the manifest is merged. " * 30
                  + "\n\n" + "The chunk stays at its last head until this is settled. " * 12
                  + "\nMay I remove the `blocked` label?")
        tags = lt.stop_tags(report)
        self.assertIn("authority", tags)
        self.assertIn("blocked", tags)
        self.assertNotIn("openspec", tags)

    def test_redaction(self) -> None:
        text = f"token {TOKEN} and password=hunter2hunter2 and AKIA{'B' * 16}"
        redacted = lt.redact(text)
        self.assertNotIn(TOKEN, redacted)
        self.assertNotIn("hunter2hunter2", redacted)
        self.assertIn("password=[REDACTED]", redacted)
        self.assertNotIn("AKIA", redacted)


class CommandLineTest(Fixture):
    def run_main(self, *argv: str) -> tuple[int, str]:
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            code = lt.main(["--archive", str(self.archive_dir), *argv])
        return code, out.getvalue()

    def test_reports_read_the_archive(self) -> None:
        code, _ = self.run_main("sync", "--codex-home", str(self.codex), "--claude-home", str(self.claude),
                                "--match", "derived-alg-geo-lean", "--quiet")
        self.assertEqual(code, 0)
        code, text = self.run_main("stops", "--json", "--owner-only")
        self.assertEqual(code, 0)
        payload = {entry["title"]: entry["stops"] for entry in json.loads(text)}
        self.assertEqual([s["answered_by"] for s in payload["ROU1 loop engineering"]], ["owner", "end"])
        code, text = self.run_main("list")
        self.assertEqual(code, 0)
        self.assertIn("ROU1 loop engineering", text)
        code, text = self.run_main("profile", "--run", "ROU1")
        self.assertIn("controller", text)
        code, text = self.run_main("show", "ROU1")
        self.assertEqual(code, 0)
        self.assertIn("# ROU1 loop engineering", text)
        self.assertIn("Please merge PR #1478", text)

    def test_an_empty_archive_says_so(self) -> None:
        code, text = self.run_main("list")
        self.assertEqual(code, 1)
        self.assertIn("sync", text)


if __name__ == "__main__":
    unittest.main()
