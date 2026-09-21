from __future__ import annotations

import io
import json
import contextlib
import sys
import tempfile
import unittest
from datetime import datetime, timezone
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import loop_tokens  # noqa: E402


LEDGER_SCHEMA = "derived-alg-geo-lean.loop-run/v1/ledger"


def write_jsonl(path: Path, entries: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("".join(json.dumps(entry) + "\n" for entry in entries), encoding="utf-8")


def claude_line(
    request_id: str,
    stamp: str,
    cwd: str,
    *,
    input_tokens: int = 10,
    cache_read: int = 100,
    cache_creation: int = 5,
    output: int = 20,
    thinking: int = 7,
    session: str = "session-a",
    model: str = "claude-opus-5",
    sidechain: bool = False,
    agent: str | None = None,
) -> dict:
    entry = {
        "type": "assistant",
        "requestId": request_id,
        "timestamp": stamp,
        "cwd": cwd,
        "sessionId": session,
        "isSidechain": sidechain,
        "message": {
            "id": f"msg_{request_id}",
            "model": model,
            "usage": {
                "input_tokens": input_tokens,
                "cache_read_input_tokens": cache_read,
                "cache_creation_input_tokens": cache_creation,
                "output_tokens": output,
                "output_tokens_details": {"thinking_tokens": thinking},
            },
        },
    }
    if agent is not None:
        entry["agentName"] = agent
    return entry


def codex_lines(
    cwd: str,
    responses: list[tuple[str, str, int, int, int]],
    *,
    session: str = "thread-a",
    model: str = "gpt-5.6-sol",
) -> list[dict]:
    """Build a rollout file: session_meta followed by token_usage_record lines.

    Each response is (response_id, timestamp, input_tokens, cached, output),
    where input_tokens is inclusive of cached, exactly as Codex reports it.
    """

    lines: list[dict] = [
        {
            "type": "session_meta",
            "timestamp": responses[0][1] if responses else "2026-09-19T00:00:00.000Z",
            "payload": {"session_id": session, "cwd": cwd, "model": model},
        }
    ]
    for index, (response_id, stamp, total_input, cached, output) in enumerate(responses):
        lines.append(
            {
                "type": "token_usage_record",
                "timestamp": stamp,
                "ordinal": index,
                "payload": {
                    "thread_id": session,
                    "response_id": response_id,
                    "usage": {
                        "input_tokens": total_input,
                        "cached_input_tokens": cached,
                        "cache_write_input_tokens": 0,
                        "output_tokens": output,
                        "reasoning_output_tokens": 0,
                        "total_tokens": total_input + output,
                    },
                    "turn_token_usage": {"total_tokens": 999999},
                    "thread_token_usage": {"total_tokens": 999999},
                },
            }
        )
    return lines


def ledger(chunk_id: str, created_at: str, review_stamps: list[str], *, issue: int = 1060) -> dict:
    rounds = []
    if review_stamps:
        rounds.append(
            {
                "number": 1,
                "commit": "abc1234",
                "reviews": [
                    {"reviewer": "mathematics-adversary", "verdict": "pass", "recorded_at": stamp}
                    for stamp in review_stamps
                ],
                "adjudication": None,
            }
        )
    return {
        "schema": LEDGER_SCHEMA,
        "chunk": {"id": chunk_id},
        "issue": {"number": issue, "slug": chunk_id},
        "status": "reviewing" if review_stamps else "initialized",
        "created_at": created_at,
        "rounds": rounds,
    }


class UsageNormalizationTest(unittest.TestCase):
    def test_reasoning_is_not_added_to_the_billed_total(self) -> None:
        usage = loop_tokens.Usage(
            input_uncached=10, input_cached=100, cache_write=5, output=20, reasoning=7
        )
        self.assertEqual(usage.billed, 135)

    def test_usage_addition_is_componentwise(self) -> None:
        combined = loop_tokens.Usage(1, 2, 3, 4, 5) + loop_tokens.Usage(10, 20, 30, 40, 50)
        self.assertEqual(combined.as_dict()["input_uncached"], 11)
        self.assertEqual(combined.as_dict()["reasoning_subset_of_output"], 55)
        self.assertEqual(combined.billed, 110)


class ClaudeReaderTest(unittest.TestCase):
    def test_one_response_split_across_lines_is_counted_once(self) -> None:
        """The measured failure mode: 75 lines, 36 requests, identical usage."""

        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp) / ".claude"
            repeated = claude_line("req_1", "2026-09-19T12:00:00.000Z", tmp)
            write_jsonl(
                home / "projects" / "slug" / "session-a.jsonl",
                [repeated, dict(repeated), dict(repeated)],
            )
            records = loop_tokens.collect(["claude"], claude_dir=home)
            self.assertEqual(len(records), 1)
            self.assertEqual(loop_tokens.total(records).billed, 135)

    def test_the_same_session_resumed_into_two_files_is_counted_once(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp) / ".claude"
            line = claude_line("req_1", "2026-09-19T12:00:00.000Z", tmp)
            write_jsonl(home / "projects" / "slug" / "a.jsonl", [line])
            write_jsonl(home / "projects" / "slug" / "b.jsonl", [dict(line)])
            self.assertEqual(len(loop_tokens.collect(["claude"], claude_dir=home)), 1)

    def test_subagent_turns_are_counted_and_attributed(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp) / ".claude"
            write_jsonl(
                home / "projects" / "slug" / "a.jsonl",
                [
                    claude_line("req_1", "2026-09-19T12:00:00.000Z", tmp),
                    claude_line(
                        "req_2",
                        "2026-09-19T12:01:00.000Z",
                        tmp,
                        sidechain=True,
                        agent="mathematics-adversary",
                    ),
                ],
            )
            records = loop_tokens.collect(["claude"], claude_dir=home)
            buckets = loop_tokens.group(records, "agent")
            self.assertEqual(sorted(buckets), ["(main thread)", "mathematics-adversary"])

    def test_a_truncated_final_line_does_not_lose_the_rest(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp) / ".claude"
            path = home / "projects" / "slug" / "a.jsonl"
            write_jsonl(path, [claude_line("req_1", "2026-09-19T12:00:00.000Z", tmp)])
            with path.open("a", encoding="utf-8") as handle:
                handle.write('{"type": "assistant", "message": {"usa')
            self.assertEqual(len(loop_tokens.collect(["claude"], claude_dir=home)), 1)


class CodexReaderTest(unittest.TestCase):
    def test_cached_input_is_subtracted_out_of_the_inclusive_input_count(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp) / ".codex"
            write_jsonl(
                home / "sessions" / "2026" / "09" / "19" / "rollout-a.jsonl",
                codex_lines(tmp, [("resp_1", "2026-09-19T12:00:00.000Z", 24635, 19968, 168)]),
            )
            usage = loop_tokens.total(loop_tokens.collect(["codex"], codex_dir=home))
            self.assertEqual(usage.input_uncached, 24635 - 19968)
            self.assertEqual(usage.input_cached, 19968)
            self.assertEqual(usage.output, 168)
            # Codex's own total_tokens is input (inclusive) + output.
            self.assertEqual(usage.billed, 24635 + 168)

    def test_cumulative_thread_totals_are_ignored(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp) / ".codex"
            write_jsonl(
                home / "sessions" / "2026" / "09" / "19" / "rollout-a.jsonl",
                codex_lines(
                    tmp,
                    [
                        ("resp_1", "2026-09-19T12:00:00.000Z", 100, 0, 10),
                        ("resp_2", "2026-09-19T12:01:00.000Z", 200, 50, 20),
                    ],
                ),
            )
            usage = loop_tokens.total(loop_tokens.collect(["codex"], codex_dir=home))
            self.assertEqual(usage.billed, 100 + 10 + 200 + 20)

    def test_working_directory_follows_a_later_turn_context(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp) / ".codex"
            inside = Path(tmp) / "repo"
            inside.mkdir()
            lines = codex_lines(str(inside), [("resp_1", "2026-09-19T12:00:00.000Z", 100, 0, 10)])
            lines.append(
                {
                    "type": "turn_context",
                    "timestamp": "2026-09-19T12:02:00.000Z",
                    "payload": {"cwd": str(Path(tmp) / "elsewhere")},
                }
            )
            lines.extend(
                codex_lines(str(inside), [("resp_2", "2026-09-19T12:03:00.000Z", 300, 0, 30)])[1:]
            )
            write_jsonl(home / "sessions" / "2026" / "09" / "19" / "rollout-a.jsonl", lines)
            records = loop_tokens.collect(["codex"], codex_dir=home)
            scoped = loop_tokens.select(records, root=inside.resolve())
            self.assertEqual(len(scoped), 1)
            self.assertEqual(loop_tokens.total(scoped).billed, 110)


class ScopeTest(unittest.TestCase):
    def test_a_subdirectory_counts_and_a_sibling_does_not(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "repo"
            (root / "sub").mkdir(parents=True)
            (Path(tmp) / "other").mkdir()
            home = Path(tmp) / ".claude"
            write_jsonl(
                home / "projects" / "slug" / "a.jsonl",
                [
                    claude_line("req_1", "2026-09-19T12:00:00.000Z", str(root)),
                    claude_line("req_2", "2026-09-19T12:01:00.000Z", str(root / "sub")),
                    claude_line("req_3", "2026-09-19T12:02:00.000Z", str(Path(tmp) / "other")),
                ],
            )
            records = loop_tokens.collect(["claude"], claude_dir=home)
            self.assertEqual(len(loop_tokens.select(records, root=root.resolve())), 2)

    def test_time_bounds_are_inclusive_and_exclude_outside_records(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            home = Path(tmp) / ".claude"
            write_jsonl(
                home / "projects" / "slug" / "a.jsonl",
                [
                    claude_line("req_1", "2026-09-19T11:59:59.000Z", tmp),
                    claude_line("req_2", "2026-09-19T12:00:00.000Z", tmp),
                    claude_line("req_3", "2026-09-19T12:30:00.000Z", tmp),
                ],
            )
            records = loop_tokens.collect(["claude"], claude_dir=home)
            window = loop_tokens.select(
                records,
                since=datetime(2026, 9, 19, 12, 0, tzinfo=timezone.utc),
                until=datetime(2026, 9, 19, 12, 30, tzinfo=timezone.utc),
            )
            self.assertEqual([record.key for record in window], ["req_2", "req_3"])


class CrossProviderTest(unittest.TestCase):
    def test_both_runtimes_add_into_one_comparable_total(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "repo"
            root.mkdir()
            claude = Path(tmp) / ".claude"
            codex = Path(tmp) / ".codex"
            write_jsonl(
                claude / "projects" / "slug" / "a.jsonl",
                [
                    claude_line(
                        "req_1",
                        "2026-09-19T12:00:00.000Z",
                        str(root),
                        input_tokens=10,
                        cache_read=100,
                        cache_creation=5,
                        output=20,
                    )
                ],
            )
            write_jsonl(
                codex / "sessions" / "2026" / "09" / "19" / "rollout-a.jsonl",
                codex_lines(str(root), [("resp_1", "2026-09-19T12:05:00.000Z", 200, 150, 30)]),
            )
            records = loop_tokens.collect(["claude", "codex"], claude_dir=claude, codex_dir=codex)
            scoped = loop_tokens.select(records, root=root.resolve())
            usage = loop_tokens.total(scoped)
            self.assertEqual(usage.input_uncached, 10 + 50)
            self.assertEqual(usage.input_cached, 100 + 150)
            self.assertEqual(usage.cache_write, 5)
            self.assertEqual(usage.output, 20 + 30)
            self.assertEqual(usage.billed, 135 + 230)
            self.assertEqual(sorted(loop_tokens.group(scoped, "provider")), ["claude", "codex"])


class LedgerWindowTest(unittest.TestCase):
    def test_window_runs_from_freeze_to_last_recorded_review(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "chunk.json"
            data = ledger(
                "chunk-a",
                "2026-09-19T12:00:00Z",
                ["2026-09-19T12:10:00Z", "2026-09-19T12:40:00Z"],
            )
            path.write_text(json.dumps(data), encoding="utf-8")
            window = loop_tokens.ledger_window(
                path, loop_tokens.load_ledger(path), datetime.now(timezone.utc)
            )
            self.assertEqual(window.chunk_id, "chunk-a")
            self.assertEqual(window.issue, 1060)
            self.assertFalse(window.open_ended)
            self.assertEqual(window.end, datetime(2026, 9, 19, 12, 40, tzinfo=timezone.utc))

    def test_a_chunk_with_no_review_stays_open_ended(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "chunk.json"
            path.write_text(json.dumps(ledger("chunk-a", "2026-09-19T12:00:00Z", [])), encoding="utf-8")
            fallback = datetime(2026, 9, 20, tzinfo=timezone.utc)
            window = loop_tokens.ledger_window(path, loop_tokens.load_ledger(path), fallback)
            self.assertTrue(window.open_ended)
            self.assertEqual(window.end, fallback)

    def test_a_file_that_is_not_a_review_ledger_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "chunk.json"
            path.write_text(json.dumps({"schema": "something-else"}), encoding="utf-8")
            with self.assertRaises(loop_tokens.TokenError):
                loop_tokens.load_ledger(path)


class LedgerCommandTest(unittest.TestCase):
    def run_ledger(self, argv: list[str]) -> tuple[int, str]:
        buffer = io.StringIO()
        with contextlib.redirect_stdout(buffer):
            code = loop_tokens.main(argv)
        return code, buffer.getvalue()

    def test_overlapping_chunk_windows_are_not_double_counted(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "repo"
            root.mkdir()
            state = Path(tmp) / ".loop-runs"
            state.mkdir()
            (state / "chunk-a.json").write_text(
                json.dumps(ledger("chunk-a", "2026-09-19T12:00:00Z", ["2026-09-19T13:00:00Z"])),
                encoding="utf-8",
            )
            (state / "chunk-b.json").write_text(
                json.dumps(
                    ledger("chunk-b", "2026-09-19T12:30:00Z", ["2026-09-19T13:30:00Z"], issue=1061)
                ),
                encoding="utf-8",
            )
            claude = Path(tmp) / ".claude"
            write_jsonl(
                claude / "projects" / "slug" / "a.jsonl",
                [
                    # Inside both windows.
                    claude_line("req_shared", "2026-09-19T12:45:00.000Z", str(root)),
                    # Inside chunk-a only.
                    claude_line("req_a", "2026-09-19T12:10:00.000Z", str(root)),
                ],
            )
            code, output = self.run_ledger(
                [
                    "ledger",
                    "--state-dir",
                    str(state),
                    "--cwd",
                    str(root),
                    "--claude-home",
                    str(claude),
                    "--provider",
                    "claude",
                    "--json",
                ]
            )
            self.assertEqual(code, 0)
            payload = json.loads(output)
            self.assertEqual(payload["run_total"]["calls"], 2)
            self.assertEqual(payload["run_total"]["billed_total"], 270)
            self.assertEqual(payload["double_counted_if_summed"], 135)

    def test_the_report_is_written_beside_the_ledger_and_never_into_it(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "repo"
            root.mkdir()
            state = Path(tmp) / ".loop-runs"
            state.mkdir()
            chunk = state / "chunk-a.json"
            original = ledger("chunk-a", "2026-09-19T12:00:00Z", ["2026-09-19T13:00:00Z"])
            chunk.write_text(json.dumps(original), encoding="utf-8")
            out = state / "chunk-a.tokens.json"
            code, _ = self.run_ledger(
                [
                    "ledger",
                    "--state-dir",
                    str(state),
                    "--cwd",
                    str(root),
                    "--claude-home",
                    str(Path(tmp) / "missing"),
                    "--provider",
                    "claude",
                    "--out",
                    str(out),
                ]
            )
            self.assertEqual(code, 0)
            self.assertTrue(out.is_file())
            self.assertEqual(json.loads(chunk.read_text(encoding="utf-8")), original)

    def test_a_generated_report_is_not_mistaken_for_a_ledger(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state = Path(tmp) / ".loop-runs"
            state.mkdir()
            (state / "chunk-a.json").write_text(
                json.dumps(ledger("chunk-a", "2026-09-19T12:00:00Z", ["2026-09-19T13:00:00Z"])),
                encoding="utf-8",
            )
            (state / "chunk-a.tokens.json").write_text("{}", encoding="utf-8")
            self.assertEqual([p.name for p in loop_tokens.discover_ledgers(state)], ["chunk-a.json"])

    def test_a_missing_state_directory_is_a_clear_failure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            code, output = self.run_ledger(["ledger", "--state-dir", str(Path(tmp) / "nope")])
            self.assertEqual(code, 1)
            self.assertIn("no ledger directory", output)


class ReportCommandTest(unittest.TestCase):
    def test_an_empty_scope_explains_itself_instead_of_printing_zero(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                code = loop_tokens.main(
                    [
                        "report",
                        "--cwd",
                        tmp,
                        "--claude-home",
                        str(Path(tmp) / "missing"),
                        "--codex-home",
                        str(Path(tmp) / "missing"),
                    ]
                )
            self.assertEqual(code, 0)
            self.assertIn("No token records matched", buffer.getvalue())

    def test_an_unparseable_bound_is_refused(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                code = loop_tokens.main(
                    ["report", "--cwd", tmp, "--since", "last tuesday", "--claude-home", tmp]
                )
            self.assertEqual(code, 1)
            self.assertIn("could not parse --since", buffer.getvalue())


if __name__ == "__main__":
    unittest.main()
