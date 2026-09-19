from __future__ import annotations

import contextlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

import loop_engine  # noqa: E402


REVIEWERS = [
    "mathematics-adversary",
    "repository-boundary-adversary",
    "abstraction-adversary",
    "mathlib-reviewer",
]


def make_spec(root: Path) -> tuple[Path, dict]:
    change_dir = root / "openspec" / "changes" / "pilot-change"
    (change_dir / "specs" / "capability").mkdir(parents=True)
    (root / "openspec").mkdir(exist_ok=True)
    (root / "openspec" / "config.yaml").write_text("schema: spec-driven\n", encoding="utf-8")
    (change_dir / "proposal.md").write_text("# Proposal\n\n## Why\nA valid reason.\n", encoding="utf-8")
    (change_dir / "design.md").write_text("# Design\n\n## Decisions\nKeep scope frozen.\n", encoding="utf-8")
    (change_dir / "tasks.md").write_text(
        "# Tasks\n\n## 1. Work\n\n- [ ] 1.1 Verify the test\n", encoding="utf-8"
    )
    (change_dir / "specs" / "capability" / "spec.md").write_text(
        "# Spec Delta\n\n## Purpose\nA sufficiently long purpose for the test capability.\n\n"
        "## ADDED Requirements\n\n### Requirement: Frozen scope\nThe system SHALL keep scope frozen.\n\n"
        "#### Scenario: Scope is fixed\n- **WHEN** a run starts\n- **THEN** the files remain fixed\n",
        encoding="utf-8",
    )
    spec = {
        "schema": loop_engine.RUN_SCHEMA,
        "id": "test-run",
        "repository": "example/repository",
        "actor": "test-actor",
        "remote": "origin",
        "base_branch": "main",
        "base_ref": "origin/main",
        "mode": "independent",
        "enabled": False,
        "state_dir": ".loop-runs",
        "roadmap_gate": "disabled",
        "openspec": {
            "change": "pilot-change",
            "validation": "structural",
            "required_artifacts": [
                "proposal.md",
                "design.md",
                "tasks.md",
                "specs/capability/spec.md",
            ],
        },
        "limits": {"min_issues": 1, "max_issues": 1, "max_review_rounds_per_chunk": 3},
        "review": {"independent": True, "reviewers": REVIEWERS},
        "runner": {"required_checks": ["ci"]},
        "closure": {"code_issue": "pr_merge_keyword", "allow_non_pr": False},
        "merge": {
            "method": "squash",
            "delete_branch": False,
            "allow_method_override": False,
            "allow_delete_branch_override": False,
            "allow_auto": False,
            "allow_admin": False,
        },
        "mutations": {
            "comment_issue": False,
            "close_issue": False,
            "push_branch": False,
            "create_pr": False,
            "approve_pr": False,
            "merge_pr": False,
        },
        "issues": [
            {
                "number": 1,
                "slug": "test-issue",
                "depends_on": [],
                "chunks": [
                    {
                        "id": "test-chunk",
                        "scope": "Test the frozen review ledger.",
                        "requirements": ["Frozen scope"],
                        "files": ["scripts/loop_engine.py"],
                        "acceptance": ["The ledger records independent verdicts."],
                    }
                ],
            }
        ],
    }
    spec_path = root / "run.yaml"
    import yaml

    spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
    return spec_path, spec


class LoopEngineTests(unittest.TestCase):
    def test_remote_and_blocker_normalization_match_github_shapes(self) -> None:
        self.assertEqual(
            loop_engine.normalize_remote("git@github.com:owner/repo.git"),
            "owner/repo",
        )
        self.assertEqual(
            loop_engine.blocked_by_entries({"blockedBy": {"nodes": [], "totalCount": 0}}),
            [],
        )
        self.assertEqual(
            loop_engine.blocked_by_entries({"blockedBy": {"nodes": [{"number": 7}], "totalCount": 1}}),
            [{"number": 7}],
        )

    def test_windows_openspec_command_uses_cmd_shim(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original_platform = loop_engine.sys.platform
            loop_engine.sys.platform = "win32"
            try:
                result = loop_engine.run_command(root, ["openspec", "--version"])
            finally:
                loop_engine.sys.platform = original_platform
            self.assertIsInstance(result, subprocess.CompletedProcess)

    def test_structural_openspec_validation_and_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            loaded = loop_engine.load_spec(spec_path, root)
            self.assertEqual(loaded["openspec"]["change"], "pilot-change")
            self.assertEqual(loop_engine.digest(loaded), loop_engine.digest(spec))

    def test_ledger_requires_all_reviewers_and_stops_after_three_rounds(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            self.assertEqual(loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None), 0)
            state_path = root / ".loop-runs" / "test-chunk.json"
            commit_a = "a" * 40
            commit_b = "b" * 40
            commit_c = "c" * 40
            commit_d = "d" * 40

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(
                    loop_engine.ledger_record_review(state_path, REVIEWERS[0], commit_a, "pass", None),
                    0,
                )
                self.assertNotEqual(
                    loop_engine.ledger_record_review(state_path, REVIEWERS[1], commit_b, "pass", None),
                    0,
                )
                for reviewer in REVIEWERS[1:]:
                    self.assertEqual(
                        loop_engine.ledger_record_review(state_path, reviewer, commit_a, "needs_changes", "fix"),
                        0,
                    )
                self.assertEqual(loop_engine.ledger_adjudicate(state_path, "needs_changes", "round one"), 0)

                for reviewer in REVIEWERS:
                    self.assertEqual(
                        loop_engine.ledger_record_review(state_path, reviewer, commit_b, "needs_changes", "fix"),
                        0,
                    )
                self.assertEqual(loop_engine.ledger_adjudicate(state_path, "needs_changes", "round two"), 0)

                for reviewer in REVIEWERS:
                    self.assertEqual(
                        loop_engine.ledger_record_review(state_path, reviewer, commit_c, "needs_changes", "stop"),
                        0,
                    )
                self.assertEqual(loop_engine.ledger_adjudicate(state_path, "needs_changes", "round three"), 0)
                self.assertNotEqual(
                    loop_engine.ledger_record_review(state_path, REVIEWERS[0], commit_d, "pass", None),
                    0,
                )

            state = json.loads(state_path.read_text(encoding="utf-8"))
            self.assertEqual(state["status"], "blocked")
            self.assertEqual(len(state["rounds"]), 3)
            self.assertEqual(state["rounds"][-1]["adjudication"]["verdict"], "blocked")

    def test_passed_ledger_is_terminal(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None)
            state_path = root / ".loop-runs" / "test-chunk.json"
            commit = "e" * 40
            with contextlib.redirect_stdout(io.StringIO()):
                for reviewer in REVIEWERS:
                    self.assertEqual(loop_engine.ledger_record_review(state_path, reviewer, commit, "pass", None), 0)
                self.assertEqual(loop_engine.ledger_adjudicate(state_path, "pass", "all clear"), 0)
                self.assertNotEqual(loop_engine.ledger_record_review(state_path, REVIEWERS[0], "f" * 40, "pass", None), 0)
            state = json.loads(state_path.read_text(encoding="utf-8"))
            self.assertEqual(state["status"], "passed")

    def test_missing_openspec_artifact_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            (root / "openspec" / "changes" / "pilot-change" / "design.md").unlink()
            with self.assertRaises(loop_engine.LoopError):
                loop_engine.load_spec(spec_path, root)

    def test_merge_command_is_bound_to_reviewed_head_and_safe_by_default(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            loaded = loop_engine.load_spec(spec_path, root)
            command = loop_engine.build_merge_command(
                loaded, 42, "a" * 40, None, False, False, None
            )
            self.assertEqual(
                command,
                [
                    "gh",
                    "pr",
                    "merge",
                    "42",
                    "--repo",
                    "example/repository",
                    "--squash",
                    "--match-head-commit",
                    "a" * 40,
                    "--delete-branch=false",
                ],
            )
            for kwargs in (
                {"method": "merge"},
                {"auto": True},
                {"admin": True},
                {"delete_branch": True},
            ):
                with self.assertRaises(loop_engine.LoopError):
                    loop_engine.build_merge_command(
                        loaded,
                        42,
                        "a" * 40,
                        kwargs.get("method"),
                        kwargs.get("auto", False),
                        kwargs.get("admin", False),
                        kwargs.get("delete_branch"),
                    )

    def test_merge_command_allows_only_manifest_authorized_variants(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            spec["merge"].update(
                {
                    "allow_method_override": True,
                    "allow_delete_branch_override": True,
                    "allow_auto": True,
                    "allow_admin": True,
                }
            )
            command = loop_engine.build_merge_command(
                spec, 42, "b" * 40, "rebase", True, False, True
            )
            self.assertEqual(
                command,
                [
                    "gh",
                    "pr",
                    "merge",
                    "42",
                    "--repo",
                    "example/repository",
                    "--rebase",
                    "--match-head-commit",
                    "b" * 40,
                    "--delete-branch",
                    "--auto",
                ],
            )
            with self.assertRaises(loop_engine.LoopError):
                loop_engine.build_merge_command(spec, 42, "b" * 40, None, True, True, None)


if __name__ == "__main__":
    unittest.main()
