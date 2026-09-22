from __future__ import annotations

import contextlib
import hashlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
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


def reviewer_output(root: Path, reviewer: str, verdict: str, body: str = "") -> Path:
    """Write a plausible verbatim reviewer message and return its path.

    The controller requires the reviewer's own text as evidence, so tests must
    supply it the same way the run-loop skill does.
    """
    token = loop_engine.CONTRACT_VERDICT_TOKENS[verdict]
    path = root / f"review-{reviewer}-{verdict}.md"
    text = body or f"{reviewer} reviewed the frozen chunk.\n"
    path.write_text(f"{text}\nClose: {token}, 0 findings, 0 lifts.\n", encoding="utf-8")
    return path


def write_backlog(root: Path, *targets: str) -> Path:
    """Create the tracked generalization backlog, optionally already carrying rows."""
    path = root / loop_engine.BACKLOG_PATH
    path.parent.mkdir(parents=True, exist_ok=True)
    rows = "".join(f"### 2026-09-20 - leaf\n- proposed ancestor: {t}\n\n" for t in targets)
    path.write_text("# Generalization backlog\n\n" + rows, encoding="utf-8")
    return path


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
        "limits": {"min_issues": 1, "max_issues": 1, "max_review_rounds_per_chunk": 5},
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


def predecessor_binding(number: int = 41) -> dict:
    return {
        "number": number,
        "manifest_id": "generic-restriction",
        "chunk_id": "generic-restriction-chunk",
        "spec_digest": "b" * 64,
        "openspec_digest": "c" * 64,
        "max_review_rounds": 3,
        "issue_number": 928,
        "source_branch": "agent/dt1-exact-bifunctor-restriction",
        "closure": "progress",
        "reviewed_head": "a" * 40,
        "merge_commit": "d" * 40,
    }


def predecessor_pr(binding: dict, comments: list[dict] | None = None) -> dict:
    return {
        "state": "MERGED",
        "mergedAt": "2026-09-22T00:00:00Z",
        "baseRefName": "main",
        "headRefName": binding["source_branch"],
        "headRefOid": binding["reviewed_head"],
        "body": f"Refs #{binding['issue_number']}\n",
        "mergeCommit": {"oid": binding["merge_commit"]},
        "comments": comments or [],
    }


def passing_ledger_state(root: Path, spec: dict, closure: str = "complete") -> dict:
    issue = spec["issues"][0]
    return {
        "spec_id": spec["id"],
        "spec_digest": loop_engine.digest(spec),
        "openspec_digest": loop_engine.openspec_digest(root, spec),
        "issue": {"number": issue["number"], "slug": issue["slug"]},
        "chunk": {
            "id": issue["chunks"][0]["id"],
            "files": issue["chunks"][0]["files"],
            "closure": closure,
        },
        "max_review_rounds": spec["limits"]["max_review_rounds_per_chunk"],
        "status": "passed",
        "rounds": [
            {
                "commit": "a" * 40,
                "adjudication": {"verdict": "pass"},
            }
        ],
    }


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
            loop_engine.blocked_by_entries({"blockedBy": {"nodes": [], "totalCount": 1}}),
            [{}],
        )
        self.assertEqual(
            loop_engine.blocked_by_entries({"blockedBy": {"nodes": [{"number": 7}], "totalCount": 1}}),
            [{"number": 7}],
        )

    def test_windows_openspec_command_uses_cmd_shim(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            original_platform = loop_engine.sys.platform
            try:
                loop_engine.sys.platform = "win32"
                with mock.patch.object(
                    loop_engine.subprocess,
                    "run",
                    return_value=subprocess.CompletedProcess(["openspec.cmd"], 0, "", ""),
                ) as process:
                    result = loop_engine.run_command(root, ["openspec", "--version"])
            finally:
                loop_engine.sys.platform = original_platform
            self.assertIsInstance(result, subprocess.CompletedProcess)
            self.assertEqual(process.call_args.args[0], ["openspec.cmd", "--version"])

    def test_structural_openspec_validation_and_manifest(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            loaded = loop_engine.load_spec(spec_path, root)
            self.assertEqual(loaded["openspec"]["change"], "pilot-change")
            self.assertEqual(loop_engine.digest(loaded), loop_engine.digest(spec))

    def test_epic_opt_in_is_explicit_and_selected_only(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            spec["eligibility"] = {"allow_epic_issues": [1]}
            import yaml

            spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
            self.assertEqual(loop_engine.load_spec(spec_path, root)["eligibility"], spec["eligibility"])
            spec["eligibility"] = {"allow_epic_issues": [2]}
            spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError):
                loop_engine.load_spec(spec_path, root)

    def test_roadmap_gate_is_scoped_to_manifest_base(self) -> None:
        self.assertEqual(
            loop_engine.roadmap_gate_args("agent/sf11-base"),
            [
                "python",
                "scripts/check_roadmap.py",
                "--require-api",
                "--scope-to-diff=agent/sf11-base",
            ],
        )

    def test_frozen_scope_preserves_dot_directories(self) -> None:
        self.assertTrue(
            loop_engine.path_is_in_frozen_chunk(
                ".claude/README.md", [".claude"]
            )
        )
        self.assertTrue(
            loop_engine.path_is_in_frozen_chunk(
                "./.github/CODEOWNERS", ["./.github"]
            )
        )
        self.assertFalse(
            loop_engine.path_is_in_frozen_chunk(
                "claude/README.md", [".claude"]
            )
        )

    def test_progress_chunk_requires_explicit_manifest_authorization(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            spec["issues"][0]["chunks"][0]["closure"] = "progress"
            import yaml

            spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError):
                loop_engine.load_spec(spec_path, root)

            spec["closure"]["allow_progress_pr"] = True
            spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
            loaded = loop_engine.load_spec(spec_path, root)
            self.assertEqual(loaded["issues"][0]["chunks"][0]["closure"], "progress")

    def test_progress_pr_link_cannot_close_an_issue(self) -> None:
        loop_engine.validate_pr_body_closure("Refs #554\n", 554, "progress")
        loop_engine.validate_pr_body_closure("See #554\n", 554, "progress")
        loop_engine.validate_pr_body_closure("Closes #554\n", 554, "complete")
        with self.assertRaises(loop_engine.LoopError):
            loop_engine.validate_pr_body_closure("Closes #554\n", 554, "progress")
        with self.assertRaises(loop_engine.LoopError):
            loop_engine.validate_pr_body_closure("Refs #554\nCloses #522\n", 554, "progress")
        with self.assertRaises(loop_engine.LoopError):
            loop_engine.validate_pr_body_closure("Refs #554\n", 554, "complete")

    def test_reviewed_commit_accepts_short_or_full_head_revision(self) -> None:
        head = "a" * 40
        with mock.patch.object(loop_engine, "git", return_value=head):
            self.assertTrue(loop_engine.reviewed_commit_matches_head(Path("."), "a" * 7, head))
            self.assertTrue(loop_engine.reviewed_commit_matches_head(Path("."), head, head))
        with mock.patch.object(loop_engine, "git", return_value=""):
            self.assertFalse(loop_engine.reviewed_commit_matches_head(Path("."), "a" * 7, head))
        self.assertFalse(loop_engine.reviewed_commit_matches_head(Path("."), "b" * 7, head))
        self.assertFalse(loop_engine.reviewed_commit_matches_head(Path("."), "a" * 7, "a" * 39))

    def test_predecessor_manifest_requires_complete_distinct_bindings(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            binding = predecessor_binding()
            spec["predecessor_prs"] = [binding, dict(binding)]
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.load_spec(spec_path, root)
            self.assertIn("must not repeat", str(caught.exception))

            spec["predecessor_prs"] = [binding]
            spec["predecessor_prs"][0]["reviewed_head"] = "a" * 7
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.load_spec(spec_path, root)
            self.assertIn("reviewed_head", str(caught.exception))

            spec["predecessor_prs"][0] = predecessor_binding()
            spec["predecessor_attestation"] = {"emit": True}
            spec["mutations"]["comment_issue"] = False
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.load_spec(spec_path, root)
            self.assertIn("comment_issue", str(caught.exception))

    def test_attested_squash_predecessor_requires_exact_metadata_and_both_ancestors(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            binding = predecessor_binding()
            spec["predecessor_prs"] = [binding]
            expected = loop_engine.predecessor_attestation_from_binding(binding)
            comment = {
                "author": {"login": spec["actor"]},
                "body": loop_engine.predecessor_attestation_body(expected),
            }
            pr = predecessor_pr(binding, [comment])

            def git_heads(_root: Path, *args: str, **_kwargs: object) -> str:
                if args == ("rev-parse", "--verify", spec["base_ref"]):
                    return "e" * 40
                if args == ("rev-parse", "HEAD"):
                    return "f" * 40
                raise AssertionError(args)

            with mock.patch.object(loop_engine, "git", side_effect=git_heads), mock.patch.object(
                loop_engine, "gh_json", return_value=pr
            ), mock.patch.object(
                loop_engine,
                "run_command",
                return_value=subprocess.CompletedProcess(["git"], 0, "", ""),
            ):
                proofs = loop_engine.require_predecessor_prs(root, spec)
            self.assertEqual(proofs[0]["reviewed_head"], binding["reviewed_head"])
            self.assertEqual(proofs[0]["merge_commit"], binding["merge_commit"])
            self.assertNotEqual(binding["reviewed_head"], binding["merge_commit"])

            cases = [
                ("wrong base", {"baseRefName": "release"}, "targets"),
                ("wrong branch", {"headRefName": "agent/other"}, "source_branch"),
                ("closing body", {"body": "Closes #928\n"}, "pinned closure"),
                ("wrong head", {"headRefOid": "9" * 40}, "reviewed_head"),
                ("wrong merge", {"mergeCommit": {"oid": "8" * 40}}, "merge_commit"),
                ("missing marker", {"comments": []}, "attestation"),
                ("unmerged", {"state": "OPEN", "mergedAt": None}, "not merged"),
            ]
            for label, change, message in cases:
                with self.subTest(label=label):
                    candidate = dict(pr)
                    candidate.update(change)
                    with mock.patch.object(loop_engine, "git", side_effect=git_heads), mock.patch.object(
                        loop_engine, "gh_json", return_value=candidate
                    ), mock.patch.object(
                        loop_engine,
                        "run_command",
                        return_value=subprocess.CompletedProcess(["git"], 0, "", ""),
                    ), self.assertRaises(loop_engine.LoopError) as caught:
                        loop_engine.require_predecessor_prs(root, spec)
                    self.assertIn(message, str(caught.exception))

            with mock.patch.object(loop_engine, "git", side_effect=git_heads), mock.patch.object(
                loop_engine, "gh_json", return_value=pr
            ), mock.patch.object(
                loop_engine,
                "run_command",
                side_effect=[
                    subprocess.CompletedProcess(["git"], 0, "", ""),
                    subprocess.CompletedProcess(["git"], 1, "", ""),
                ],
            ), self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.require_predecessor_prs(root, spec)
            self.assertIn("current HEAD", str(caught.exception))

    def test_preflight_and_ledger_init_recheck_predecessor_evidence(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            spec["enabled"] = True
            spec["predecessor_prs"] = [predecessor_binding()]
            spec_path.write_text(json.dumps(spec), encoding="utf-8")

            def git_for_preflight(_root: Path, *args: str, **_kwargs: object) -> str:
                values = {
                    ("status", "--porcelain", "--untracked-files=all"): "",
                    ("branch", "--show-current"): "agent/test-issue",
                    ("rev-parse", "HEAD"): "a" * 40,
                    ("rev-parse", "--verify", spec["base_ref"]): "a" * 40,
                    ("remote", "get-url", spec["remote"]): "https://github.com/example/repository.git",
                }
                return values[args]

            with mock.patch.object(loop_engine, "git", side_effect=git_for_preflight), mock.patch.object(
                loop_engine, "gh_authenticated", return_value=spec["actor"]
            ), mock.patch.object(loop_engine, "existing_prs", return_value=[]), mock.patch.object(
                loop_engine, "gh_json", return_value={"contexts": ["ci"]}
            ), mock.patch.object(
                loop_engine, "issue_state", return_value={"state": "OPEN", "labels": [], "blockedBy": []}
            ), mock.patch.object(
                loop_engine,
                "require_predecessor_prs",
                side_effect=loop_engine.LoopError("missing predecessor attestation"),
            ), contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertNotEqual(loop_engine.preflight(root, spec_path), 0)
            self.assertIn("missing predecessor attestation", output.getvalue())

            with mock.patch.object(
                loop_engine,
                "require_predecessor_prs",
                side_effect=loop_engine.LoopError("missing predecessor attestation"),
            ), contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertNotEqual(loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None), 0)
            self.assertIn("missing predecessor attestation", output.getvalue())

    def test_actions_recheck_predecessors_and_source_attestation_requires_a_passing_ledger(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            spec["enabled"] = True
            for mutation in ("create_pr", "approve_pr", "merge_pr"):
                spec["mutations"][mutation] = True
            failure = loop_engine.LoopError("predecessor branch was rebased away")
            calls = [
                lambda: loop_engine.action_create_pr(
                    root, spec, 1, root / "missing-ledger", "title", "missing-body", False, True
                ),
                lambda: loop_engine.action_approve(
                    root, spec, 12, root / "missing-ledger", "body", True
                ),
                lambda: loop_engine.action_merge(
                    root, spec, 12, root / "missing-ledger", None, False, False, None, True
                ),
            ]
            for action in calls:
                with mock.patch.object(loop_engine, "require_predecessor_prs", side_effect=failure) as check:
                    with self.assertRaises(loop_engine.LoopError) as caught:
                        action()
                    self.assertIn("rebased", str(caught.exception))
                    check.assert_called_once_with(root, spec)

            blocked = {"status": "blocked"}
            with self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.predecessor_attestation_from_state(blocked, "a" * 40)
            self.assertIn("passing", str(caught.exception))

    def test_source_attestation_binds_the_frozen_issue_branch_and_progress_body(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            spec["enabled"] = True
            spec["mutations"]["comment_issue"] = True
            spec["mutations"]["merge_pr"] = True
            spec["predecessor_attestation"] = {"emit": True}
            state = passing_ledger_state(root, spec, "progress")
            state["rounds"][0]["adjudication"]["verdict"] = "pass_with_lift"
            pr = {
                "state": "OPEN",
                "isDraft": False,
                "baseRefName": "main",
                "headRefName": "agent/test-issue",
                "headRefOid": "a" * 40,
                "body": "Refs #1\n",
                "files": [{"path": "scripts/loop_engine.py"}],
                "comments": [],
            }
            with mock.patch.object(loop_engine, "load_state", return_value=state), mock.patch.object(
                loop_engine, "gh_json", return_value=pr
            ), mock.patch.object(
                loop_engine, "reviewed_commit_matches_head", return_value=True
            ), mock.patch.object(loop_engine, "run_command") as command:
                self.assertEqual(
                    loop_engine.action_attest_pr(root, spec, 1, 51, root / "ledger.json", False), 0
                )
            written = command.call_args.args[1]
            self.assertEqual(written[:4], ["gh", "pr", "comment", "51"])
            marker = loop_engine.parse_predecessor_attestation(written[-1])
            self.assertIsNotNone(marker)
            self.assertEqual(marker["issue_number"], 1)
            self.assertEqual(marker["source_branch"], "agent/test-issue")
            self.assertEqual(marker["closure"], "progress")

            blocked_state = dict(state)
            blocked_state["status"] = "blocked"
            with mock.patch.object(loop_engine, "load_state", return_value=blocked_state), self.assertRaises(
                loop_engine.LoopError
            ) as caught:
                loop_engine.action_attest_pr(root, spec, 1, 51, root / "ledger.json", True)
            self.assertIn("passing review ledger", str(caught.exception))

            pr["comments"] = [{"author": {"login": spec["actor"]}, "body": written[-1]}]
            with mock.patch.object(loop_engine, "load_state", return_value=state), mock.patch.object(
                loop_engine, "gh_json", return_value=pr
            ), mock.patch.object(
                loop_engine, "reviewed_commit_matches_head", return_value=True
            ), mock.patch.object(loop_engine, "check_required_checks"), mock.patch.object(
                loop_engine, "run_command"
            ):
                self.assertEqual(
                    loop_engine.action_merge(
                        root, spec, 51, root / "ledger.json", None, False, False, None, True
                    ),
                    0,
                )

            for label, change, message in (
                ("wrong branch", {"headRefName": "agent/other"}, "frozen issue branch"),
                ("closing body", {"body": "Closes #1\n"}, "frozen 'progress' closure"),
            ):
                with self.subTest(label=label):
                    candidate = dict(pr)
                    candidate.update(change)
                    with mock.patch.object(loop_engine, "load_state", return_value=state), mock.patch.object(
                        loop_engine, "gh_json", return_value=candidate
                    ), mock.patch.object(
                        loop_engine, "reviewed_commit_matches_head", return_value=True
                    ), self.assertRaises(loop_engine.LoopError) as caught:
                        loop_engine.action_attest_pr(
                            root, spec, 1, 51, root / "ledger.json", True
                        )
                    self.assertIn(message, str(caught.exception))

            missing_marker = dict(pr)
            missing_marker["comments"] = []
            with mock.patch.object(loop_engine, "load_state", return_value=state), mock.patch.object(
                loop_engine, "gh_json", return_value=missing_marker
            ), mock.patch.object(
                loop_engine, "reviewed_commit_matches_head", return_value=True
            ), mock.patch.object(loop_engine, "check_required_checks"), self.assertRaises(
                loop_engine.LoopError
            ) as caught:
                loop_engine.action_merge(
                    root, spec, 51, root / "ledger.json", None, False, False, None, True
                )
            self.assertIn("attestation", str(caught.exception))

    def test_remote_pr_head_is_rechecked_against_predecessor_merges(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            spec["enabled"] = True
            spec["mutations"]["approve_pr"] = True
            state = passing_ledger_state(root, spec)
            proof = {
                "number": 41,
                "merge_commit": "d" * 40,
            }
            pr = {
                "state": "OPEN",
                "isDraft": False,
                "baseRefName": "main",
                "headRefName": "agent/test-issue",
                "headRefOid": "f" * 40,
                "body": "Closes #1\n",
                "files": [{"path": "scripts/loop_engine.py"}],
            }
            with mock.patch.object(loop_engine, "require_predecessor_prs", return_value=[proof]), mock.patch.object(
                loop_engine, "load_state", return_value=state
            ), mock.patch.object(loop_engine, "gh_json", return_value=pr), mock.patch.object(
                loop_engine,
                "run_command",
                return_value=subprocess.CompletedProcess(["git"], 1, "", ""),
            ), self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.action_approve(root, spec, 52, root / "ledger.json", "body", True)
            self.assertIn("PR head", str(caught.exception))

    def test_progress_dependency_cannot_unlock_downstream_chunk(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            spec["mode"] = "stack"
            spec["limits"]["min_issues"] = 2
            spec["limits"]["max_issues"] = 2
            spec["closure"]["allow_progress_pr"] = True
            spec["issues"][0]["chunks"][0]["closure"] = "progress"
            spec["issues"].append(
                {
                    "number": 2,
                    "slug": "downstream-issue",
                    "depends_on": [1],
                    "chunks": [
                        {
                            "id": "downstream-chunk",
                            "scope": "Wait for the upstream issue.",
                            "requirements": ["Frozen scope"],
                            "files": ["scripts/loop_engine.py"],
                            "acceptance": ["The upstream issue is complete."],
                        }
                    ],
                }
            )
            import yaml

            spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
            loaded = loop_engine.load_spec(spec_path, root)
            dependency_path = loop_engine.state_path(root, loaded, None, "test-chunk")
            loop_engine.write_json(
                dependency_path,
                {
                    "schema": f"{loop_engine.RUN_SCHEMA}/ledger",
                    "spec_digest": loop_engine.digest(loaded),
                    "openspec_digest": loop_engine.openspec_digest(root, loaded),
                    "chunk": {"closure": "progress"},
                    "status": "passed",
                },
            )
            with mock.patch.object(loop_engine, "issue_state") as issue_state:
                with contextlib.redirect_stdout(io.StringIO()) as output:
                    result = loop_engine.ledger_init(root, spec_path, 2, "downstream-chunk", None)
            issue_state.assert_not_called()
            self.assertNotEqual(result, 0)
            self.assertIn("progress ledger cannot unlock", output.getvalue())

    def test_open_upstream_issue_cannot_unlock_complete_dependency(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            spec["mode"] = "stack"
            spec["limits"]["min_issues"] = 2
            spec["limits"]["max_issues"] = 2
            spec["issues"].append(
                {
                    "number": 2,
                    "slug": "downstream-issue",
                    "depends_on": [1],
                    "chunks": [
                        {
                            "id": "downstream-chunk",
                            "scope": "Wait for the upstream issue.",
                            "requirements": ["Frozen scope"],
                            "files": ["scripts/loop_engine.py"],
                            "acceptance": ["The upstream issue is complete."],
                        }
                    ],
                }
            )
            import yaml

            spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
            loaded = loop_engine.load_spec(spec_path, root)
            dependency_path = loop_engine.state_path(root, loaded, None, "test-chunk")
            loop_engine.write_json(
                dependency_path,
                {
                    "schema": f"{loop_engine.RUN_SCHEMA}/ledger",
                    "spec_digest": loop_engine.digest(loaded),
                    "openspec_digest": loop_engine.openspec_digest(root, loaded),
                    "chunk": {"closure": "complete"},
                    "status": "passed",
                },
            )
            with mock.patch.object(loop_engine, "issue_state", return_value={"state": "open"}) as issue_state:
                with contextlib.redirect_stdout(io.StringIO()) as output:
                    result = loop_engine.ledger_init(root, spec_path, 2, "downstream-chunk", None)
            issue_state.assert_called_once_with(root, spec["repository"], 1)
            self.assertNotEqual(result, 0)
            self.assertIn("remaining open", output.getvalue())

    def test_ledger_requires_all_reviewers_and_stops_after_five_rounds(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            self.assertEqual(loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None), 0)
            state_path = root / ".loop-runs" / "test-chunk.json"
            commit_a = "a" * 40
            commit_b = "b" * 40
            commit_c = "c" * 40
            commit_d = "d" * 40
            commit_e = "e" * 40
            commit_f = "f" * 40

            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(
                    loop_engine.ledger_record_review(
                        state_path,
                        REVIEWERS[0],
                        commit_a,
                        "pass",
                        None,
                        reviewer_output(root, REVIEWERS[0], "pass"),
                    ),
                    0,
                )
                self.assertNotEqual(
                    loop_engine.ledger_record_review(state_path, REVIEWERS[1], commit_b, "pass", None),
                    0,
                )
                for reviewer in REVIEWERS[1:]:
                    self.assertEqual(
                        loop_engine.ledger_record_review(
                            state_path,
                            reviewer,
                            commit_a,
                            "needs_changes",
                            "fix",
                            reviewer_output(root, reviewer, "needs_changes"),
                        ),
                        0,
                    )
                self.assertEqual(loop_engine.ledger_adjudicate(state_path, "needs_changes", "round one"), 0)

                for round_number, commit in enumerate(
                    (commit_b, commit_c, commit_d, commit_e), start=2
                ):
                    for reviewer in REVIEWERS:
                        self.assertEqual(
                            loop_engine.ledger_record_review(
                                state_path,
                                reviewer,
                                commit,
                                "needs_changes",
                                "fix",
                                reviewer_output(root, reviewer, "needs_changes"),
                            ),
                            0,
                        )
                    self.assertEqual(
                        loop_engine.ledger_adjudicate(
                            state_path, "needs_changes", f"round {round_number}"
                        ),
                        0,
                    )

                self.assertNotEqual(
                    loop_engine.ledger_record_review(
                        state_path, REVIEWERS[0], commit_f, "pass", None
                    ),
                    0,
                )

            state = json.loads(state_path.read_text(encoding="utf-8"))
            self.assertEqual(state["status"], "blocked")
            self.assertEqual(len(state["rounds"]), 5)
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
                    self.assertEqual(
                        loop_engine.ledger_record_review(
                            state_path,
                            reviewer,
                            commit,
                            "pass",
                            None,
                            reviewer_output(root, reviewer, "pass"),
                        ),
                        0,
                    )
                self.assertEqual(loop_engine.ledger_adjudicate(state_path, "pass", "all clear"), 0)
                self.assertNotEqual(loop_engine.ledger_record_review(state_path, REVIEWERS[0], "f" * 40, "pass", None), 0)
            state = json.loads(state_path.read_text(encoding="utf-8"))
            self.assertEqual(state["status"], "passed")


    def test_adjudication_refuses_uncaptured_reviewer_output(self) -> None:
        """A round whose reviewers returned no readable message cannot pass."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None)
            state_path = root / ".loop-runs" / "test-chunk.json"
            commit = "a" * 40
            with contextlib.redirect_stdout(io.StringIO()):
                for reviewer in REVIEWERS:
                    self.assertEqual(
                        loop_engine.ledger_record_review(
                            state_path, reviewer, commit, "pass", "looks fine"
                        ),
                        0,
                    )
                # every reviewer submitted, but none of them left captured output
                self.assertNotEqual(
                    loop_engine.ledger_adjudicate(state_path, "pass", "all clear"), 0
                )
                self.assertNotEqual(
                    loop_engine.ledger_adjudicate(state_path, "needs_changes", "again"), 0
                )
                # stopping is always permitted: a void round may be recorded blocked
                self.assertEqual(
                    loop_engine.ledger_adjudicate(state_path, "blocked", "void round"), 0
                )
            state = json.loads(state_path.read_text(encoding="utf-8"))
            self.assertEqual(state["status"], "blocked")

    def test_captured_output_is_stored_with_its_digest(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None)
            state_path = root / ".loop-runs" / "test-chunk.json"
            commit = "a" * 40
            path = reviewer_output(root, REVIEWERS[0], "pass")
            # the controller digests the decoded text, not raw bytes, so the
            # digest is stable across CRLF and LF checkouts of the same review
            expected = hashlib.sha256(
                path.read_text(encoding="utf-8").encode("utf-8")
            ).hexdigest()
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(
                    loop_engine.ledger_record_review(
                        state_path, REVIEWERS[0], commit, "pass", None, path
                    ),
                    0,
                )
            row = json.loads(state_path.read_text(encoding="utf-8"))["rounds"][0]["reviews"][0]
            self.assertEqual(row["finding_digest"], expected)
            self.assertIn("PASS", row["finding_text"])

    def test_empty_reviewer_output_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None)
            state_path = root / ".loop-runs" / "test-chunk.json"
            empty = root / "empty.md"
            empty.write_text("   \n\n", encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertNotEqual(
                    loop_engine.ledger_record_review(
                        state_path, REVIEWERS[0], "a" * 40, "pass", None, empty
                    ),
                    0,
                )

    def test_verdict_must_match_the_reviewer_text(self) -> None:
        """The orchestrator cannot record pass over a reviewer that said otherwise."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None)
            state_path = root / ".loop-runs" / "test-chunk.json"
            dissent = root / "dissent.md"
            dissent.write_text(
                "The root owns two carriers.\nClose: NEEDS_CHANGES, 2 findings.\n",
                encoding="utf-8",
            )
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertNotEqual(
                    loop_engine.ledger_record_review(
                        state_path, REVIEWERS[0], "a" * 40, "pass", None, dissent
                    ),
                    0,
                )
                self.assertEqual(
                    loop_engine.ledger_record_review(
                        state_path, REVIEWERS[0], "a" * 40, "needs_changes", None, dissent
                    ),
                    0,
                )

    def test_pass_with_lift_requires_a_target(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None)
            state_path = root / ".loop-runs" / "test-chunk.json"
            out = reviewer_output(root, REVIEWERS[0], "pass_with_lift")
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertNotEqual(
                    loop_engine.ledger_record_review(
                        state_path, REVIEWERS[0], "a" * 40, "pass_with_lift", None, out, None
                    ),
                    0,
                )
                # and a target is meaningless on any other verdict
                self.assertNotEqual(
                    loop_engine.ledger_record_review(
                        state_path,
                        REVIEWERS[0],
                        "a" * 40,
                        "pass",
                        None,
                        reviewer_output(root, REVIEWERS[0], "pass"),
                        "DerivedAlgGeo/Foo",
                    ),
                    0,
                )

    def test_lift_must_reach_the_backlog_before_the_chunk_passes(self) -> None:
        """A lift recorded only in the gitignored ledger dies with the run."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            write_backlog(root)  # exists, but carries no rows yet
            loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None)
            state_path = root / ".loop-runs" / "test-chunk.json"
            commit = "a" * 40
            target = "DerivedAlgGeo/CategoryTheory/Triangulated/Basic.lean"
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(
                    loop_engine.ledger_record_review(
                        state_path,
                        REVIEWERS[0],
                        commit,
                        "pass_with_lift",
                        None,
                        reviewer_output(root, REVIEWERS[0], "pass_with_lift"),
                        target,
                    ),
                    0,
                )
                for reviewer in REVIEWERS[1:]:
                    self.assertEqual(
                        loop_engine.ledger_record_review(
                            state_path,
                            reviewer,
                            commit,
                            "pass",
                            None,
                            reviewer_output(root, reviewer, "pass"),
                        ),
                        0,
                    )
                # a round carrying a lift may not be adjudicated a plain pass
                self.assertNotEqual(
                    loop_engine.ledger_adjudicate(state_path, "pass", "clean"), 0
                )
                # and pass_with_lift is refused while the backlog is silent
                self.assertNotEqual(
                    loop_engine.ledger_adjudicate(state_path, "pass_with_lift", "lifted"), 0
                )
                write_backlog(root, target)
                self.assertEqual(
                    loop_engine.ledger_adjudicate(state_path, "pass_with_lift", "lifted"), 0
                )
            state = json.loads(state_path.read_text(encoding="utf-8"))
            self.assertEqual(state["status"], "passed")
            # the lift cost the chunk nothing: still one round
            self.assertEqual(len(state["rounds"]), 1)
            self.assertEqual(state["rounds"][0]["reviews"][0]["lift_target"], target)

    def test_manifest_missing_the_style_reviewer_fails_validation(self) -> None:
        """The spec delta requires four reviewers; the code used to enforce three."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            spec["review"]["reviewers"] = [r for r in REVIEWERS if r != "mathlib-reviewer"]
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.load_spec(spec_path, root)
            self.assertIn("mathlib-reviewer", str(caught.exception))


    def test_lift_target_opens_only_after_a_reviewer_asks(self) -> None:
        """Declaring a lift target is standing permission, not an open door."""
        state = {
            "chunk": {
                "files": ["DerivedAlgGeo/Leaf"],
                "lift_targets": ["DerivedAlgGeo/CategoryTheory/Triangulated"],
            },
            "rounds": [],
        }
        self.assertEqual(loop_engine.authorized_lift_targets(state), [])
        self.assertEqual(loop_engine.chunk_allowed_paths(state), ["DerivedAlgGeo/Leaf"])
        self.assertFalse(
            loop_engine.path_is_in_frozen_chunk(
                "DerivedAlgGeo/CategoryTheory/Triangulated/Basic.lean",
                loop_engine.chunk_allowed_paths(state),
            )
        )

        # a reviewer names a path under the declared prefix
        state["rounds"] = [
            {
                "reviews": [
                    {
                        "reviewer": REVIEWERS[2],
                        "verdict": "pass_with_lift",
                        "lift_target": "DerivedAlgGeo/CategoryTheory/Triangulated/Basic.lean",
                    }
                ]
            }
        ]
        self.assertEqual(
            loop_engine.authorized_lift_targets(state),
            ["DerivedAlgGeo/CategoryTheory/Triangulated"],
        )
        self.assertTrue(
            loop_engine.path_is_in_frozen_chunk(
                "DerivedAlgGeo/CategoryTheory/Triangulated/Basic.lean",
                loop_engine.chunk_allowed_paths(state),
            )
        )
        # an unrelated prefix stays shut
        self.assertFalse(
            loop_engine.path_is_in_frozen_chunk(
                "DerivedAlgGeo/Elsewhere/Other.lean",
                loop_engine.chunk_allowed_paths(state),
            )
        )

    def test_a_lift_target_may_not_duplicate_a_frozen_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            chunk = spec["issues"][0]["chunks"][0]
            chunk["lift_targets"] = list(chunk["files"])[:1]
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.load_spec(spec_path, root)
            self.assertIn("lift_targets", str(caught.exception))

    def test_renaming_a_ledger_does_not_start_a_fresh_review(self) -> None:
        """The state dir is gitignored; identity is (spec_id, chunk_id), not filename."""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(
                    loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None), 0
                )
                state_path = root / ".loop-runs" / "test-chunk.json"
                self.assertTrue(state_path.is_file())
                state_path.rename(state_path.with_name("test-chunk.bak.json"))
                # the chunk looks unstarted by filename, but its ledger still exists
                self.assertNotEqual(
                    loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None), 0
                )

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
