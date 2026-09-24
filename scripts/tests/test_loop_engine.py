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
    chunk = issue["chunks"][0]
    return {
        "schema": f"{loop_engine.RUN_SCHEMA}/ledger",
        "spec_id": spec["id"],
        "spec_digest": loop_engine.digest(spec),
        "openspec_digest": loop_engine.openspec_digest(root, spec),
        "repository": spec["repository"],
        "remote": spec["remote"],
        "base_branch": spec["base_branch"],
        "repo_root": str(root.resolve()),
        "issue": {"number": issue["number"], "slug": issue["slug"]},
        "chunk": {
            "id": chunk["id"],
            "scope": chunk["scope"],
            "files": chunk["files"],
            "lift_targets": chunk.get("lift_targets", []),
            "requirements": chunk["requirements"],
            "acceptance": chunk["acceptance"],
            "closure": closure,
        },
        "max_review_rounds": spec["limits"]["max_review_rounds_per_chunk"],
        "reviewers": spec["review"]["reviewers"],
        "status": "passed",
        "ci_failure_repairs": [],
        "rounds": [
            {
                "commit": "a" * 40,
                "adjudication": {"verdict": "pass"},
            }
        ],
    }


def persist_test_ledger(root: Path, state: dict) -> Path:
    path = root / ".loop-runs" / f"{state['chunk']['id']}.json"
    path.parent.mkdir(parents=True, exist_ok=True)
    loop_engine.atomic_json(path, state)
    return path


class LoopEngineTests(unittest.TestCase):
    def setUp(self) -> None:
        # These tests model a legacy manifest the owner reviewed through a
        # planning PR, so its own grants and policies are the authority.
        # AuthorityTests and BranchManifestPolicyTests cover branch manifests.
        for name, value in (
            ("owner_reviewed_legacy_manifest", True),
            ("standing_authority", {}),
            ("require_legacy_issue_open", None),
        ):
            patcher = mock.patch.object(loop_engine, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)

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
            loaded = loop_engine.load_spec(spec_path, root, verify_owner_review=False)
            self.assertEqual(loaded["openspec"]["change"], "pilot-change")
            self.assertEqual(loop_engine.digest(loaded), loop_engine.digest(spec))

    def test_epic_opt_in_is_explicit_and_selected_only(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            spec["eligibility"] = {"allow_epic_issues": [1]}
            import yaml

            spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
            self.assertEqual(
                loop_engine.load_spec(spec_path, root, verify_owner_review=False)["eligibility"], spec["eligibility"]
            )
            spec["eligibility"] = {"allow_epic_issues": [2]}
            spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError):
                loop_engine.load_spec(spec_path, root, verify_owner_review=False)

    def test_roadmap_gate_is_scoped_to_manifest_base(self) -> None:
        self.assertEqual(
            loop_engine.roadmap_gate_args("agent/sf11-base"),
            [
                sys.executable,
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
                loop_engine.load_spec(spec_path, root, verify_owner_review=False)

            spec["closure"]["allow_progress_pr"] = True
            spec_path.write_text(yaml.safe_dump(spec, sort_keys=False), encoding="utf-8")
            loaded = loop_engine.load_spec(spec_path, root, verify_owner_review=False)
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
                loop_engine.load_spec(spec_path, root, verify_owner_review=False)
            self.assertIn("must not repeat", str(caught.exception))

            spec["predecessor_prs"] = [binding]
            spec["predecessor_prs"][0]["reviewed_head"] = "a" * 7
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.load_spec(spec_path, root, verify_owner_review=False)
            self.assertIn("reviewed_head", str(caught.exception))

            spec["predecessor_prs"][0] = predecessor_binding()
            spec["predecessor_attestation"] = {"emit": True}
            spec["mutations"]["comment_issue"] = False
            spec_path.write_text(json.dumps(spec), encoding="utf-8")
            with self.assertRaises(loop_engine.LoopError) as caught:
                loop_engine.load_spec(spec_path, root, verify_owner_review=False)
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
            spec["closure"]["allow_progress_pr"] = True
            spec["issues"][0]["chunks"][0]["closure"] = "progress"
            spec["predecessor_attestation"] = {"emit": True}
            state = passing_ledger_state(root, spec, "progress")
            ledger_path = persist_test_ledger(root, state)
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
                    loop_engine.action_attest_pr(root, spec, 1, 51, ledger_path, False), 0
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
                loop_engine.action_attest_pr(root, spec, 1, 51, ledger_path, True)
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
                        root, spec, 51, ledger_path, None, False, False, None, True
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
                            root, spec, 1, 51, ledger_path, True
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
                    root, spec, 51, ledger_path, None, False, False, None, True
                )
            self.assertIn("attestation", str(caught.exception))

    def test_remote_pr_head_is_rechecked_against_predecessor_merges(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            spec["enabled"] = True
            spec["mutations"]["approve_pr"] = True
            state = passing_ledger_state(root, spec)
            ledger_path = persist_test_ledger(root, state)
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
                loop_engine.action_approve(root, spec, 52, ledger_path, "body", True)
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
            loaded = loop_engine.load_spec(spec_path, root, verify_owner_review=False)
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
            loaded = loop_engine.load_spec(spec_path, root, verify_owner_review=False)
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
                loop_engine.load_spec(spec_path, root, verify_owner_review=False)
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
                loop_engine.load_spec(spec_path, root, verify_owner_review=False)
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

    def test_nested_ledger_identity_is_issue_slug_and_chunk_not_spec_id_or_filename(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(loop_engine.ledger_init(root, spec_path, 1, "test-chunk", None), 0)
            state_path = root / ".loop-runs" / "test-chunk.json"
            state = json.loads(state_path.read_text(encoding="utf-8"))
            state["spec_id"] = "a-different-run"
            nested = root / ".loop-runs" / "nested" / "renamed.json"
            loop_engine.atomic_json(nested, state)
            original = state_path.read_bytes()
            with contextlib.redirect_stdout(io.StringIO()) as output:
                result = loop_engine.ledger_init(
                    root, spec_path, 1, "test-chunk", ".loop-runs/another-directory"
                )
            self.assertNotEqual(result, 0)
            self.assertIn("already has a ledger", output.getvalue())
            self.assertEqual(state_path.read_bytes(), original)

    def test_missing_openspec_artifact_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, _ = make_spec(root)
            (root / "openspec" / "changes" / "pilot-change" / "design.md").unlink()
            with self.assertRaises(loop_engine.LoopError):
                loop_engine.load_spec(spec_path, root, verify_owner_review=False)

    def test_merge_command_is_bound_to_reviewed_head_and_safe_by_default(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            spec_path, spec = make_spec(root)
            loaded = loop_engine.load_spec(spec_path, root, verify_owner_review=False)
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

    def test_ready_marks_a_draft_only_after_the_panel_passes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            spec["enabled"] = True
            spec["mutations"]["ready_pr"] = True
            state = passing_ledger_state(root, spec)
            ledger_path = persist_test_ledger(root, state)
            pr = {
                "state": "OPEN",
                "isDraft": True,
                "headRefName": "agent/test-issue",
                "headRefOid": "a" * 40,
                "baseRefName": "main",
                "body": "Closes #1\n",
                "files": [{"path": "scripts/loop_engine.py"}],
            }
            with mock.patch.object(loop_engine, "load_state", return_value=state), mock.patch.object(
                loop_engine, "gh_json", return_value=pr
            ), contextlib.redirect_stdout(io.StringIO()) as output:
                self.assertEqual(loop_engine.action_ready(root, spec, 7, ledger_path, True), 0)
            self.assertIn("DRY-RUN gh pr ready 7", output.getvalue())

            state["status"] = "improve_required"
            with mock.patch.object(loop_engine, "load_state", return_value=state), mock.patch.object(
                loop_engine, "gh_json", return_value=pr
            ):
                with self.assertRaisesRegex(loop_engine.LoopError, "passing review ledger"):
                    loop_engine.action_ready(root, spec, 7, ledger_path, True)

    def test_follow_up_links_the_parent_and_inherits_its_milestone(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            spec["enabled"] = True
            spec["mutations"]["create_issue"] = True
            body = root / "follow-up.md"
            body.write_text("The reviewer found a stale dependency.\n", encoding="utf-8")
            with mock.patch.object(
                loop_engine, "gh_json", return_value={"milestone": {"title": "ROU1"}}
            ), mock.patch.object(loop_engine, "run_command") as write:
                write.return_value = subprocess.CompletedProcess([], 0, stdout="https://x/issues/9\n", stderr="")
                with contextlib.redirect_stdout(io.StringIO()):
                    self.assertEqual(
                        loop_engine.action_follow_up(root, spec, 1, "Refresh #1's blocker", str(body), ["loop"], False),
                        0,
                    )
            args = write.call_args.args[1]
            self.assertEqual(args[:3], ["gh", "issue", "create"])
            self.assertIn("Follow-up of #1", args[args.index("--body") + 1])
            self.assertEqual(args[args.index("--milestone") + 1], "ROU1")
            self.assertEqual(args[args.index("--label") + 1], "loop")
            with self.assertRaisesRegex(loop_engine.LoopError, "not included"):
                loop_engine.action_follow_up(root, spec, 99, "Unrelated", str(body), [], True)


def git_in(root: Path, *args: str) -> str:
    return subprocess.run(
        ["git", *args], cwd=root, check=True, capture_output=True, text=True
    ).stdout.strip()


def init_repo(root: Path) -> None:
    git_in(root, "init", "-q", "-b", "main")
    git_in(root, "config", "user.email", "loop-test@example.invalid")
    git_in(root, "config", "user.name", "Loop Test")
    git_in(root, "config", "commit.gpgsign", "false")
    # Ledgers and captured reviewer output are run-local, as in the repository.
    (root / ".gitignore").write_text(".loop-runs/\nreview-*.md\n", encoding="utf-8")


def commit_all(root: Path, message: str) -> str:
    git_in(root, "add", "-A")
    git_in(root, "commit", "-q", "--allow-empty", "-m", message)
    return git_in(root, "rev-parse", "HEAD")


def publish_base(root: Path) -> None:
    """Point the remote-tracking base at the current main, as a fetch would."""
    git_in(root, "update-ref", "refs/remotes/origin/main", "main")


def numbered_lines(count: int, changed: dict[int, str] | None = None) -> str:
    changed = changed or {}
    return "".join(f"{changed.get(line, f'line {line}')}\n" for line in range(1, count + 1))


class OpenSpecDigestTests(unittest.TestCase):
    def test_v3_ignores_checkbox_state_and_observation_logs_but_not_the_contract(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            change = root / "openspec" / "changes" / "pilot-change"
            (change / "agent-observations.md").write_text("# Observations\n", encoding="utf-8")
            spec["openspec"]["required_artifacts"].append("agent-observations.md")
            v1 = loop_engine.openspec_digest(root, spec, 1)
            v3 = loop_engine.openspec_digest(root, spec)
            legacy = {"openspec_digest": v1}
            current = {"openspec_digest": v3, "openspec_digest_version": 3}

            tasks = change / "tasks.md"
            tasks.write_text(tasks.read_text(encoding="utf-8").replace("- [ ] 1.1", "- [x] 1.1"), encoding="utf-8")
            with (change / "agent-observations.md").open("a", encoding="utf-8") as log:
                log.write("- OBS-001 the base moved during review\n")
            self.assertEqual(loop_engine.openspec_digest(root, spec), v3)
            self.assertTrue(loop_engine.ledger_openspec_matches(root, spec, current))
            # A ledger written before v2 keeps its byte-for-byte meaning.
            self.assertNotEqual(loop_engine.openspec_digest(root, spec, 1), v1)
            self.assertFalse(loop_engine.ledger_openspec_matches(root, spec, legacy))

            tasks.write_text(
                tasks.read_text(encoding="utf-8").replace("Verify the test", "Verify a different test"),
                encoding="utf-8",
            )
            self.assertNotEqual(loop_engine.openspec_digest(root, spec), v3)

    def test_v2_ledger_keeps_its_original_regex_and_newline_semantics(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            tasks = root / "openspec" / "changes" / "pilot-change" / "tasks.md"
            tasks.write_bytes(
                b"# Tasks\r\n\r\n- [ ] 1.1 Real task\r\n\r\n```md\r\n- [ ] 9.1 Example\r\n```\r\n"
            )
            old_v2 = {
                "openspec_digest": loop_engine.openspec_digest(root, spec, 2),
                "openspec_digest_version": 2,
            }

            # Historical v2 normalized CRLF via read_text() and also normalized
            # checkbox-shaped lines inside fenced examples.
            tasks.write_text(
                "# Tasks\n\n- [ ] 1.1 Real task\n\n```md\n- [x] 9.1 Example\n```\n",
                encoding="utf-8",
            )
            self.assertTrue(loop_engine.ledger_openspec_matches(root, spec, old_v2))

    def test_unknown_digest_versions_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            for version in (0, 4, -1, True, "3", 2.0):
                with self.subTest(version=version):
                    with self.assertRaisesRegex(loop_engine.LoopError, "unsupported OpenSpec digest version"):
                        loop_engine.openspec_digest(root, spec, version)
                    with self.assertRaisesRegex(loop_engine.LoopError, "unsupported OpenSpec digest version"):
                        loop_engine.ledger_digest_version({"openspec_digest_version": version})

    def test_a_single_issue_manifest_may_omit_openspec(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            del spec["openspec"]
            del spec["issues"][0]["chunks"][0]["requirements"]
            del spec["limits"]["min_issues"]
            spec["issues"][0]["chunks"][0]["files"] = ["DerivedAlgGeo/Example.lean"]
            loop_engine.validate_spec(spec)
            loop_engine.validate_openspec_artifacts(root, spec)
            self.assertEqual(loop_engine.openspec_digest(root, spec), loop_engine.digest([]))
            manifest = root / ".claude" / "loop-specs" / "one.yaml"
            self.assertEqual(loop_engine.plan_paths(root, manifest, spec), [".claude/loop-specs/one.yaml"])
            # A manifest outside the manifest directory is not plan, so it
            # cannot open an arbitrary tracked file to the PR.
            self.assertEqual(loop_engine.plan_paths(root, root / "registry" / "run.yaml", spec), [])

    def test_only_the_top_level_log_and_task_list_are_progress_records(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            change = root / "openspec" / "changes" / "pilot-change"
            (change / "specs" / "agent-observations.md").write_text(
                "### Requirement: Frozen scope\nThe system SHALL keep scope frozen.\n", encoding="utf-8"
            )
            spec["openspec"]["required_artifacts"].append("specs/agent-observations.md")
            before = loop_engine.openspec_digest(root, spec)
            (change / "specs" / "agent-observations.md").write_text(
                "### Requirement: Frozen scope\nThe system MAY widen scope.\n", encoding="utf-8"
            )
            self.assertNotEqual(loop_engine.openspec_digest(root, spec), before)

            spec["openspec"] = {"change": "pilot-change", "required_artifacts": ["proposal.md"]}
            with self.assertRaises(loop_engine.LoopError):
                loop_engine.validate_spec(spec)


class CommonMarkBoundaryTests(unittest.TestCase):
    def test_proposal_why_must_be_a_visible_root_level_atx_heading(self) -> None:
        for proposal in (
            "## Why\n",
            "## **Why**\n",
            "## *Why*\n",
            "## `Why`\n",
            "## Wh&#121;\n",
            "## [Why](https://example.test)\n",
            "# Proposal\n\n## Why ###\n",
            "`<widget>` is inline code\n## Why\n",
            "<widget>text</widget>\n## Why\n",
        ):
            with self.subTest(proposal=proposal):
                self.assertTrue(loop_engine.has_visible_why_heading(proposal))

        for proposal in (
            "## WhyNot\n",
            "## Why with extra text\n",
            "Why\n---\n",
            "```md\n## Why\n```\n",
            "> ## Why\n",
            "- ## Why\n",
            "## Why *not*\n",
            "## ![Why](https://example.test/image.png)\n",
            "## ![icon](https://example.test/image.png)Why\n",
            "## <span hidden>Why</span>\n",
            "## <b>Why</b>\n",
        ):
            with self.subTest(proposal=proposal):
                self.assertFalse(loop_engine.has_visible_why_heading(proposal))

    def test_task_checkbox_normalization_follows_commonmark_blocks(self) -> None:
        tasks = (
            "- [x] 1.1 Parent\n"
            "  - [X] 1.2 Nested\n"
            "* [x] Unnumbered star item\n"
            "+ [X] Unnumbered plus item\n"
        )
        self.assertEqual(
            loop_engine.normalize_task_checkboxes(tasks),
            "- [ ] 1.1 Parent\n"
            "  - [ ] 1.2 Nested\n"
            "* [ ] Unnumbered star item\n"
            "+ [ ] Unnumbered plus item\n",
        )

        code_and_non_tasks = (
            "```md\n- [x] Fenced example\n```\n"
            "-     [x] Indented code block\n"
            "- Parent paragraph\n\n  [x] Later paragraph\n"
            "> - [x] Blockquote item\n"
            "-[x] Malformed list marker\n"
            "- [ ]literal text\n"
            "- [x]literal text\n"
        )
        self.assertEqual(loop_engine.normalize_task_checkboxes(code_and_non_tasks), code_and_non_tasks)

        links_and_inline_html = "- [x](https://example.test)\n- [ ](https://example.test)\n- [x] Render <tag>\n"
        self.assertEqual(
            loop_engine.normalize_task_checkboxes(links_and_inline_html),
            "- [x](https://example.test)\n- [ ](https://example.test)\n- [ ] Render <tag>\n",
        )
        reference_link = "- [x] linked label\n\n[x]: https://example.test\n"
        self.assertEqual(loop_engine.normalize_task_checkboxes(reference_link), reference_link)
        soft_break = "- [x]\n  continued text\n"
        self.assertEqual(
            loop_engine.normalize_task_checkboxes(soft_break),
            "- [ ]\n  continued text\n",
        )

    def test_v3_digest_ignores_only_actual_list_checkbox_state(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            tasks = root / "openspec" / "changes" / "pilot-change" / "tasks.md"
            tasks.write_text(
                "# Tasks\n\n- [ ] 1.1 Real task\n\n```md\n- [ ] 9.1 Example\n```\n",
                encoding="utf-8",
            )
            initial = loop_engine.openspec_digest(root, spec)
            tasks.write_text(
                tasks.read_text(encoding="utf-8").replace("- [ ] 1.1", "- [x] 1.1"),
                encoding="utf-8",
            )
            self.assertEqual(loop_engine.openspec_digest(root, spec), initial)

            tasks.write_text(
                tasks.read_text(encoding="utf-8").replace("- [ ] 9.1", "- [x] 9.1"),
                encoding="utf-8",
            )
            self.assertNotEqual(loop_engine.openspec_digest(root, spec), initial)

            tasks.write_text("- [x](https://example.test)\n", encoding="utf-8")
            checked_link = loop_engine.openspec_digest(root, spec)
            tasks.write_text("- [ ](https://example.test)\n", encoding="utf-8")
            self.assertNotEqual(loop_engine.openspec_digest(root, spec), checked_link)

            tasks.write_text("# Tasks\n\n- [x]\n  continued description\n", encoding="utf-8")
            checked_soft_break = loop_engine.openspec_digest(root, spec)
            tasks.write_text("# Tasks\n\n- [ ]\n  continued description\n", encoding="utf-8")
            self.assertEqual(loop_engine.openspec_digest(root, spec), checked_soft_break)

            tasks.write_text("- [x] linked label\n\n[x]: https://example.test\n", encoding="utf-8")
            reference_link = loop_engine.openspec_digest(root, spec)
            tasks.write_text("- [ ] linked label\n\n[x]: https://example.test\n", encoding="utf-8")
            self.assertNotEqual(loop_engine.openspec_digest(root, spec), reference_link)

    def test_structural_proposal_validation_does_not_match_examples(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            _, spec = make_spec(root)
            proposal = root / "openspec" / "changes" / "pilot-change" / "proposal.md"
            proposal.write_text("The phrase ## Why appears in prose.\n", encoding="utf-8")
            with self.assertRaisesRegex(loop_engine.LoopError, "proposal must contain"):
                loop_engine.validate_openspec_artifacts(root, spec)

            proposal.write_text("```md\n## Why\n```\n", encoding="utf-8")
            with self.assertRaisesRegex(loop_engine.LoopError, "proposal must contain"):
                loop_engine.validate_openspec_artifacts(root, spec)


MANIFEST = ".claude/loop-specs/test-run.yaml"
REAL_READ_OWNER_FILE = loop_engine.read_owner_file


def branch_spec(root: Path, files: list[str], enabled: bool = True) -> tuple[Path, dict]:
    """make_spec as a branch-authored manifest: unprotected scope, at a manifest path."""
    run_path, spec = make_spec(root)
    run_path.unlink()
    spec["enabled"] = enabled
    spec["issues"][0]["chunks"][0]["files"] = files
    return write_manifest(root, spec), spec


def write_manifest(root: Path, spec: dict) -> Path:
    manifest = root / MANIFEST
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(json.dumps(spec), encoding="utf-8")
    return manifest


class AuthorityTests(unittest.TestCase):
    """Provider authority comes only from the owner's default branch on the provider."""

    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        _, self.spec = branch_spec(self.root, ["a.txt"])
        self.spec["mutations"] = {}
        # The provider's default branch, keyed by repository-relative path.
        self.default_branch: dict[str, str] = {}
        patcher = mock.patch.object(
            loop_engine, "read_owner_file", side_effect=lambda _root, _spec, path: self.default_branch.get(path)
        )
        patcher.start()
        self.addCleanup(patcher.stop)

    def grant(self, grants: dict[str, bool]) -> None:
        import yaml

        self.default_branch[loop_engine.STANDING_AUTHORITY_PATH] = yaml.safe_dump(
            {"schema": loop_engine.STANDING_AUTHORITY_SCHEMA, "mutations": grants}
        )

    def test_without_a_standing_file_a_branch_manifest_grants_nothing(self) -> None:
        self.spec["mutations"] = {"merge_pr": True, "push_branch": True}
        self.assertFalse(any(loop_engine.effective_mutations(self.root, self.spec).values()))
        with self.assertRaisesRegex(loop_engine.LoopError, "not authorized"):
            loop_engine.authorize_action(self.root, self.spec, "merge")

    def test_a_branch_manifest_narrows_standing_authority_and_cannot_widen_it(self) -> None:
        self.grant({"push_branch": True, "create_pr": True, "ready_pr": True, "merge_pr": True})
        self.spec["mutations"] = {"merge_pr": False, "comment_issue": True}
        effective = loop_engine.effective_mutations(self.root, self.spec)
        self.assertTrue(effective["push_branch"] and effective["create_pr"] and effective["ready_pr"])
        self.assertFalse(effective["merge_pr"])
        self.assertFalse(effective["comment_issue"])

    def test_local_refs_and_worktree_files_grant_nothing(self) -> None:
        # A standing file in the worktree, even committed and published to the
        # local remote-tracking ref, is not the provider's default branch.
        init_repo(self.root)
        path = self.root / loop_engine.STANDING_AUTHORITY_PATH
        path.write_text(
            f"schema: {loop_engine.STANDING_AUTHORITY_SCHEMA}\nmutations:\n  merge_pr: true\n", encoding="utf-8"
        )
        commit_all(self.root, "self-granted authority")
        publish_base(self.root)
        self.assertFalse(any(loop_engine.effective_mutations(self.root, self.spec).values()))

    def test_merging_a_branch_manifest_later_confers_nothing(self) -> None:
        import yaml

        # A work PR ships its own manifest; once merged it is on the default
        # branch, and that must not turn its self-written grants into authority.
        self.spec["mutations"] = {"approve_pr": True, "close_issue": True, "merge_pr": True}
        self.default_branch[MANIFEST] = yaml.safe_dump(self.spec, sort_keys=False)
        self.grant({"push_branch": True})
        effective = loop_engine.effective_mutations(self.root, self.spec)
        self.assertEqual({key for key, value in effective.items() if value}, {"push_branch"})

    def test_a_legacy_manifest_keeps_its_grants_and_obeys_the_kill_switch(self) -> None:
        self.spec["mutations"] = {"comment_issue": True, "merge_pr": True}
        reviewed_digest = loop_engine.digest(self.spec)
        with mock.patch.object(
            loop_engine, "LEGACY_REVIEWED_MANIFESTS", frozenset()
        ):
            self.default_branch["scripts/loop_engine.py"] = (
                f"LEGACY_REVIEWED_MANIFESTS = frozenset({{{reviewed_digest!r}}})\n"
            )
            effective = loop_engine.effective_mutations(self.root, self.spec)
            self.assertTrue(effective["comment_issue"] and effective["merge_pr"])
            self.assertFalse(effective["push_branch"])
            self.grant({"push_branch": True, "merge_pr": False})
            effective = loop_engine.effective_mutations(self.root, self.spec)
            self.assertTrue(effective["comment_issue"] and effective["push_branch"])
            self.assertFalse(effective["merge_pr"])

    def test_a_branch_local_legacy_digest_cannot_authorize_before_default_branch_merge(self) -> None:
        self.spec["mutations"] = {"push_branch": True, "merge_pr": True}
        with mock.patch.object(
            loop_engine, "LEGACY_REVIEWED_MANIFESTS", frozenset({loop_engine.digest(self.spec)})
        ):
            # A digest newly added on the current planning branch is not in the
            # controller fetched from the provider's default branch yet.
            self.default_branch["scripts/loop_engine.py"] = (
                "LEGACY_REVIEWED_MANIFESTS = frozenset(" + repr({"a" * 64}) + ")\n"
            )
            effective = loop_engine.effective_mutations(self.root, self.spec)
            self.assertFalse(any(effective.values()))
            self.default_branch["scripts/loop_engine.py"] = (
                f"LEGACY_REVIEWED_MANIFESTS = frozenset({{{loop_engine.digest(self.spec)!r}}})\n"
            )
            effective = loop_engine.effective_mutations(self.root, self.spec)
            self.assertTrue(effective["push_branch"] and effective["merge_pr"])

    def test_branch_local_digest_does_not_skip_protected_path_validation(self) -> None:
        self.spec["issues"][0]["chunks"][0]["files"] = ["scripts/loop_engine.py"]
        with mock.patch.object(
            loop_engine, "LEGACY_REVIEWED_MANIFESTS", frozenset({loop_engine.digest(self.spec)})
        ):
            self.default_branch["scripts/loop_engine.py"] = (
                "LEGACY_REVIEWED_MANIFESTS = frozenset(" + repr({"b" * 64}) + ")\n"
            )
            owner_reviewed = loop_engine.owner_reviewed_legacy_manifest(self.root, self.spec)
            self.assertFalse(owner_reviewed)
            with self.assertRaisesRegex(loop_engine.LoopError, "protected"):
                loop_engine.validate_spec(self.spec, owner_reviewed_legacy=owner_reviewed)

    def test_branch_local_digest_does_not_skip_ledger_publication_guards(self) -> None:
        spec_digest = loop_engine.digest(self.spec)
        state = {"spec_id": self.spec["id"], "spec_digest": spec_digest, "plan_paths": []}
        self.default_branch["scripts/loop_engine.py"] = (
            "LEGACY_REVIEWED_MANIFESTS = frozenset(" + repr({"b" * 64}) + ")\n"
        )
        with mock.patch.object(loop_engine, "LEGACY_REVIEWED_MANIFESTS", frozenset({spec_digest})):
            self.assertFalse(loop_engine.owner_reviewed_legacy_state(self.root, self.spec, state))
            with self.assertRaisesRegex(loop_engine.LoopError, "protected"):
                loop_engine.require_unprotected(self.root, self.spec, ["scripts/loop_engine.py"], state)
            clean_diff = subprocess.CompletedProcess([], 0, stdout="", stderr="")
            with mock.patch.object(loop_engine, "ensure_commit") as ensure_commit, mock.patch.object(
                loop_engine, "trusted_base_commit", return_value="main"
            ), mock.patch.object(loop_engine, "run_command", return_value=clean_diff) as run_command:
                loop_engine.require_published_head_has_no_links(self.root, self.spec, state, "a" * 40)
                ensure_commit.assert_called_once()
                run_command.assert_called_once()

    def test_branch_local_digest_does_not_authorize_force_push(self) -> None:
        self.spec["mutations"] = {"push_branch": True}
        self.spec["allow_force_push"] = True
        with mock.patch.object(
            loop_engine, "LEGACY_REVIEWED_MANIFESTS", frozenset({loop_engine.digest(self.spec)})
        ):
            self.default_branch["scripts/loop_engine.py"] = (
                "LEGACY_REVIEWED_MANIFESTS = frozenset(" + repr({"b" * 64}) + ")\n"
            )
            self.grant({"push_branch": True})
            with self.assertRaisesRegex(loop_engine.LoopError, "force-with-lease is not available"):
                loop_engine.action_push(self.root, self.spec, None, True, True)

    def test_branch_local_digest_does_not_authorize_administrator_merge(self) -> None:
        self.spec["mutations"] = {"merge_pr": True}
        with mock.patch.object(
            loop_engine, "LEGACY_REVIEWED_MANIFESTS", frozenset({loop_engine.digest(self.spec)})
        ):
            self.default_branch["scripts/loop_engine.py"] = (
                "LEGACY_REVIEWED_MANIFESTS = frozenset(" + repr({"b" * 64}) + ")\n"
            )
            self.grant({"merge_pr": True})
            with self.assertRaisesRegex(loop_engine.LoopError, "administrator merge is never available"):
                loop_engine.action_merge(
                    self.root, self.spec, 1, self.root / "ledger.json", None, False, True, None, True
                )

    def test_branch_local_digest_does_not_enable_non_pr_issue_closure(self) -> None:
        self.spec["mutations"] = {"close_issue": True}
        self.spec["closure"]["allow_non_pr"] = True
        with mock.patch.object(
            loop_engine, "LEGACY_REVIEWED_MANIFESTS", frozenset({loop_engine.digest(self.spec)})
        ):
            self.default_branch["scripts/loop_engine.py"] = (
                "LEGACY_REVIEWED_MANIFESTS = frozenset(" + repr({"b" * 64}) + ")\n"
            )
            self.grant({"close_issue": True})
            with self.assertRaisesRegex(loop_engine.LoopError, "verified merged PR"):
                loop_engine.action_close(self.root, self.spec, 1, None, None, True)

    def test_a_malformed_standing_file_fails_closed(self) -> None:
        self.default_branch[loop_engine.STANDING_AUTHORITY_PATH] = "mutations:\n  merge_pr: yes please\n"
        with self.assertRaises(loop_engine.LoopError):
            loop_engine.authorize_action(self.root, self.spec, "merge")

    def test_the_legacy_allowlist_matches_every_reviewed_manifest(self) -> None:
        import yaml

        specs = SCRIPT_DIR.parent / ".claude" / "loop-specs"
        digests = {
            loop_engine.digest(yaml.safe_load(path.read_text(encoding="utf-8"))) for path in specs.glob("*.yaml")
        }
        # Every allowlisted digest is a tracked manifest's exact content.
        self.assertEqual(loop_engine.LEGACY_REVIEWED_MANIFESTS - digests, set())

    def test_a_disabled_manifest_is_history_and_skips_branch_rules(self) -> None:
        historical = json.loads(json.dumps(self.spec))
        historical["enabled"] = False
        historical["issues"][0]["chunks"][0]["files"].append("scripts/loop_engine.py")
        loop_engine.validate_spec(historical)
        with self.assertRaisesRegex(loop_engine.LoopError, "disabled"):
            loop_engine.authorize_action(self.root, historical, "push")
        historical["enabled"] = True
        with self.assertRaisesRegex(loop_engine.LoopError, "protected"):
            loop_engine.validate_spec(historical)

    def test_a_legacy_grant_covers_only_open_issues(self) -> None:
        with mock.patch.object(loop_engine, "issue_state", return_value={"state": "CLOSED"}) as state:
            loop_engine.require_legacy_issue_open(self.root, self.spec, 1)
            state.assert_not_called()
            self.default_branch["scripts/loop_engine.py"] = (
                f"LEGACY_REVIEWED_MANIFESTS = frozenset({{{loop_engine.digest(self.spec)!r}}})\n"
            )
            with self.assertRaisesRegex(loop_engine.LoopError, "CLOSED"):
                loop_engine.require_legacy_issue_open(self.root, self.spec, 1)
            state.return_value = {"state": "OPEN"}
            loop_engine.require_legacy_issue_open(self.root, self.spec, 1)

    def test_an_unreadable_repository_is_not_an_absent_standing_file(self) -> None:
        not_found = subprocess.CompletedProcess([], 1, stdout="", stderr="gh: Not Found (HTTP 404)")
        with mock.patch.object(loop_engine, "run_command", return_value=not_found):
            with self.assertRaisesRegex(loop_engine.LoopError, "could not read"):
                REAL_READ_OWNER_FILE(self.root, self.spec, loop_engine.STANDING_AUTHORITY_PATH)
        readable = subprocess.CompletedProcess([], 0, stdout="{}", stderr="")
        with mock.patch.object(loop_engine, "run_command", side_effect=[not_found, readable]):
            self.assertIsNone(REAL_READ_OWNER_FILE(self.root, self.spec, loop_engine.STANDING_AUTHORITY_PATH))


class BranchManifestPolicyTests(unittest.TestCase):
    """Policy keys outside `mutations` cannot widen a branch manifest's powers either."""

    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        _, self.spec = branch_spec(self.root, ["a.txt"])
        patcher = mock.patch.object(loop_engine, "owner_reviewed_legacy_manifest", return_value=False)
        patcher.start()
        self.addCleanup(patcher.stop)
        patcher = mock.patch.object(
            loop_engine, "effective_mutations", return_value={key: True for key in loop_engine.MUTATION_KEYS}
        )
        patcher.start()
        self.addCleanup(patcher.stop)

    def test_validation_pins_the_base_and_refuses_protected_scope(self) -> None:
        loop_engine.validate_spec(self.spec)
        moved = json.loads(json.dumps(self.spec))
        moved["base_ref"] = "HEAD"
        with self.assertRaisesRegex(loop_engine.LoopError, "remote base branch"):
            loop_engine.validate_spec(moved)
        for path in (
            loop_engine.STANDING_AUTHORITY_PATH,
            "scripts/loop_engine.py",
            ".github/workflows/ci.yml",
            "AGENTS.md",
            ".claude/loop-specs/another-run.yaml",
        ):
            widened = json.loads(json.dumps(self.spec))
            widened["issues"][0]["chunks"][0]["files"].append(path)
            with self.assertRaisesRegex(loop_engine.LoopError, "protected"):
                loop_engine.validate_spec(widened)

    def test_the_protected_set_covers_gates_hooks_pins_and_instructions_in_every_spelling(self) -> None:
        protected = [
            # gates, hooks and CI tooling
            "scripts/check_mathlib_style.py", "scripts/check_workflows.sh", "scripts/gates.sh",
            "scripts/precheck.sh", "scripts/validate_loop_specs.sh", "scripts/nolints.json",
            "scripts/audit_missing_baseline.txt", "scripts/EnumDecls.lean",
            # pins and the retired trust-guard surface
            "lakefile.toml", "lean-toolchain", "lake-manifest.json", "pins.json", "exe/Restate.lean",
            "registry/sources.json", "DerivedAlgGeoSweep.lean",
            # instructions and agent configuration at any depth
            "DerivedAlgGeo/CLAUDE.md", "docs/AGENTS.md", "CLAUDE.local.md", ".mcp.json",
            ".claude/commands/go.md", ".codex/config.toml", "openspec/config.yaml",
            # other spellings of protected paths
            "Scripts/loop_engine.py", "claude.md", "Agents.md", ".GitHub/workflows/ci.yml",
            ".claude//settings.json", "./scripts/gates.sh", "scripts/AlgebraicGeometryAudit/../gates.sh",
            "scripts/AlgebraicGeometryAudit/../../evil.lean", ".claude/roadmap/../settings.json",
            # git's own path-level behaviour, at any depth
            ".gitattributes", "DerivedAlgGeo/.gitattributes", ".gitmodules", "docs/.gitignore",
            # another run's OpenSpec contract, and the accepted specs
            "openspec/changes/other-change/proposal.md", "openspec/specs/capability/spec.md",
        ]
        allowed = [
            "scripts/AlgebraicGeometryAudit.lean", "scripts/AlgebraicGeometryAudit/SchemeDerived.lean",
            "scripts/StabilityConditionAudit", "scripts/StabilityConditionCensus.lean",
            "DerivedAlgGeo/AlgebraicGeometry/Example.lean", "docs/architecture/generalization-backlog.md",
            "docs/architecture/loop-engineering-friction.md", "DerivedAlgGeo.lean",
            # RM-08 in the required ci check needs a closing PR to advance its entry
            ".claude/roadmap/stability-families.yaml",
        ]
        self.assertEqual([path for path in protected if not loop_engine.is_protected_path(path)], [])
        self.assertEqual([path for path in allowed if loop_engine.is_protected_path(path)], [])
        own = [MANIFEST, "openspec/changes/pilot-change"]
        self.assertFalse(loop_engine.is_protected_path(MANIFEST, own))
        self.assertFalse(loop_engine.is_protected_path("openspec/changes/pilot-change/tasks.md", own))
        self.assertTrue(loop_engine.is_protected_path(".claude/loop-specs/other.yaml", own))
        self.assertTrue(loop_engine.is_protected_path(".claude/loop-specs/TEST-RUN.yaml", own))

    def test_a_branch_run_may_not_introduce_symlinks(self) -> None:
        init_repo(self.root)
        base = commit_all(self.root, "base")
        (self.root / "docs").mkdir()
        (self.root / "docs" / "notes.md").symlink_to("../.claude/settings.json")
        head = commit_all(self.root, "an innocent-looking doc")
        state = {"spec_digest": loop_engine.digest(self.spec), "plan_paths": [MANIFEST]}
        with self.assertRaisesRegex(loop_engine.LoopError, "docs/notes.md"):
            loop_engine.require_no_links(self.root, self.spec, base, head, state)
        (self.root / "docs" / "notes.md").unlink()
        (self.root / "docs" / "notes.md").write_text("ordinary\n", encoding="utf-8")
        loop_engine.require_no_links(self.root, self.spec, base, commit_all(self.root, "a real doc"), state)
        lifted = json.loads(json.dumps(self.spec))
        lifted["issues"][0]["chunks"][0]["lift_targets"] = [".claude/skills"]
        with self.assertRaisesRegex(loop_engine.LoopError, "protected"):
            loop_engine.validate_spec(lifted)

    def test_publication_refuses_protected_paths_but_admits_the_runs_own_manifest(self) -> None:
        state = {
            "spec_digest": loop_engine.digest(self.spec),
            "plan_paths": [MANIFEST],
            "chunk": {"files": ["a.txt"]},
        }
        loop_engine.verify_remote_chunk_files(
            self.root, self.spec, {"files": [{"path": "a.txt"}, {"path": MANIFEST}]}, state
        )
        for path in (loop_engine.STANDING_AUTHORITY_PATH, "scripts/loop_recovery.py"):
            with self.assertRaisesRegex(loop_engine.LoopError, "protected"):
                loop_engine.verify_remote_chunk_files(
                    self.root, self.spec, {"files": [{"path": "a.txt"}, {"path": path}]}, state
                )

    def test_admin_merge_force_push_and_non_pr_close_are_owner_policy(self) -> None:
        self.spec["merge"] = {**self.spec["merge"], "allow_admin": True}
        self.spec["allow_force_push"] = True
        self.spec["closure"]["allow_non_pr"] = True
        with self.assertRaisesRegex(loop_engine.LoopError, "administrator merge is never available"):
            loop_engine.action_merge(self.root, self.spec, 12, self.root / "ledger.json", None, False, True, None, True)
        with self.assertRaisesRegex(loop_engine.LoopError, "force-with-lease is not available"):
            loop_engine.action_push(self.root, self.spec, None, True, True)
        with self.assertRaisesRegex(loop_engine.LoopError, "only through a verified merged PR"):
            loop_engine.action_close(self.root, self.spec, 1, None, None, True)

    def test_push_lands_only_on_the_authorized_repository(self) -> None:
        init_repo(self.root)
        self.spec["issues"][0]["chunks"][0]["files"] = ["a.txt"]
        (self.root / "a.txt").write_text("base\n", encoding="utf-8")
        commit_all(self.root, "base")
        publish_base(self.root)
        git_in(self.root, "checkout", "-q", "-b", "agent/test-issue")
        (self.root / "a.txt").write_text("chunk\n", encoding="utf-8")
        commit_all(self.root, "chunk")
        git_in(self.root, "remote", "add", "origin", "https://github.com/example/repository.git")
        ledger_file = self.root / ".loop-runs" / "test-chunk.json"
        ledger = passing_ledger_state(self.root, self.spec)
        ledger["schema"] = f"{loop_engine.RUN_SCHEMA}/ledger"
        loop_engine.atomic_json(ledger_file, ledger)
        git_in(self.root, "remote", "set-url", "--push", "origin", "https://github.com/attacker/fork.git")
        with self.assertRaisesRegex(loop_engine.LoopError, "attacker/fork"):
            loop_engine.action_push(self.root, self.spec, None, False, True, ledger_file)
        # A second push URL behind a legitimate first one also receives the push.
        git_in(self.root, "remote", "set-url", "--push", "origin", "https://github.com/example/repository.git")
        git_in(self.root, "remote", "set-url", "--add", "--push", "origin", "https://github.com/attacker/fork.git")
        with self.assertRaisesRegex(loop_engine.LoopError, "attacker/fork"):
            loop_engine.action_push(self.root, self.spec, None, False, True, ledger_file)
        git_in(self.root, "remote", "set-url", "--delete", "--push", "origin", "attacker")
        with contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(loop_engine.action_push(self.root, self.spec, None, False, True, ledger_file), 0)
        self.assertIn("DRY-RUN git push", output.getvalue())


class CIFailureRepairTests(unittest.TestCase):
    """CI repair evidence is exact-head, append-only, cap-charged, and ledger-bound."""

    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        init_repo(self.root)
        self.spec_path, self.spec = branch_spec(self.root, ["a.txt"])
        (self.root / "a.txt").write_text("base\n", encoding="utf-8")
        commit_all(self.root, "base")
        publish_base(self.root)
        self.base_sha = git_in(self.root, "rev-parse", "main")
        git_in(self.root, "checkout", "-q", "-b", "agent/test-issue")
        (self.root / "a.txt").write_text("failed build\n", encoding="utf-8")
        self.failed_head = commit_all(self.root, "failed build")
        git_in(self.root, "remote", "add", "origin", "https://github.com/example/repository.git")
        self.remote_head = self.failed_head
        self.pull = self.make_pull(self.failed_head)
        self.pull_reread: dict | None = None
        self.open_pulls = [self.pull]
        self.protection: dict = {"contexts": ["ci"], "checks": []}
        self.check_runs: list[dict] = [self.check_run(self.failed_head, "failure", "2026-09-24T01:00:00Z")]
        self.statuses: list[dict] = []
        self.source_sha_sequence: list[str] = []
        self.base_sha_sequence: list[str] = []
        self.protection_sequence: list[dict] = []
        for name, value in (
            ("owner_reviewed_legacy_manifest", False),
            ("require_legacy_issue_open", None),
        ):
            patcher = mock.patch.object(loop_engine, name, return_value=value)
            patcher.start()
            self.addCleanup(patcher.stop)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(loop_engine.ledger_init(self.root, self.spec_path, 1, "test-chunk", None), 0)
        self.state_file = self.root / ".loop-runs" / "test-chunk.json"
        self.pass_review(self.failed_head)

    def make_pull(self, head: str, *, source: str = "example/repository", state: str = "open", draft: bool = False) -> dict:
        repository = {"full_name": "example/repository"}
        return {
            "number": 42,
            "state": state,
            "draft": draft,
            "head": {"ref": "agent/test-issue", "sha": head, "repo": {"full_name": source}},
            "base": {"ref": "main", "sha": self.base_sha if hasattr(self, "base_sha") else "b" * 40, "repo": repository},
            "body": "Closes #1\n",
            "html_url": "https://github.com/example/repository/pull/42",
        }

    def check_run(self, head: str, conclusion: str | None, completed: str, *, status: str = "completed", app_id: int = 77) -> dict:
        return {
            "id": 7001,
            "name": "ci",
            "head_sha": head,
            "status": status,
            "conclusion": conclusion,
            "created_at": "2026-09-24T00:00:00Z",
            "started_at": "2026-09-24T00:00:30Z",
            "completed_at": completed,
            "html_url": "https://github.com/example/repository/actions/runs/7001",
            "app": {"id": app_id, "slug": "github-actions"},
        }

    def pass_review(self, commit: str) -> None:
        with contextlib.redirect_stdout(io.StringIO()):
            for reviewer in REVIEWERS:
                self.assertEqual(
                    loop_engine.ledger_record_review(
                        self.state_file,
                        reviewer,
                        commit,
                        "pass",
                        None,
                        reviewer_output(self.root, reviewer, "pass"),
                    ),
                    0,
                )
            self.assertEqual(loop_engine.ledger_adjudicate(self.state_file, "pass", "all checks passed"), 0)

    def repair_candidate(self, content: str = "fixed build\n") -> str:
        (self.root / "a.txt").write_text(content, encoding="utf-8")
        return commit_all(self.root, "repair build")

    def provider_api(self, _root: Path, args: list[str]):
        request = next((arg for arg in args if arg.startswith("repos/")), "")
        if "/pulls?state=open" in request:
            return self.open_pulls
        if request.endswith("/pulls/42"):
            return self.pull_reread or self.pull
        if "/git/ref/heads/agent/test-issue" in request:
            value = self.source_sha_sequence.pop(0) if self.source_sha_sequence else self.remote_head
            return {"object": {"sha": value}}
        if "/git/ref/heads/main" in request:
            value = self.base_sha_sequence.pop(0) if self.base_sha_sequence else self.base_sha
            return {"object": {"sha": value}}
        if "/protection/required_status_checks" in request:
            return self.protection_sequence.pop(0) if self.protection_sequence else self.protection
        if "/check-runs?per_page=100" in request:
            return {"total_count": len(self.check_runs), "check_runs": self.check_runs}
        if "/statuses?per_page=100" in request:
            return self.statuses
        raise AssertionError(f"unexpected provider request: {request}")

    def admit(self, candidate: str) -> int:
        with mock.patch.object(loop_engine, "gh_json", side_effect=self.provider_api):
            return loop_engine.ledger_admit_ci_repair(self.root, self.spec, self.state_file, candidate)

    def test_exact_head_failure_appends_a_charged_round_without_rewriting_history(self) -> None:
        original = json.loads(self.state_file.read_text(encoding="utf-8"))["rounds"][0]
        original_bytes = self.state_file.read_bytes()
        candidate = self.repair_candidate()
        with contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(self.admit(candidate), 0)
        self.assertIn("round=2", output.getvalue())
        state = json.loads(self.state_file.read_text(encoding="utf-8"))
        self.assertEqual(state["rounds"][0], original)
        self.assertEqual(loop_engine.improvement_rounds_used(state), 2)
        self.assertEqual(state["status"], "reviewing")
        event = state["ci_failure_repairs"][0]
        self.assertEqual(event["sequence"], 1)
        self.assertEqual(event["prior_passing_round"], 1)
        self.assertEqual(event["failed_head"], self.failed_head)
        self.assertEqual(event["required_check"]["name"], "ci")
        self.assertEqual(event["required_check"]["conclusion"], "failure")
        self.assertEqual(event["required_check"]["app_id"], 77)
        self.assertEqual(event["pr_number"], 42)
        self.assertEqual(event["source_branch"], "agent/test-issue")
        self.assertEqual(event["proposed_commit"], candidate)
        self.assertEqual(state["rounds"][1]["kind"], "ci_failure_repair")
        self.assertEqual(state["rounds"][1]["number"], 2)
        self.assertEqual(state["rounds"][1]["commit"], candidate)
        with self.assertRaisesRegex(loop_engine.LoopError, "pending or needs changes"):
            loop_engine.require_ci_repairs_resolved(state)

        event_before = json.loads(json.dumps(event))
        self.pass_review(candidate)
        state = json.loads(self.state_file.read_text(encoding="utf-8"))
        self.assertEqual(state["ci_failure_repairs"][0], event_before)
        loop_engine.require_ci_repairs_resolved(state)
        loop_engine.require_repair_pr_binding(state, 42, candidate)
        with self.assertRaisesRegex(loop_engine.LoopError, "does not match the PR bound"):
            loop_engine.require_repair_pr_binding(state, 43, candidate)
        with self.assertRaisesRegex(loop_engine.LoopError, "must equal the full commit"):
            loop_engine.require_repair_pr_binding(state, 42, self.failed_head)

    def test_failure_admission_rejects_stale_moved_or_ambiguous_heads_without_writing(self) -> None:
        candidate = self.repair_candidate()
        cases = [
            ("check SHA", lambda: self.check_runs.__setitem__(0, self.check_run("e" * 40, "failure", "2026-09-24T01:00:00Z"))),
            ("source SHA", lambda: setattr(self, "remote_head", "f" * 40)),
            ("source moved after checks", lambda: setattr(self, "source_sha_sequence", [self.failed_head, "f" * 40])),
            ("base moved after checks", lambda: setattr(self, "base_sha_sequence", [self.base_sha, "f" * 40])),
            ("moved PR", lambda: setattr(self, "pull_reread", self.make_pull("d" * 40))),
            ("issue link moved", lambda: setattr(self, "pull_reread", {**self.make_pull(self.failed_head), "body": "Closes #2\n"})),
            ("duplicate PR", lambda: self.open_pulls.append(self.make_pull(self.failed_head))),
            ("draft PR", lambda: self.open_pulls.__setitem__(0, self.make_pull(self.failed_head, draft=True))),
            ("fork source", lambda: self.open_pulls.__setitem__(0, self.make_pull(self.failed_head, source="fork/repository"))),
        ]
        for label, change in cases:
            with self.subTest(label=label):
                self.pull = self.make_pull(self.failed_head)
                self.pull_reread = None
                self.open_pulls = [self.pull]
                self.remote_head = self.failed_head
                self.source_sha_sequence = []
                self.base_sha_sequence = []
                self.protection_sequence = []
                self.check_runs = [self.check_run(self.failed_head, "failure", "2026-09-24T01:00:00Z")]
                change()
                before = self.state_file.read_bytes()
                with mock.patch.object(loop_engine, "gh_json", side_effect=self.provider_api), self.assertRaises(loop_engine.LoopError):
                    loop_engine.ledger_admit_ci_repair(self.root, self.spec, self.state_file, candidate)
                self.assertEqual(self.state_file.read_bytes(), before)
        self.pull = self.make_pull(self.failed_head)
        self.pull_reread = None
        self.open_pulls = [self.pull]
        self.remote_head = self.failed_head
        self.check_runs = []
        self.statuses = [{
            "id": 811,
            "context": "ci",
            "state": "failure",
            "sha": "e" * 40,
            "updated_at": "2026-09-24T01:05:00Z",
        }]
        before = self.state_file.read_bytes()
        with mock.patch.object(loop_engine, "gh_json", side_effect=self.provider_api), self.assertRaisesRegex(
            loop_engine.LoopError, "exact pull-request head"
        ):
            loop_engine.ledger_admit_ci_repair(self.root, self.spec, self.state_file, candidate)
        self.assertEqual(self.state_file.read_bytes(), before)

    def test_only_current_failures_of_checks_required_by_both_sources_are_admissible(self) -> None:
        candidate = self.repair_candidate()
        cases = [
            ("optional check", {"contexts": ["build"], "checks": []}, [self.check_run(self.failed_head, "failure", "2026-09-24T01:00:00Z")]),
            ("pending", {"contexts": ["ci"], "checks": []}, [self.check_run(self.failed_head, None, "", status="in_progress")]),
            ("cancelled", {"contexts": ["ci"], "checks": []}, [self.check_run(self.failed_head, "cancelled", "2026-09-24T01:00:00Z")]),
            ("successful rerun", {"contexts": ["ci"], "checks": []}, [
                self.check_run(self.failed_head, "failure", "2026-09-24T01:00:00Z"),
                {**self.check_run(self.failed_head, "success", "2026-09-24T02:00:00Z"), "id": 7002},
            ]),
            ("wrong app", {"contexts": [], "checks": [{"context": "ci", "app_id": 99}]}, [self.check_run(self.failed_head, "failure", "2026-09-24T01:00:00Z")]),
            ("missing live protection", {"contexts": ["ci"]}, [self.check_run(self.failed_head, "failure", "2026-09-24T01:00:00Z")]),
        ]
        for label, protection, checks in cases:
            with self.subTest(label=label):
                self.pull = self.make_pull(self.failed_head)
                self.pull_reread = None
                self.open_pulls = [self.pull]
                self.remote_head = self.failed_head
                self.protection = protection
                self.check_runs = checks
                self.statuses = []
                before = self.state_file.read_bytes()
                with mock.patch.object(loop_engine, "gh_json", side_effect=self.provider_api), self.assertRaises(loop_engine.LoopError):
                    loop_engine.ledger_admit_ci_repair(self.root, self.spec, self.state_file, candidate)
                self.assertEqual(self.state_file.read_bytes(), before)
        self.protection = {"contexts": ["ci"], "checks": []}

    def test_changed_live_protection_during_admission_is_rejected_without_writing(self) -> None:
        candidate = self.repair_candidate()
        self.protection_sequence = [
            {"contexts": ["ci"], "checks": []},
            {"contexts": ["build"], "checks": []},
        ]
        before = self.state_file.read_bytes()
        with mock.patch.object(loop_engine, "gh_json", side_effect=self.provider_api), self.assertRaisesRegex(
            loop_engine.LoopError, "protection changed"
        ):
            loop_engine.ledger_admit_ci_repair(self.root, self.spec, self.state_file, candidate)
        self.assertEqual(self.state_file.read_bytes(), before)

    def test_legacy_status_failure_records_exact_context_sha_and_run(self) -> None:
        candidate = self.repair_candidate()
        self.check_runs = []
        self.statuses = [
            {
                "id": 811,
                "context": "ci",
                "state": "failure",
                "sha": self.failed_head,
                "updated_at": "2026-09-24T01:05:00Z",
                "target_url": "https://ci.example/run/811",
            }
        ]
        self.admit(candidate)
        state = json.loads(self.state_file.read_text(encoding="utf-8"))
        evidence = state["ci_failure_repairs"][0]["required_check"]
        self.assertEqual(evidence["source"], "commit_status")
        self.assertEqual(evidence["name"], "ci")
        self.assertEqual(evidence["head_sha"], self.failed_head)
        self.assertEqual(evidence["run_id"], 811)

    def test_repeated_failures_append_events_and_charge_each_ordinary_review_slot(self) -> None:
        first_candidate = self.repair_candidate("first repair\n")
        self.admit(first_candidate)
        self.pass_review(first_candidate)
        first_event = json.loads(self.state_file.read_text(encoding="utf-8"))["ci_failure_repairs"][0]

        self.remote_head = first_candidate
        self.pull = self.make_pull(first_candidate)
        self.pull_reread = None
        self.open_pulls = [self.pull]
        self.check_runs = [self.check_run(first_candidate, "failure", "2026-09-24T03:00:00Z")]
        second_candidate = self.repair_candidate("second repair\n")
        self.admit(second_candidate)

        state = json.loads(self.state_file.read_text(encoding="utf-8"))
        self.assertEqual(state["ci_failure_repairs"][0], first_event)
        self.assertEqual([event["sequence"] for event in state["ci_failure_repairs"]], [1, 2])
        self.assertEqual(state["ci_failure_repairs"][1]["prior_passing_round"], 2)
        self.assertEqual(state["ci_failure_repairs"][1]["failed_head"], first_candidate)
        self.assertEqual(state["rounds"][-1]["kind"], "ci_failure_repair")
        self.assertEqual(state["rounds"][-1]["number"], 3)
        self.assertEqual(state["rounds"][-1]["commit"], second_candidate)
        self.assertEqual(loop_engine.improvement_rounds_used(state), 3)

    def test_passing_repair_still_requires_green_checks_on_its_exact_pr_head_before_merge(self) -> None:
        candidate = self.repair_candidate()
        self.admit(candidate)
        self.pass_review(candidate)
        pr = {
            "state": "OPEN",
            "isDraft": False,
            "headRefName": "agent/test-issue",
            "headRefOid": candidate,
            "baseRefName": "main",
            "body": "Closes #1\n",
            "files": [{"path": "a.txt"}],
            "comments": [],
        }
        with mock.patch.object(loop_engine, "authorize_action"), mock.patch.object(
            loop_engine, "require_predecessor_prs", return_value=[]
        ), mock.patch.object(loop_engine, "check_required_checks", return_value=candidate) as checks, mock.patch.object(
            loop_engine, "gh_json", return_value=pr
        ), mock.patch.object(loop_engine, "reviewed_content_matches", return_value=True), mock.patch.object(
            loop_engine, "verify_remote_chunk_files"
        ), mock.patch.object(loop_engine, "require_published_head_has_no_links"), contextlib.redirect_stdout(
            io.StringIO()
        ):
            self.assertEqual(
                loop_engine.action_merge(
                    self.root, self.spec, 42, self.state_file, None, False, False, None, True
                ),
                0,
            )
        checks.assert_called_once_with(self.root, self.spec, 42)

        with mock.patch.object(loop_engine, "authorize_action"), mock.patch.object(
            loop_engine, "require_predecessor_prs", return_value=[]
        ), mock.patch.object(
            loop_engine, "check_required_checks", side_effect=loop_engine.LoopError("required checks are not green")
        ), self.assertRaisesRegex(loop_engine.LoopError, "required checks are not green"):
            loop_engine.action_merge(
                self.root, self.spec, 42, self.state_file, None, False, False, None, True
            )

        with mock.patch.object(loop_engine, "authorize_action"), mock.patch.object(
            loop_engine, "require_predecessor_prs", return_value=[]
        ), mock.patch.object(loop_engine, "check_required_checks", return_value=self.failed_head), mock.patch.object(
            loop_engine, "gh_json", return_value=pr
        ), mock.patch.object(loop_engine, "reviewed_content_matches", return_value=True), mock.patch.object(
            loop_engine, "verify_remote_chunk_files"
        ), mock.patch.object(loop_engine, "require_published_head_has_no_links"), self.assertRaisesRegex(
            loop_engine.LoopError, "moved between the check read"
        ):
            loop_engine.action_merge(
                self.root, self.spec, 42, self.state_file, None, False, False, None, True
            )

    def test_repair_push_and_pr_creation_stay_bound_to_the_failed_pr(self) -> None:
        candidate = self.repair_candidate()
        self.admit(candidate)
        self.pass_review(candidate)

        with mock.patch.object(loop_engine, "authorize_action"), mock.patch.object(
            loop_engine, "gh_json", side_effect=self.provider_api
        ), contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(
                loop_engine.action_push(self.root, self.spec, None, False, True, self.state_file), 0
            )
        self.assertIn("DRY-RUN git push", output.getvalue())

        wrong_pr = self.make_pull(self.failed_head)
        wrong_pr["number"] = 43
        self.pull = wrong_pr
        self.open_pulls = [wrong_pr]
        with mock.patch.object(loop_engine, "authorize_action"), mock.patch.object(
            loop_engine, "gh_json", side_effect=self.provider_api
        ), self.assertRaisesRegex(loop_engine.LoopError, "bound to the latest CI-repair event"):
            loop_engine.action_push(self.root, self.spec, None, False, True, self.state_file)

        body = self.root / ".loop-runs" / "replacement-pr.md"
        body.parent.mkdir(parents=True, exist_ok=True)
        body.write_text("Closes #1\n", encoding="utf-8")
        with mock.patch.object(loop_engine, "authorize_action"), mock.patch.object(
            loop_engine, "gh_json"
        ) as provider, self.assertRaisesRegex(loop_engine.LoopError, "refusing to create a replacement PR"):
            loop_engine.action_create_pr(
                self.root, self.spec, 1, self.state_file, "Repair", str(body), True, True
            )
        provider.assert_not_called()

    def test_candidate_must_descend_from_failed_head_and_stay_inside_the_chunk(self) -> None:
        with self.assertRaisesRegex(loop_engine.LoopError, "must descend"):
            loop_engine.validate_repair_candidate(self.root, self.spec, json.loads(self.state_file.read_text()), "a" * 40, self.failed_head)
        outside = self.root / "b.txt"
        outside.write_text("out of scope\n", encoding="utf-8")
        outside_commit = commit_all(self.root, "out of scope")
        with self.assertRaisesRegex(loop_engine.LoopError, "outside the frozen chunk"):
            loop_engine.validate_repair_candidate(
                self.root, self.spec, json.loads(self.state_file.read_text()), self.failed_head, outside_commit
            )

    def test_candidate_scope_includes_the_source_of_a_rename(self) -> None:
        outside = self.root / "outside.txt"
        outside.write_text("failed build\n", encoding="utf-8")
        failed_head = commit_all(self.root, "add out-of-scope rename source")
        git_in(self.root, "rm", "a.txt")
        git_in(self.root, "mv", "outside.txt", "a.txt")
        renamed = commit_all(self.root, "move out-of-scope source into frozen path")
        with self.assertRaisesRegex(loop_engine.LoopError, "outside the frozen chunk"):
            loop_engine.validate_repair_candidate(
                self.root,
                self.spec,
                json.loads(self.state_file.read_text(encoding="utf-8")),
                failed_head,
                renamed,
            )

    def test_existing_passed_ledger_must_be_upgraded_without_losing_round_history(self) -> None:
        state = json.loads(self.state_file.read_text(encoding="utf-8"))
        prior_rounds = state["rounds"]
        for key in ("repository", "remote", "base_branch", "ci_failure_repairs"):
            state.pop(key, None)
        loop_engine.atomic_json(self.state_file, state)
        with self.assertRaisesRegex(loop_engine.LoopError, "predates the CI-repair protocol"):
            loop_engine.action_ledger_state(self.root, self.spec, self.state_file)

        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(loop_engine.ledger_init(self.root, self.spec_path, 1, "test-chunk", None), 0)
        upgraded = json.loads(self.state_file.read_text(encoding="utf-8"))
        self.assertEqual(upgraded["rounds"], prior_rounds)
        self.assertEqual(upgraded["repository"], self.spec["repository"])
        self.assertEqual(upgraded["remote"], self.spec["remote"])
        self.assertEqual(upgraded["base_branch"], self.spec["base_branch"])
        self.assertEqual(upgraded["ci_failure_repairs"], [])
        self.assertEqual(
            loop_engine.action_ledger_state(self.root, self.spec, self.state_file)["rounds"], prior_rounds
        )

    def test_cap_exhaustion_is_terminal_and_another_state_directory_cannot_replace_it(self) -> None:
        self.spec["limits"]["max_review_rounds_per_chunk"] = 1
        write_manifest(self.root, self.spec)
        self.failed_head = commit_all(self.root, "freeze one-round cap")
        self.remote_head = self.failed_head
        self.pull = self.make_pull(self.failed_head)
        self.open_pulls = [self.pull]
        self.check_runs = [self.check_run(self.failed_head, "failure", "2026-09-24T01:00:00Z")]
        self.state_file.unlink()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(loop_engine.ledger_init(self.root, self.spec_path, 1, "test-chunk", None), 0)
        self.pass_review(self.failed_head)
        original_round = json.loads(self.state_file.read_text(encoding="utf-8"))["rounds"][0]
        candidate = self.repair_candidate()
        with contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(self.admit(candidate), 0)
        self.assertIn("CAP EXHAUSTED", output.getvalue())
        state = json.loads(self.state_file.read_text(encoding="utf-8"))
        self.assertEqual(state["status"], "repair_exhausted")
        self.assertEqual(state["rounds"], [original_round])
        self.assertEqual(state["ci_failure_repairs"][0]["disposition"], "cap_exhausted")
        self.assertIsNone(state["ci_failure_repairs"][0]["round"])
        before = self.state_file.read_bytes()
        with self.assertRaisesRegex(loop_engine.LoopError, "cap is exhausted"):
            loop_engine.require_ci_repairs_resolved(state)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertNotEqual(loop_engine.ledger_init(self.root, self.spec_path, 1, "test-chunk", ".loop-runs/alternate"), 0)
        self.assertEqual(self.state_file.read_bytes(), before)
        with self.assertRaisesRegex(loop_engine.LoopError, "under the repository's .loop-runs root"):
            loop_engine.state_path(self.root, self.spec, str(self.root / "outside"), "test-chunk")

    def test_all_shipping_paths_reject_a_pending_repair_and_initial_draft_pr_still_works(self) -> None:
        candidate = self.repair_candidate()
        self.admit(candidate)
        body = self.root / ".loop-runs" / "pr-body.md"
        body.write_text("Closes #1\n", encoding="utf-8")
        with mock.patch.object(loop_engine, "authorize_action"), mock.patch.object(
            loop_engine, "require_predecessor_prs", return_value=[]
        ), mock.patch.object(loop_engine, "owner_reviewed_legacy_manifest", return_value=True), mock.patch.object(
            loop_engine, "predecessor_attestation_policy", return_value={"emit": True}
        ):
            actions = [
                lambda: loop_engine.action_push(self.root, self.spec, None, False, True, self.state_file),
                lambda: loop_engine.action_create_pr(self.root, self.spec, 1, self.state_file, "title", str(body), True, True),
                lambda: loop_engine.action_attest_pr(self.root, self.spec, 1, 42, self.state_file, True),
                lambda: loop_engine.action_ready(self.root, self.spec, 42, self.state_file, True),
                lambda: loop_engine.action_approve(self.root, self.spec, 42, self.state_file, "approved", True),
                lambda: loop_engine.action_merge(self.root, self.spec, 42, self.state_file, None, False, False, None, True),
                lambda: loop_engine.action_close(self.root, self.spec, 1, None, None, True, self.state_file),
            ]
            for action in actions:
                with self.subTest(action=action), self.assertRaisesRegex(loop_engine.LoopError, "CI-repair panel is pending"):
                    action()

        # A fresh, unreviewed ledger keeps the existing draft-first workflow.
        self.state_file.unlink()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(loop_engine.ledger_init(self.root, self.spec_path, 1, "test-chunk", None), 0)
        with mock.patch.object(loop_engine, "authorize_action"), contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(
                loop_engine.action_create_pr(self.root, self.spec, 1, self.state_file, "title", str(body), True, True),
                0,
            )
        self.assertIn("--draft", output.getvalue())

    def test_required_checks_fall_back_to_the_manifest_and_report_the_checked_head(self) -> None:
        self.spec["runner"]["required_checks"] = ["ci", "build"]
        rollup = {
            "headRefOid": "c" * 40,
            "statusCheckRollup": [{"name": "ci", "conclusion": "SUCCESS", "completedAt": "2026-09-22T00:00:00Z"}],
        }
        with mock.patch.object(loop_engine, "gh_json", return_value=rollup), mock.patch.object(
            loop_engine, "protected_check_names", return_value=set()
        ):
            with self.assertRaisesRegex(loop_engine.LoopError, "missing build"):
                loop_engine.check_required_checks(self.root, self.spec, 12)
        with mock.patch.object(loop_engine, "gh_json", return_value=rollup), mock.patch.object(
            loop_engine, "protected_check_names", return_value={"ci"}
        ):
            self.assertEqual(loop_engine.check_required_checks(self.root, self.spec, 12), "c" * 40)


class ContentBindingTests(unittest.TestCase):
    """A review binds the change it read, not the base the change sits on."""

    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        init_repo(self.root)
        self.spec_path, self.spec = branch_spec(self.root, ["a.txt"])
        (self.root / "a.txt").write_text(numbered_lines(20), encoding="utf-8")
        (self.root / "b.txt").write_text("unrelated\n", encoding="utf-8")
        commit_all(self.root, "base")
        publish_base(self.root)
        git_in(self.root, "checkout", "-q", "-b", "agent/test-issue")
        (self.root / "a.txt").write_text(numbered_lines(20, {2: "reviewed change"}), encoding="utf-8")
        self.reviewed = commit_all(self.root, "reviewed change")
        patcher = mock.patch.object(loop_engine, "owner_reviewed_legacy_manifest", return_value=False)
        patcher.start()
        self.addCleanup(patcher.stop)
        self.state = {
            "plan_paths": [MANIFEST, "openspec/changes/pilot-change"],
            "openspec_change": "pilot-change",
            "openspec_digest_version": 3,
            "chunk": {"files": ["a.txt"]},
        }
        # The provider's view of the base branch tip is local `main` here.
        patcher = mock.patch.object(
            loop_engine, "trusted_base_commit", side_effect=lambda _root, _spec: git_in(self.root, "rev-parse", "main")
        )
        patcher.start()
        self.addCleanup(patcher.stop)

    def move_base(self, touch_reviewed_file: bool = False, base_marker: str = "base change") -> None:
        git_in(self.root, "checkout", "-q", "main")
        (self.root / "b.txt").write_text("unrelated, updated\n", encoding="utf-8")
        if touch_reviewed_file:
            (self.root / "a.txt").write_text(numbered_lines(20, {18: base_marker}), encoding="utf-8")
        commit_all(self.root, "base moves")
        publish_base(self.root)
        git_in(self.root, "checkout", "-q", "agent/test-issue")

    def matches(self, head: str) -> bool:
        with contextlib.redirect_stdout(io.StringIO()):
            return loop_engine.reviewed_content_matches(self.root, self.spec, self.state, self.reviewed, head)

    def probe(self, name: str, edit) -> str:
        """Commit one edit on top of the reviewed commit, on a throwaway branch."""
        git_in(self.root, "checkout", "-q", "-B", name, self.reviewed)
        edit()
        return commit_all(self.root, name)

    def test_a_rebase_over_unrelated_base_changes_keeps_the_review(self) -> None:
        self.move_base()
        git_in(self.root, "rebase", "-q", "origin/main")
        rebased = git_in(self.root, "rev-parse", "HEAD")
        self.assertNotEqual(rebased, self.reviewed)
        self.assertTrue(self.matches(rebased))

    def test_progress_records_may_change_after_review_and_nothing_else_may(self) -> None:
        change = self.root / "openspec" / "changes" / "pilot-change"

        def tick() -> None:
            tasks = change / "tasks.md"
            tasks.write_text(tasks.read_text(encoding="utf-8").replace("- [ ]", "- [x]"), encoding="utf-8")

        def log() -> None:
            (change / "agent-observations.md").write_text("- OBS-001 the base moved\n", encoding="utf-8")

        def reword() -> None:
            tasks = change / "tasks.md"
            tasks.write_text(tasks.read_text(encoding="utf-8").replace("Verify the test", "Skip the test"), encoding="utf-8")

        def swap_manifest() -> None:
            swapped = json.loads(json.dumps(self.spec))
            swapped["merge"]["allow_admin"] = True
            write_manifest(self.root, swapped)

        def smuggle() -> None:
            (change / "Smuggled.lean").write_text("attribute [simp] foo\n", encoding="utf-8")

        def edit_code() -> None:
            (self.root / "a.txt").write_text(numbered_lines(20, {2: "unreviewed"}), encoding="utf-8")

        self.assertTrue(self.matches(self.probe("tick", tick)))
        self.assertTrue(self.matches(self.probe("log", log)))
        for name, edit in (
            ("reword", reword),
            ("swap-manifest", swap_manifest),
            ("smuggle", smuggle),
            ("edit-code", edit_code),
        ):
            with self.subTest(name):
                self.assertFalse(self.matches(self.probe(name, edit)))

    def test_v2_reviewed_head_uses_historical_task_normalization(self) -> None:
        tasks = self.root / "openspec" / "changes" / "pilot-change" / "tasks.md"
        tasks.write_text(
            "# Tasks\n\n- [ ] 1.1 Real task\n\n```md\n- [ ] 9.1 Example\n```\n",
            encoding="utf-8",
        )
        self.reviewed = commit_all(self.root, "reviewed v2 tasks")
        state = {**self.state, "openspec_digest_version": 2}

        def tick_example() -> None:
            tasks.write_text(tasks.read_text(encoding="utf-8").replace("- [ ] 9.1", "- [x] 9.1"), encoding="utf-8")

        head = self.probe("v2-example-progress", tick_example)
        self.assertTrue(loop_engine.reviewed_content_matches(self.root, self.spec, state, self.reviewed, head))

        state["openspec_digest_version"] = 3
        self.assertFalse(loop_engine.reviewed_content_matches(self.root, self.spec, state, self.reviewed, head))

    def test_a_base_change_to_a_reviewed_file_requires_revalidation(self) -> None:
        self.move_base(touch_reviewed_file=True)
        git_in(self.root, "rebase", "-q", "origin/main")
        rebased = git_in(self.root, "rev-parse", "HEAD")
        base = git_in(self.root, "rev-parse", "main")
        # The diff is unchanged, but the file it sits in is not.
        self.assertEqual(
            loop_engine.change_fingerprint(self.root, base, self.reviewed, []),
            loop_engine.change_fingerprint(self.root, base, rebased, []),
        )
        self.assertFalse(self.matches(rebased))

    def test_a_base_change_to_a_directly_imported_module_requires_revalidation(self) -> None:
        git_in(self.root, "checkout", "-q", "main")
        (self.root / "Pkg").mkdir()
        (self.root / "Pkg" / "Dep.lean").write_text("def dep := 1\n", encoding="utf-8")
        (self.root / "Main.lean").write_text("import Pkg.Dep\n\ndef main := dep\n", encoding="utf-8")
        commit_all(self.root, "a module and its dependency")
        git_in(self.root, "checkout", "-q", "-b", "agent/import-test")
        (self.root / "Main.lean").write_text("import Pkg.Dep\n\ndef main := dep + 0\n", encoding="utf-8")
        reviewed = commit_all(self.root, "reviewed")
        git_in(self.root, "checkout", "-q", "main")
        (self.root / "Pkg" / "Dep.lean").write_text("def dep := 2\n", encoding="utf-8")
        base = commit_all(self.root, "the dependency changes meaning")
        git_in(self.root, "checkout", "-q", "agent/import-test")
        git_in(self.root, "rebase", "-q", "main")
        rebased = git_in(self.root, "rev-parse", "HEAD")
        state = {"chunk": {"files": ["Main.lean"]}}
        self.assertEqual(
            loop_engine.base_changes_under_review(self.root, base, state, reviewed, rebased), ["Pkg/Dep.lean"]
        )

    def test_a_relocated_change_moves_the_fingerprint(self) -> None:
        git_in(self.root, "checkout", "-q", "main")
        filler = "".join("  -- filler\n" for _ in range(30))
        text = f"namespace Safe\n{filler}end Safe\n\nnamespace Unsafe\n{filler}end Unsafe\n"
        (self.root / "Rel.lean").write_text(text, encoding="utf-8")
        base = commit_all(self.root, "two namespaces with identical bodies")
        lines = text.splitlines(keepends=True)

        def insert_at(index: int, name: str) -> str:
            git_in(self.root, "checkout", "-q", "-B", name, base)
            edited = lines[:index] + ["  attribute [simp] x\n"] + lines[index:]
            (self.root / "Rel.lean").write_text("".join(edited), encoding="utf-8")
            return commit_all(self.root, name)

        safe = insert_at(16, "in-safe")
        unsafe = insert_at(16 + 34, "in-unsafe")
        self.assertNotEqual(
            loop_engine.change_fingerprint(self.root, base, safe, []),
            loop_engine.change_fingerprint(self.root, base, unsafe, []),
        )

    def test_a_run_chosen_base_cannot_make_new_content_look_reviewed(self) -> None:
        # With the manifest's base_ref at the candidate itself, both diffs would
        # be empty; equivalence is measured against the provider's base tip.
        (self.root / "a.txt").write_text(numbered_lines(20, {2: "reviewed change", 5: "smuggled"}), encoding="utf-8")
        smuggled = commit_all(self.root, "unreviewed addition")
        spec = json.loads(json.dumps(self.spec))
        spec["base_ref"] = "HEAD"
        self.assertEqual(
            loop_engine.change_fingerprint(self.root, "HEAD", self.reviewed, []),
            loop_engine.change_fingerprint(self.root, "HEAD", smuggled, []),
        )
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertFalse(loop_engine.reviewed_content_matches(self.root, spec, {}, self.reviewed, smuggled))

    def test_a_passed_ledger_only_reopens_for_in_scope_base_revalidations(self) -> None:
        state_path = self.root / ".loop-runs" / "test-chunk.json"
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(loop_engine.ledger_init(self.root, self.spec_path, 1, "test-chunk", None), 0)
            state = json.loads(state_path.read_text(encoding="utf-8"))
            self.assertEqual(state["plan_paths"], [MANIFEST, "openspec/changes/pilot-change"])
            self.assertEqual(state["openspec_digest_version"], loop_engine.OPENSPEC_DIGEST_VERSION)
            base_at_init = git_in(self.root, "rev-parse", "origin/main")
            self.assertEqual(state["base_commit_at_init"], base_at_init)

            def panel(commit: str, verdict: str) -> None:
                for reviewer in REVIEWERS:
                    self.assertEqual(
                        loop_engine.ledger_record_review(
                            state_path, reviewer, commit, verdict, None,
                            reviewer_output(self.root, reviewer, verdict),
                        ),
                        0,
                    )

            panel(self.reviewed, "pass")
            self.assertEqual(loop_engine.ledger_adjudicate(state_path, "pass", "all clear"), 0)
            # Each round records the base it was reviewed against, as audit evidence.
            self.assertEqual(json.loads(state_path.read_text(encoding="utf-8"))["rounds"][0]["base_commit"], base_at_init)
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertNotEqual(
                    loop_engine.ledger_record_review(state_path, REVIEWERS[0], self.reviewed, "pass", None), 0
                )
            self.assertIn("exact commit", output.getvalue())

            self.move_base(touch_reviewed_file=True)
            git_in(self.root, "rebase", "-q", "origin/main")
            resolved = git_in(self.root, "rev-parse", "HEAD")
            panel(resolved, "pass")
            self.assertEqual(loop_engine.ledger_adjudicate(state_path, "pass", "base-only revalidation"), 0)
            state = json.loads(state_path.read_text(encoding="utf-8"))
            self.assertEqual(state["rounds"][-1]["kind"], "revalidation")
            self.assertEqual(state["status"], "passed")
            self.assertEqual(loop_engine.improvement_rounds_used(state), 1)

            (self.root / "a.txt").write_text(numbered_lines(20, {2: "changed implementation"}), encoding="utf-8")
            changed = commit_all(self.root, "changed implementation")
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertNotEqual(
                    loop_engine.ledger_record_review(state_path, REVIEWERS[0], changed, "pass", None), 0
                )
            self.assertIn("charged CI repair", output.getvalue())
            git_in(self.root, "checkout", "-q", "--detach", resolved)
            git_in(self.root, "checkout", "-q", "-B", "agent/test-issue")

            self.move_base(touch_reviewed_file=True, base_marker="base change 2")
            git_in(self.root, "rebase", "-q", "origin/main")
            second = git_in(self.root, "rev-parse", "HEAD")
            panel(second, "pass")
            self.assertEqual(loop_engine.ledger_adjudicate(state_path, "pass", "second base revalidation"), 0)

            self.move_base(touch_reviewed_file=True, base_marker="base change 3")
            git_in(self.root, "rebase", "-q", "origin/main")
            third = git_in(self.root, "rev-parse", "HEAD")
            output = io.StringIO()
            with contextlib.redirect_stdout(output):
                self.assertNotEqual(
                    loop_engine.ledger_record_review(state_path, REVIEWERS[0], third, "pass", None), 0
                )
            self.assertIn("revalidation limit", output.getvalue())


class PlanInPullRequestPreflightTests(unittest.TestCase):
    """The plan may travel in the work PR; nothing has to merge first."""

    def setUp(self) -> None:
        self.directory = tempfile.TemporaryDirectory()
        self.addCleanup(self.directory.cleanup)
        self.root = Path(self.directory.name)
        init_repo(self.root)
        (self.root / "openspec").mkdir()
        (self.root / "openspec" / "config.yaml").write_text("schema: spec-driven\n", encoding="utf-8")
        commit_all(self.root, "repository with OpenSpec configured")
        publish_base(self.root)
        git_in(self.root, "remote", "add", "origin", "https://github.com/example/repository.git")
        git_in(self.root, "checkout", "-q", "-b", "agent/test-issue")
        # make_spec rewrites the committed config with identical content.
        self.spec_path, self.spec = branch_spec(self.root, ["a.txt"])
        self.spec["roadmap_gate"] = "required"
        write_manifest(self.root, self.spec)
        patcher = mock.patch.object(loop_engine, "owner_reviewed_legacy_manifest", return_value=False)
        patcher.start()
        self.addCleanup(patcher.stop)

    def preflight(
        self, prs: list[dict] | None = None, protected: set[str] | None = None, labels: list[dict] | None = None
    ) -> tuple[int, str]:
        output = io.StringIO()
        with mock.patch.object(loop_engine, "gh_authenticated", return_value=self.spec["actor"]), mock.patch.object(
            loop_engine, "existing_prs", return_value=prs or []
        ), mock.patch.object(
            loop_engine, "protected_check_names", return_value=protected if protected is not None else {"ci"}
        ), mock.patch.object(
            loop_engine, "issue_state", return_value={"state": "OPEN", "labels": labels or [], "blockedBy": []}
        ), mock.patch.object(loop_engine, "require_predecessor_prs", return_value=[]), mock.patch.object(
            loop_engine, "roadmap_gate_args", return_value=[sys.executable, "-c", "pass"]
        ), contextlib.redirect_stdout(output):
            code = loop_engine.preflight(self.root, self.spec_path)
        return code, output.getvalue()

    def test_an_uncommitted_plan_on_the_work_branch_passes(self) -> None:
        code, output = self.preflight()
        self.assertEqual(code, 0, output)

    def test_unplanned_uncommitted_work_fails(self) -> None:
        (self.root / "stray.lean").write_text("-- unfinished\n", encoding="utf-8")
        code, output = self.preflight()
        self.assertEqual(code, 1)
        self.assertIn("outside this run's plan: stray.lean", output)

    def test_a_committed_plan_ahead_of_the_base_passes_and_a_stale_branch_fails(self) -> None:
        commit_all(self.root, "plan")
        code, output = self.preflight()
        self.assertEqual(code, 0, output)

        git_in(self.root, "checkout", "-q", "main")
        (self.root / "moved.txt").write_text("the base moved\n", encoding="utf-8")
        commit_all(self.root, "base moves")
        publish_base(self.root)
        git_in(self.root, "checkout", "-q", "agent/test-issue")
        code, output = self.preflight()
        self.assertEqual(code, 1)
        self.assertIn("does not contain origin/main", output)

    def test_history_on_the_branch_name_does_not_block_and_a_rival_pr_does(self) -> None:
        merged = {"number": 5, "state": "MERGED", "headRefName": "agent/test-issue", "closingIssuesReferences": []}
        own_open = {
            "number": 6, "state": "OPEN", "headRefName": "agent/test-issue",
            "closingIssuesReferences": [{"number": 1}], "author": {"login": self.spec["actor"]},
        }
        code, output = self.preflight([merged, own_open])
        self.assertEqual(code, 0, output)
        self.assertIn("resuming open PR #6", output)

        stranger = {**own_open, "author": {"login": "someone-else"}}
        code, output = self.preflight([stranger])
        self.assertEqual(code, 1)
        self.assertIn("is by 'someone-else'", output)

        rival = {"number": 7, "state": "OPEN", "headRefName": "agent/other", "closingIssuesReferences": [{"number": 1}]}
        code, output = self.preflight([rival])
        self.assertEqual(code, 1)
        self.assertIn("already has open PR #7", output)

    def test_a_retired_required_check_warns_instead_of_failing(self) -> None:
        code, output = self.preflight(protected={"build"})
        self.assertEqual(code, 0, output)
        self.assertIn("WARN manifest names checks branch protection no longer requires: ci", output)

    def test_epic_opt_ins_and_a_disabled_roadmap_gate_are_owner_policy(self) -> None:
        self.spec["eligibility"] = {"allow_epic_issues": [1]}
        self.spec["roadmap_gate"] = "disabled"
        write_manifest(self.root, self.spec)
        code, output = self.preflight(labels=[{"name": "epic"}])
        self.assertEqual(code, 1)
        self.assertIn("ineligible labels: epic", output)
        self.assertIn("runs it as required", output)


if __name__ == "__main__":
    unittest.main()
