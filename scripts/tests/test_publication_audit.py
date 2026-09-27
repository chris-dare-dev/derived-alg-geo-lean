#!/usr/bin/env python3
"""Git-tree and provider fixtures for the post-publication auditor."""

from __future__ import annotations

import copy
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts.ci_github_evidence import EvidenceError, GitHubClient
from scripts.publication_audit import UNKNOWN, _digest, collect, tree_comparison, verify_saved

REPO = "chris-dare-dev/derived-alg-geo-lean"
BASE = "a" * 40
HEAD = "b" * 40
PUBLISHED = "c" * 40
REVIEWED = "d" * 40
OTHER = "e" * 40
TREE = "1" * 40
CHANGED_TREE = "2" * 40


class Provider:
    def __init__(self) -> None:
        self.repository = REPO
        self.objects = {
            f"/pulls/7": {
                "number": 7, "merged": True, "merged_at": "2026-09-27T10:00:00Z",
                "merge_commit_sha": PUBLISHED, "html_url": f"https://github.com/{REPO}/pull/7",
                "head": {"sha": HEAD}, "base": {"sha": BASE}, "draft": False,
            },
            f"/git/commits/{PUBLISHED}": {"sha": PUBLISHED, "tree": {"sha": TREE}, "parents": [{"sha": BASE}]},
            f"/git/commits/{HEAD}": {"sha": HEAD, "tree": {"sha": TREE}, "parents": [{"sha": BASE}]},
            f"/git/commits/{REVIEWED}": {"sha": REVIEWED, "tree": {"sha": TREE}, "parents": [{"sha": BASE}]},
            f"/git/commits/{OTHER}": {"sha": OTHER, "tree": {"sha": CHANGED_TREE}, "parents": [{"sha": BASE}]},
        }
        self.ci = {
            "id": 11, "name": "ci", "head_sha": HEAD, "status": "completed",
            "conclusion": "success", "completed_at": "2026-09-27T09:59:00Z",
            "check_suite": {"id": 99}, "app": {"slug": "github-actions"},
            "html_url": f"https://github.com/{REPO}/runs/11",
        }
        self.workflow = {
            "id": 21, "run_attempt": 1, "check_suite_id": 99,
            "name": "CI", "path": ".github/workflows/ci.yml",
            "event": "pull_request", "head_sha": HEAD,
            "status": "completed", "conclusion": "success", "updated_at": "2026-09-27T09:59:01Z",
            "pull_requests": [{"number": 7, "base": {"sha": BASE}, "head": {"sha": HEAD}}],
        }
        self.checks = {HEAD: [self.ci], PUBLISHED: []}
        self.statuses = {HEAD: [], PUBLISHED: []}
        self.runs = [self.workflow]

    def get_object(self, path: str):
        if path.startswith("/actions/runs/"):
            run_id = int(path.rsplit("/", 1)[1])
            return copy.deepcopy(next(run for run in self.runs if run["id"] == run_id))
        return copy.deepcopy(self.objects[path])

    def get_all(self, path: str, *, key=None):
        if path.startswith("/commits/") and path.endswith("/check-runs?filter=all"):
            return copy.deepcopy(self.checks[path.split("/")[2]])
        if path.startswith("/commits/") and path.endswith("/statuses"):
            return copy.deepcopy(self.statuses[path.split("/")[2]])
        if path.startswith("/actions/runs?head_sha="):
            head = path.split("=", 1)[1]
            return copy.deepcopy([run for run in self.runs if run.get("head_sha") == head])
        raise AssertionError(path)


class PublicationAuditTest(unittest.TestCase):
    def test_clean_receipt_never_promotes_unknown_provenance(self):
        receipt = collect(Provider(), 7, REVIEWED)
        self.assertEqual(receipt["published_equals_supplied_reviewed_tree"], "identical")
        self.assertEqual(receipt["premerge_ci"]["state"], "observed_success_before_merge")
        self.assertEqual(receipt["premerge_ci"]["tested_candidate"], UNKNOWN)
        self.assertEqual(receipt["review_provenance"], UNKNOWN)
        self.assertEqual(receipt["merge_time_readiness"], UNKNOWN)
        self.assertFalse(receipt["operationally_verified"])
        self.assertEqual(receipt["receipt_sha256"], _digest(receipt))

    def test_reviewed_tree_and_base_drift_are_independent(self):
        provider = Provider()
        provider.objects[f"/git/commits/{PUBLISHED}"]["tree"]["sha"] = CHANGED_TREE
        provider.objects[f"/git/commits/{PUBLISHED}"]["parents"] = [{"sha": OTHER}]
        receipt = collect(provider, 7, REVIEWED)
        self.assertEqual(receipt["published_equals_supplied_reviewed_tree"], "different")
        self.assertFalse(receipt["recorded_base_equals_published_parent"])
        self.assertEqual(receipt["premerge_ci"]["state"], "observed_success_before_merge")

    def test_required_green_auxiliary_red_is_not_all_green(self):
        provider = Provider()
        provider.checks[HEAD].append({
            "id": 12, "name": "optional", "head_sha": HEAD,
            "status": "completed", "conclusion": "failure",
            "app": {"slug": "github-actions"}, "check_suite": {"id": 100},
            "completed_at": "2026-09-27T09:59:00Z",
        })
        receipt = collect(provider, 7, REVIEWED)
        self.assertEqual(receipt["premerge_ci"]["state"], "observed_success_before_merge")
        self.assertEqual(len(receipt["auxiliary_failed_checks"]), 1)
        self.assertEqual(receipt["merge_time_readiness"], UNKNOWN)

    def test_missing_or_ambiguous_ci_does_not_pass(self):
        provider = Provider()
        provider.checks[HEAD] = []
        self.assertEqual(collect(provider, 7)["premerge_ci"]["state"], "no_ci_check_observed")
        provider = Provider()
        provider.runs.append({**provider.workflow, "id": 22})
        self.assertEqual(collect(provider, 7)["premerge_ci"]["state"], UNKNOWN)
        provider = Provider()
        provider.ci["completed_at"] = "2026-09-27T10:01:00Z"
        self.assertEqual(collect(provider, 7)["premerge_ci"]["state"], "not_successful_before_merge")
        provider = Provider()
        provider.workflow["run_attempt"] = 2
        self.assertEqual(collect(provider, 7)["premerge_ci"]["state"], UNKNOWN)
        provider = Provider()
        provider.workflow["updated_at"] = "2026-09-27T10:01:00Z"
        self.assertEqual(collect(provider, 7)["premerge_ci"]["state"], UNKNOWN)

    def test_same_head_other_pr_cannot_authorize_pr_ci(self):
        provider = Provider()
        provider.workflow["pull_requests"] = [{"number": 8, "base": {"sha": BASE}, "head": {"sha": HEAD}}]
        self.assertEqual(collect(provider, 7)["premerge_ci"]["state"], UNKNOWN)
        provider.workflow["pull_requests"] = []
        self.assertEqual(
            collect(provider, 7)["premerge_ci"]["state"],
            "observed_head_success_before_merge_unassociated",
        )

    def test_bad_provider_identity_fails_closed(self):
        provider = Provider()
        provider.checks[HEAD].append(copy.deepcopy(provider.ci))
        with self.assertRaises(EvidenceError):
            collect(provider, 7)
        provider = Provider()
        provider.statuses[HEAD].append({"sha": OTHER, "state": "success"})
        with self.assertRaises(EvidenceError):
            collect(provider, 7)

    def test_postmerge_failure_is_separate(self):
        provider = Provider()
        provider.checks[PUBLISHED] = [{**provider.ci, "id": 31, "head_sha": PUBLISHED, "conclusion": "failure", "check_suite": {"id": 199}}]
        provider.runs.append({
            "id": 41, "run_attempt": 1, "check_suite_id": 199,
            "name": "CI", "path": ".github/workflows/ci.yml",
            "event": "push", "head_sha": PUBLISHED,
            "status": "completed", "conclusion": "failure",
        })
        receipt = collect(provider, 7, REVIEWED)
        self.assertEqual(receipt["postmerge_ci"]["state"], "failed")
        self.assertEqual(receipt["premerge_ci"]["state"], "observed_success_before_merge")

    def test_postmerge_same_name_foreign_workflow_and_neutral(self):
        provider = Provider()
        provider.checks[PUBLISHED] = [{**provider.ci, "id": 31, "head_sha": PUBLISHED, "check_suite": {"id": 199}}]
        provider.runs.append({
            "id": 41, "run_attempt": 1, "check_suite_id": 199,
            "name": "CI", "path": ".github/workflows/other.yml",
            "event": "push", "head_sha": PUBLISHED,
            "status": "completed", "conclusion": "success",
        })
        self.assertEqual(collect(provider, 7)["postmerge_ci"]["state"], UNKNOWN)
        provider.runs[-1]["path"] = ".github/workflows/ci.yml"
        for conclusion in ("cancelled", "skipped", "neutral", "timed_out"):
            provider.checks[PUBLISHED][0]["conclusion"] = conclusion
            provider.runs[-1]["conclusion"] = conclusion
            receipt = collect(provider, 7)
            self.assertEqual(receipt["postmerge_ci"]["state"], "not_passed")
            self.assertEqual(receipt["postmerge_ci"]["checks"][0]["conclusion"], conclusion)

    def test_forged_saved_claim_or_digest_cannot_verify_itself(self):
        provider = Provider()
        saved = collect(provider, 7, REVIEWED)
        self.assertEqual(verify_saved(provider, 7, saved, REVIEWED), saved)
        forged = copy.deepcopy(saved)
        forged["premerge_ci"]["tested_candidate"] = PUBLISHED
        forged["receipt_sha256"] = _digest(forged)
        with self.assertRaises(EvidenceError):
            verify_saved(provider, 7, forged, REVIEWED)
        forged = copy.deepcopy(saved)
        forged["published_tree"] = OTHER
        forged["receipt_sha256"] = _digest(forged)
        with self.assertRaises(EvidenceError):
            verify_saved(provider, 7, forged, REVIEWED)

    def test_historical_draft_or_behind_is_never_inferred(self):
        provider = Provider()
        provider.objects["/pulls/7"]["draft"] = True
        provider.objects["/pulls/7"]["mergeable_state"] = "behind"
        receipt = collect(provider, 7, REVIEWED)
        self.assertEqual(receipt["merge_time_readiness"], UNKNOWN)

    def test_new_push_and_stale_review_cannot_match_tree(self):
        provider = Provider()
        provider.objects[f"/git/commits/{HEAD}"]["tree"]["sha"] = CHANGED_TREE
        provider.objects[f"/git/commits/{PUBLISHED}"]["tree"]["sha"] = CHANGED_TREE
        self.assertEqual(collect(provider, 7, REVIEWED)["published_equals_supplied_reviewed_tree"], "different")
        self.assertEqual(collect(provider, 7)["published_equals_supplied_reviewed_tree"], UNKNOWN)

    def test_git_tree_modes_symlinks_names_and_deletions(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            def git(*args: str) -> str:
                return subprocess.check_output(["git", *args], cwd=root, text=True).strip()
            git("init", "-q")
            git("config", "user.email", "fixture@example.com")
            git("config", "user.name", "Fixture")
            git("config", "core.filemode", "true")
            script = root / "script.py"
            script.write_text("print('same bytes')\n")
            (root / "target-a").write_text("a\n")
            (root / "target-b").write_text("b\n")
            os.symlink("target-a", root / "link")
            git("add", "-A")
            git("commit", "-qm", "initial")
            original = git("rev-parse", "HEAD^{tree}")
            self.assertEqual(tree_comparison(original, original), "identical")
            script.chmod(0o755)
            git("add", "script.py")
            mode_tree = git("write-tree")
            self.assertEqual(script.read_text(), "print('same bytes')\n")
            self.assertEqual(tree_comparison(original, mode_tree), "different")
            (root / "link").unlink()
            os.symlink("target-b", root / "link")
            git("add", "link")
            self.assertNotEqual(mode_tree, git("write-tree"))
            (root / "target-a").unlink()
            git("add", "-A")
            deleted = git("write-tree")
            self.assertNotEqual(mode_tree, deleted)
            script.rename(root / "renamed.py")
            git("add", "-A")
            self.assertNotEqual(deleted, git("write-tree"))

    def test_linux_executable_audit_script(self):
        path = Path(__file__).resolve().parents[1] / "check_audit_complete.py"
        self.assertTrue(os.access(path, os.X_OK))
        mode = subprocess.check_output(["git", "ls-files", "--stage", str(path)], text=True)
        self.assertTrue(mode.startswith("100755 "))
        result = subprocess.run([str(path)], capture_output=True, text=True)
        # No sweep file was supplied: the gate documents usage and exits 1.
        # Reaching that branch proves the Linux kernel invoked this file.
        self.assertEqual(result.returncode, 1)
        self.assertIn("Usage:", result.stderr)

    def test_github_client_rejects_incomplete_check_page(self):
        prefix = f"https://api.github.com/repos/{REPO}/"
        def transport(url):
            if url.startswith(prefix + "commits/"):
                return {"total_count": 2, "check_runs": [{"id": 1}]}, {}
            raise AssertionError(url)
        client = GitHubClient(REPO, transport=transport)
        with self.assertRaises(EvidenceError):
            client.get_all(f"/commits/{HEAD}/check-runs?filter=all", key="check_runs")


if __name__ == "__main__":
    unittest.main()
