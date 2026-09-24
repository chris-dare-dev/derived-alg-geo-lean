#!/usr/bin/env python3
"""Provider-response tests for the read-only GitHub evidence collector."""

from __future__ import annotations

import base64
import copy
import json
import tempfile
import unittest
from pathlib import Path
from urllib.parse import urlsplit

from scripts.ci_github_evidence import (
    EvidenceError,
    GitHubClient,
    collect,
    write_bundle,
)


REPO = "chris-dare-dev/derived-alg-geo-lean"
BASE = f"https://api.github.com/repos/{REPO}"
ROOT = Path(__file__).resolve().parents[2]
INVENTORY = json.loads((ROOT / "scripts/ci_gate_inventory.json").read_text())
SHA_BASE = "a" * 40
SHA_HEAD = "b" * 40
SHA_MERGE = "c" * 40
SHA_TREE = "d" * 40
WORKFLOW = b"name: CI\nname: trust-artifacts-${{ github.sha }}\n"


class ProviderFixture:
    def __init__(self) -> None:
        self.base = SHA_BASE
        self.head = SHA_HEAD
        self.parents = [SHA_BASE, SHA_HEAD]
        self.pr_merge = SHA_MERGE
        self.inventory = copy.deepcopy(INVENTORY)
        self.candidate_inventory = copy.deepcopy(INVENTORY)
        self.protection = {
            "strict": True,
            "contexts": ["ci"],
            "checks": [{"context": "ci", "app_id": 15368}],
        }
        self.run = {
            "id": 12345,
            "run_number": 9,
            "run_attempt": 1,
            "check_suite_id": 222,
            "name": "CI",
            "event": "pull_request",
            "path": ".github/workflows/ci.yml",
            "head_sha": SHA_HEAD,
            "status": "completed",
            "conclusion": "success",
            "pull_requests": [
                {"number": 7, "base": {"sha": SHA_BASE}, "head": {"sha": SHA_HEAD}}
            ],
        }
        self.artifacts = [
            {
                "id": 1,
                "name": f"trust-artifacts-{SHA_MERGE}",
                "expired": False,
                "created_at": "2026-09-23T10:00:00Z",
                "workflow_run": {"id": 12345, "head_sha": SHA_HEAD},
            }
        ]
        self.workflow_base = WORKFLOW
        self.workflow_candidate = WORKFLOW
        self.checks = [
            self._check(name, 100 + i)
            for i, name in enumerate(("build", "roadmap", "ci"))
        ]
        self.jobs = {1: [self._job(check, 1) for check in self.checks]}
        self.statuses: list[dict] = []
        self.calls: list[str] = []
        self.move_head_on_recheck = False
        self.move_run_on_recheck = False
        self.paginate_suites = False
        self.paginate_statuses = False
        self.paginate_checks = False

    @staticmethod
    def _check(name: str, check_id: int, conclusion: str = "success") -> dict:
        return {
            "id": check_id,
            "name": name,
            "head_sha": SHA_HEAD,
            "status": "completed",
            "conclusion": conclusion,
            "app": {"id": 15368, "slug": "github-actions"},
        }

    @staticmethod
    def _job(check: dict, attempt: int) -> dict:
        return {
            "id": check["id"],
            "name": check["name"],
            "head_sha": SHA_HEAD,
            "run_id": 12345,
            "run_attempt": attempt,
            "check_run_url": f"{BASE}/check-runs/{check['id']}",
        }

    @staticmethod
    def _content(data: bytes) -> dict:
        return {
            "type": "file",
            "encoding": "base64",
            "size": len(data),
            "content": base64.b64encode(data).decode(),
        }

    def transport(self, url: str) -> tuple[object, dict]:
        self.calls.append(url)
        path = urlsplit(url).path.removeprefix(f"/repos/{REPO}")
        if path == "/branches/main":
            return {"name": "main", "protected": True, "commit": {"sha": self.base}}, {}
        if path == "/pulls/7":
            head = (
                "e" * 40
                if self.move_head_on_recheck and self.calls.count(url) > 1
                else self.head
            )
            if self.move_run_on_recheck and self.calls.count(url) > 1:
                self.run = {
                    **self.run,
                    "run_attempt": 2,
                    "status": "in_progress",
                    "conclusion": None,
                }
            return {
                "number": 7,
                "state": "open",
                "base": {"sha": self.base, "ref": "main"},
                "head": {"sha": head},
                "merge_commit_sha": self.pr_merge,
            }, {}
        if path == "/branches/main/protection/required_status_checks":
            return self.protection, {}
        if path == "/git/commits/" + SHA_MERGE:
            return {
                "sha": SHA_MERGE,
                "tree": {"sha": SHA_TREE},
                "parents": [{"sha": sha} for sha in self.parents],
            }, {}
        if path.startswith("/contents/"):
            target = path.removeprefix("/contents/")
            ref = urlsplit(url).query.removeprefix("ref=")
            if target == "scripts/ci_gate_inventory.json" and ref == SHA_BASE:
                return self._content(json.dumps(self.inventory).encode()), {}
            if target == "scripts/ci_gate_inventory.json" and ref == SHA_MERGE:
                return self._content(json.dumps(self.candidate_inventory).encode()), {}
            if target == ".github/workflows/ci.yml":
                return (
                    self._content(
                        self.workflow_base
                        if ref == SHA_BASE
                        else self.workflow_candidate
                    ),
                    {},
                )
            if (
                target in {"lean-toolchain", "lake-manifest.json", "pins.json"}
                and ref == SHA_MERGE
            ):
                return self._content(f"{target} fixture\n".encode()), {}
            raise EvidenceError(f"missing fixture Git blob {ref}:{target}")
        if path == "/actions/runs":
            return {"total_count": 1, "workflow_runs": [self.run]}, {}
        if path == "/actions/runs/12345":
            return self.run, {}
        if path == "/actions/runs/12345/artifacts":
            return {"total_count": len(self.artifacts), "artifacts": self.artifacts}, {}
        if path == "/actions/runs/12345/attempts/2":
            return {
                "id": 12345,
                "run_attempt": 2,
                "head_sha": SHA_HEAD,
                "run_started_at": "2026-09-23T09:00:00Z",
            }, {}
        if path.startswith("/actions/runs/12345/attempts/") and path.endswith("/jobs"):
            number = int(path.split("/")[-2])
            jobs = self.jobs[number]
            return {"total_count": len(jobs), "jobs": jobs}, {}
        if path == f"/commits/{SHA_HEAD}/check-suites":
            suites = [
                {
                    "id": 222,
                    "head_sha": SHA_HEAD,
                    "latest_check_runs_count": 3,
                    "app": {"id": 15368, "slug": "github-actions"},
                }
            ]
            if self.paginate_suites and "page=2" not in url:
                next_url = f"{BASE}{path}?per_page=100&page=2"
                return {"total_count": 1, "check_suites": []}, {
                    "Link": f'<{next_url}>; rel="next"'
                }
            return {"total_count": len(suites), "check_suites": suites}, {}
        if path == "/check-suites/222/check-runs":
            if self.paginate_checks and "page=2" not in url:
                next_url = f"{BASE}{path}?filter=all&per_page=100&page=2"
                return {"total_count": len(self.checks), "check_runs": []}, {
                    "Link": f'<{next_url}>; rel="next"'
                }
            return {"total_count": len(self.checks), "check_runs": self.checks}, {}
        if path == f"/commits/{SHA_HEAD}/statuses":
            if self.paginate_statuses and "page=2" not in url:
                next_url = f"{BASE}{path}?per_page=100&page=2"
                return [], {"Link": f'<{next_url}>; rel="next"'}
            return self.statuses, {}
        raise AssertionError(f"unexpected fixture request: {url}")

    def client(self) -> GitHubClient:
        return GitHubClient(REPO, transport=self.transport)


class ClientTests(unittest.TestCase):
    def test_reads_multiple_pages_and_checks_total(self) -> None:
        first = f"{BASE}/commits/example/check-suites?per_page=100"
        second = f"{first}&page=2"
        responses = {
            first: (
                {"total_count": 2, "check_suites": [{"id": 1}]},
                {"Link": f'<{second}>; rel="next"'},
            ),
            second: ({"total_count": 2, "check_suites": [{"id": 2}]}, {}),
        }
        client = GitHubClient(REPO, transport=responses.__getitem__)
        self.assertEqual(
            [
                item["id"]
                for item in client.get_all(
                    "/commits/example/check-suites", key="check_suites"
                )
            ],
            [1, 2],
        )

    def test_truncated_page_denies_completion(self) -> None:
        client = GitHubClient(
            REPO,
            transport=lambda _: ({"total_count": 2, "check_runs": [{"id": 1}]}, {}),
        )
        with self.assertRaisesRegex(EvidenceError, "truncated"):
            client.get_all("/check-suites/1/check-runs", key="check_runs")

    def test_malformed_and_rate_limited_responses_fail_closed(self) -> None:
        client = GitHubClient(REPO, transport=lambda _: ([], {}))
        with self.assertRaisesRegex(EvidenceError, "malformed"):
            client.get_object("/branches/main")

        def rate_limited(_: str):
            raise EvidenceError("GitHub API rate limit (403)")

        client = GitHubClient(REPO, transport=rate_limited)
        with self.assertRaisesRegex(EvidenceError, "rate limit"):
            client.get_all("/statuses/example")

    def test_link_cannot_leave_repository_or_cycle(self) -> None:
        first = f"{BASE}/statuses/example?per_page=100"
        escaping = GitHubClient(
            REPO,
            transport=lambda _: (
                [{"id": 1}],
                {"link": '<https://example.org/>; rel="next"'},
            ),
        )
        with self.assertRaisesRegex(EvidenceError, "changed resource path"):
            escaping.get_all("/statuses/example")
        cycling = GitHubClient(
            REPO, transport=lambda _: ([{"id": 1}], {"link": f'<{first}>; rel="next"'})
        )
        with self.assertRaisesRegex(EvidenceError, "pagination loop"):
            cycling.get_all("/statuses/example")


class CollectorTests(unittest.TestCase):
    def test_exact_merge_candidate_and_real_payload_hashes(self) -> None:
        fixture = ProviderFixture()
        result = collect(fixture.client(), 7)
        self.assertTrue(result["validation"]["claims"]["required_ci_verified"])
        self.assertEqual(result["evidence"]["candidate_commit"], SHA_MERGE)
        self.assertEqual(result["evidence"]["candidate_tree"], SHA_TREE)
        self.assertEqual(len(result["evidence"]["artifacts"]), 3)
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary)
            write_bundle(result, destination)
            self.assertTrue((destination / "source-observations.json").is_file())
            result["payloads"]["results/check-run-100.json"] = b"tampered"
            with self.assertRaisesRegex(EvidenceError, "do not match"):
                write_bundle(result, destination)

    def test_moving_head_denies_current_claim(self) -> None:
        fixture = ProviderFixture()
        fixture.move_head_on_recheck = True
        with self.assertRaisesRegex(EvidenceError, "moved"):
            collect(fixture.client(), 7)

    def test_moving_base_denies_current_claim(self) -> None:
        fixture = ProviderFixture()
        original = fixture.transport

        def moving_base(url: str):
            if url.endswith("/branches/main") and fixture.calls.count(url) > 0:
                return {
                    "name": "main",
                    "protected": True,
                    "commit": {"sha": "e" * 40},
                }, {}
            return original(url)

        with self.assertRaisesRegex(EvidenceError, "base differs"):
            collect(GitHubClient(REPO, transport=moving_base), 7)

    def test_new_attempt_during_collection_denies_stale_green(self) -> None:
        fixture = ProviderFixture()
        fixture.move_run_on_recheck = True
        with self.assertRaisesRegex(EvidenceError, "not completed"):
            collect(fixture.client(), 7)

    def test_separate_older_ci_run_cannot_be_superseded_by_new_green_run(self) -> None:
        fixture = ProviderFixture()
        old = {**fixture.run, "id": 12344, "run_number": 8, "conclusion": "failure"}
        original = fixture.transport

        def extra_run(url: str):
            if urlsplit(url).path == f"/repos/{REPO}/actions/runs":
                return {"total_count": 2, "workflow_runs": [old, fixture.run]}, {}
            return original(url)

        with self.assertRaisesRegex(EvidenceError, "one distinct CI workflow run"):
            collect(GitHubClient(REPO, transport=extra_run), 7)

    def test_unproved_parent_or_missing_artifact_denies(self) -> None:
        fixture = ProviderFixture()
        fixture.parents = [SHA_BASE, "f" * 40]
        with self.assertRaisesRegex(EvidenceError, "not the current"):
            collect(fixture.client(), 7)
        fixture = ProviderFixture()
        fixture.artifacts = []
        with self.assertRaisesRegex(EvidenceError, "lacks one"):
            collect(fixture.client(), 7)
        fixture = ProviderFixture()
        fixture.pr_merge = "e" * 40
        with self.assertRaisesRegex(EvidenceError, "differs from current PR merge"):
            collect(fixture.client(), 7)

    def test_changed_workflow_or_missing_pin_denies(self) -> None:
        fixture = ProviderFixture()
        fixture.workflow_candidate = b"name: changed\n"
        with self.assertRaisesRegex(EvidenceError, "workflow changed"):
            collect(fixture.client(), 7)
        fixture = ProviderFixture()
        fixture.transport_original = fixture.transport

        def missing_pin(url: str):
            if "/contents/pins.json?" in url:
                raise EvidenceError("missing fixture Git blob pins.json")
            return fixture.transport_original(url)

        with self.assertRaisesRegex(EvidenceError, "missing fixture Git blob"):
            collect(GitHubClient(REPO, transport=missing_pin), 7)

    def test_protected_inventory_ignores_candidate_edit_and_requires_known_context(
        self,
    ) -> None:
        fixture = ProviderFixture()
        fixture.candidate_inventory["gates"] = []
        self.assertTrue(
            collect(fixture.client(), 7)["validation"]["claims"]["required_ci_verified"]
        )
        fixture = ProviderFixture()
        fixture.protection["contexts"].append("unknown-required")
        with self.assertRaisesRegex(EvidenceError, "unaccounted protected context"):
            collect(fixture.client(), 7)
        fixture = ProviderFixture()
        original = fixture.transport

        def inaccessible_policy(url: str):
            if url.endswith("/branches/main/protection/required_status_checks"):
                raise EvidenceError("GitHub API HTTP 403")
            return original(url)

        with self.assertRaisesRegex(EvidenceError, "403"):
            collect(GitHubClient(REPO, transport=inaccessible_policy), 7)
        fixture = ProviderFixture()
        fixture.protection["checks"] = [
            {"context": "ci", "app_id": 24680},
            {"context": "ci", "app_id": 15368},
        ]
        with self.assertRaisesRegex(EvidenceError, "duplicate required check"):
            collect(fixture.client(), 7)

    def test_required_red_and_auxiliary_red_are_distinct(self) -> None:
        fixture = ProviderFixture()
        fixture.checks[0]["conclusion"] = "failure"
        denied = collect(fixture.client(), 7)
        self.assertFalse(denied["validation"]["claims"]["required_ci_verified"])
        self.assertEqual(denied["evidence"]["gates"][0]["status"], "failed")
        fixture = ProviderFixture()
        fixture.statuses = [
            {
                "id": 999,
                "context": "build",
                "sha": SHA_HEAD,
                "state": "failure",
                "creator": {"login": "other"},
            }
        ]
        result = collect(fixture.client(), 7)
        self.assertTrue(result["validation"]["claims"]["required_ci_verified"])
        self.assertFalse(result["validation"]["claims"]["all_pipelines_green"])
        self.assertEqual(result["observations"]["statuses"][0]["state"], "failure")

    def test_suites_and_statuses_follow_all_pages(self) -> None:
        fixture = ProviderFixture()
        fixture.paginate_suites = True
        fixture.paginate_statuses = True
        fixture.paginate_checks = True
        fixture.statuses = [
            {"id": 999, "context": "build", "sha": SHA_HEAD, "state": "failure"}
        ]
        result = collect(fixture.client(), 7)
        self.assertTrue(result["validation"]["claims"]["required_ci_verified"])
        self.assertEqual(
            [suite["id"] for suite in result["observations"]["suites"]], [222]
        )
        self.assertEqual(
            [check["id"] for check in result["observations"]["check_runs"]],
            [100, 101, 102],
        )
        self.assertEqual(
            [status["id"] for status in result["observations"]["statuses"]], [999]
        )
        self.assertEqual(sum("page=2" in call for call in fixture.calls), 3)

    def test_ambiguous_same_name_current_jobs_denies(self) -> None:
        fixture = ProviderFixture()
        fixture.jobs[1].append(
            {**fixture.jobs[1][0], "id": 888, "check_run_url": f"{BASE}/check-runs/888"}
        )
        with self.assertRaisesRegex(EvidenceError, "ambiguous current workflow jobs"):
            collect(fixture.client(), 7)

    def test_successful_rerun_uses_current_attempt_and_retains_history(self) -> None:
        fixture = ProviderFixture()
        fixture.run["run_attempt"] = 2
        previous = [
            fixture._check(name, 200 + i, "failure")
            for i, name in enumerate(("build", "roadmap", "ci"))
        ]
        fixture.checks.extend(previous)
        fixture.jobs[1] = [fixture._job(check, 1) for check in previous]
        fixture.jobs[2] = [fixture._job(check, 2) for check in fixture.checks[:3]]
        result = collect(fixture.client(), 7)
        self.assertTrue(result["validation"]["claims"]["required_ci_verified"])
        self.assertEqual(
            {gate["run_attempt"] for gate in result["evidence"]["gates"]}, {2}
        )
        self.assertEqual(len(result["observations"]["attempt_jobs"][1]), 3)
        fixture.artifacts[0]["created_at"] = "2026-09-23T08:00:00Z"
        with self.assertRaisesRegex(EvidenceError, "cannot be bound"):
            collect(fixture.client(), 7)


if __name__ == "__main__":
    unittest.main()
