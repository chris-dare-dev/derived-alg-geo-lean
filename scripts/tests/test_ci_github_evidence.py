#!/usr/bin/env python3
"""Provider-response tests for the read-only GitHub evidence collector."""

from __future__ import annotations

import base64
import copy
import hashlib
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
        self.security_check: dict | None = None
        self.duplicate_security_check: dict | None = None
        self.security_setting: dict | None = {"pr_scan": "disabled"}
        self.dynamic_run: dict | None = None
        self.extra_dynamic_runs: list[dict] = []
        self.security_jobs: list[dict] = []
        self.statuses: list[dict] = []
        self.calls: list[str] = []
        self.move_head_on_recheck = False
        self.move_run_on_recheck = False
        self.move_security_setting_on_recheck = False
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
            "check_suite": {"id": 222},
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
            "status": check["status"],
            "conclusion": check["conclusion"],
        }

    def add_dynamic_scan(self, conclusion: str = "success") -> None:
        self.security_check = {
            **self._check("github-advanced-security", 900, conclusion),
            "check_suite": {"id": 333},
        }
        self.dynamic_run = {
            "id": 77777,
            "workflow_id": 360047049,
            "run_attempt": 1,
            "check_suite_id": 333,
            "name": "Code scanning AI findings on PR #7",
            "event": "dynamic",
            "path": "dynamic/agents/github-advanced-security",
            "head_sha": SHA_HEAD,
            "status": "completed",
            "conclusion": conclusion,
            "actor": {"id": 62310815, "login": "github-advanced-security[bot]"},
            "pull_requests": [],
        }
        self.security_jobs = [
            {
                **self._job(self.security_check, 1),
                "run_id": 77777,
            }
        ]

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
        if path == "/code-scanning/ai-scan":
            if self.security_setting is None:
                raise EvidenceError("AI Scan setting unavailable (403)")
            if self.move_security_setting_on_recheck and self.calls.count(url) > 1:
                return {"pr_scan": "enabled"}, {}
            return self.security_setting, {}
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
            runs = [self.run]
            if self.dynamic_run is not None:
                runs.append(self.dynamic_run)
            runs.extend(self.extra_dynamic_runs)
            return {"total_count": len(runs), "workflow_runs": runs}, {}
        if path == "/actions/runs/12345":
            return self.run, {}
        if self.dynamic_run is not None and path == f"/actions/runs/{self.dynamic_run['id']}":
            return self.dynamic_run, {}
        if self.dynamic_run is not None and path == f"/actions/runs/{self.dynamic_run['id']}/attempts/{self.dynamic_run['run_attempt']}/jobs":
            return {"total_count": len(self.security_jobs), "jobs": self.security_jobs}, {}
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
            if self.security_check is not None:
                suites.append(
                    {
                        "id": self.security_check["check_suite"]["id"],
                        "head_sha": SHA_HEAD,
                        "latest_check_runs_count": 1
                        + (self.duplicate_security_check is not None),
                        "app": {"id": 15368, "slug": "github-actions"},
                    }
                )
            if self.paginate_suites and "page=2" not in url:
                next_url = f"{BASE}{path}?per_page=100&page=2"
                return {"total_count": len(suites), "check_suites": []}, {
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
        if self.security_check is not None and path == f"/check-suites/{self.security_check['check_suite']['id']}/check-runs":
            checks = [self.security_check]
            if self.duplicate_security_check is not None:
                checks.append(self.duplicate_security_check)
            return {"total_count": len(checks), "check_runs": checks}, {}
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
    def test_current_v4_base_emits_v4_until_protected_policy_is_upgraded(self) -> None:
        fixture = ProviderFixture()
        fixture.inventory["schema_version"] = 4
        security = next(
            gate
            for gate in fixture.inventory["gates"]
            if gate["id"] == "github-advanced-security"
        )
        security["run_binding"] = "independent"
        security["platforms"] = ["github-actions"]
        fixture.security_check = {
            "id": 900,
            "name": "github-advanced-security",
            "head_sha": SHA_HEAD,
            "status": "completed",
            "conclusion": "success",
            "check_suite": {"id": 333},
            "app": {"id": 15368, "slug": "github-actions"},
        }
        result = collect(fixture.client(), 7)
        self.assertEqual(result["evidence"]["schema_version"], 4)
        self.assertNotIn(
            "github-advanced-security",
            [gate["id"] for gate in result["evidence"]["gates"]],
        )
        self.assertIn(fixture.security_check, result["observations"]["check_runs"])
        self.assertTrue(result["validation"]["claims"]["required_ci_verified"])
        self.assertFalse(result["validation"]["claims"]["auxiliary_checks_healthy"])
        self.assertFalse(result["validation"]["claims"]["all_pipelines_green"])

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
            inventory = (destination / "protected-inventory.json").read_bytes()
            protection = (destination / "live-protection.json").read_bytes()
            manifest = json.loads((destination / "bundle-manifest.json").read_bytes())
            self.assertEqual(json.loads(inventory), result["inventory"])
            self.assertEqual(json.loads(protection), fixture.protection)
            self.assertEqual(
                manifest["protected_inventory_sha256"],
                result["evidence"]["policy_binding"]["inventory_sha256"],
            )
            self.assertEqual(manifest["protected_inventory_size_bytes"], len(inventory))
            self.assertEqual(
                manifest["live_protection_sha256"],
                hashlib.sha256(protection).hexdigest(),
            )
            self.assertEqual(manifest["live_protection_size_bytes"], len(protection))
            result["inventory"] = {"changed": True}
            with self.assertRaisesRegex(EvidenceError, "retained inventory"):
                write_bundle(result, destination)
            result["inventory"] = json.loads(inventory)
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
        fixture.jobs[1][0]["conclusion"] = "failure"
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

    def test_dynamic_security_run_green_is_unknown_and_red_is_visible(self) -> None:
        fixture = ProviderFixture()
        fixture.add_dynamic_scan()
        green = collect(fixture.client(), 7)
        self.assertTrue(green["validation"]["claims"]["required_ci_verified"])
        self.assertFalse(green["validation"]["claims"]["auxiliary_checks_healthy"])
        self.assertFalse(green["validation"]["claims"]["all_pipelines_green"])
        gate = next(
            g
            for g in green["evidence"]["gates"]
            if g["id"] == "github-advanced-security"
        )
        self.assertEqual(gate["commit"], SHA_HEAD)
        self.assertEqual(gate["run_id"], 77777)
        self.assertEqual(gate["status"], "unknown")
        self.assertEqual(green["observations"]["security_scan"]["state"], "execution_observed_result_unknown")
        fixture.security_check["conclusion"] = "failure"
        fixture.dynamic_run["conclusion"] = "failure"
        fixture.security_jobs[0]["conclusion"] = "failure"
        red = collect(fixture.client(), 7)
        self.assertTrue(red["validation"]["claims"]["required_ci_verified"])
        self.assertFalse(red["validation"]["claims"]["auxiliary_checks_healthy"])
        self.assertFalse(red["validation"]["claims"]["all_pipelines_green"])
        self.assertEqual(red["observations"]["security_scan"]["state"], "unclassified_failure")

    def test_duplicate_dynamic_security_check_denies_claim(self) -> None:
        fixture = ProviderFixture()
        fixture.add_dynamic_scan()
        fixture.duplicate_security_check = {**fixture.security_check, "id": 901}
        with self.assertRaisesRegex(EvidenceError, "missing or ambiguous"):
            collect(fixture.client(), 7)

    def test_dynamic_security_absence_preserves_setting_uncertainty(self) -> None:
        fixture = ProviderFixture()
        for setting, state in (({"pr_scan": "disabled"}, "disabled_by_setting"),
                               ({"pr_scan": "enabled"}, "missing"),
                               (None, "provider_state_unknown")):
            with self.subTest(state=state):
                fixture.security_setting = setting
                result = collect(fixture.client(), 7)
                self.assertEqual(result["observations"]["security_scan"]["state"], state)
                self.assertFalse(result["validation"]["claims"]["auxiliary_checks_healthy"])
                self.assertTrue(result["validation"]["claims"]["required_ci_verified"])

    def test_wrong_dynamic_workflow_does_not_bind_same_named_check(self) -> None:
        fixture = ProviderFixture()
        fixture.add_dynamic_scan()
        fixture.dynamic_run["workflow_id"] = 123
        with self.assertRaisesRegex(EvidenceError, "missing or ambiguous"):
            collect(fixture.client(), 7)

    def test_ambiguous_dynamic_run_or_job_denies_claim(self) -> None:
        fixture = ProviderFixture()
        fixture.add_dynamic_scan()
        fixture.extra_dynamic_runs.append({**fixture.dynamic_run, "id": 77778})
        with self.assertRaisesRegex(EvidenceError, "missing or ambiguous"):
            collect(fixture.client(), 7)
        fixture.extra_dynamic_runs.clear()
        fixture.security_jobs.append(dict(fixture.security_jobs[0]))
        with self.assertRaisesRegex(EvidenceError, "no unique matching job"):
            collect(fixture.client(), 7)

    def test_dynamic_binding_rejects_wrong_protected_definition(self) -> None:
        fixture = ProviderFixture()
        fixture.add_dynamic_scan()
        security = next(g for g in fixture.inventory["gates"] if g["id"] == "github-advanced-security")
        security["producer"] = "github-actions/Unknown"
        with self.assertRaisesRegex(EvidenceError, "unrecognized dynamic security gate"):
            collect(fixture.client(), 7)

    def test_security_setting_change_denies_stale_absence(self) -> None:
        fixture = ProviderFixture()
        fixture.move_security_setting_on_recheck = True
        with self.assertRaisesRegex(EvidenceError, "AI Scan setting changed"):
            collect(fixture.client(), 7)

    def test_redacted_historical_dynamic_shapes_remain_unverified(self) -> None:
        source = ROOT / "scripts/tests/fixtures/github-advanced-security/dynamic-runs.json"
        records = json.loads(source.read_text())
        self.assertEqual({item["pr"] for item in records["runs"]}, {1415, 1419, 1424, 1427, 1426})
        for item in records["runs"]:
            with self.subTest(pr=item["pr"]):
                fixture = ProviderFixture()
                fixture.add_dynamic_scan(item["conclusion"])
                fixture.security_check["id"] = item["check_id"]
                fixture.security_check["check_suite"]["id"] = item["suite_id"]
                fixture.dynamic_run.update(
                    id=item["run_id"], workflow_id=records["workflow_id"],
                    check_suite_id=item["suite_id"], path=records["path"],
                    event=records["event"], actor=records["actor"],
                )
                fixture.security_jobs[0].update(
                    id=item["check_id"], run_id=item["run_id"],
                    check_run_url=f"{BASE}/check-runs/{item['check_id']}",
                )
                result = collect(fixture.client(), 7)
                gate = next(g for g in result["evidence"]["gates"] if g["id"] == "github-advanced-security")
                self.assertEqual(gate["provider_id"], str(item["check_id"]))
                self.assertEqual(gate["run_id"], item["run_id"])
                self.assertEqual(gate["conclusion"], item["conclusion"])
                self.assertEqual(gate["status"], "failed" if item["conclusion"] == "failure" else "unknown")
                self.assertFalse(result["validation"]["claims"]["auxiliary_checks_healthy"])
                if item["conclusion"] == "failure":
                    self.assertIn("HTTP 403", item["diagnostic"])
                else:
                    self.assertIn("no prompt or model session", item["diagnostic"])

    def test_conflicting_job_or_workflow_outcome_denies_claim(self) -> None:
        fixture = ProviderFixture()
        fixture.jobs[1][0]["conclusion"] = "failure"
        with self.assertRaisesRegex(EvidenceError, "outcomes conflict"):
            collect(fixture.client(), 7)
        fixture = ProviderFixture()
        fixture.run["conclusion"] = "failure"
        result = collect(fixture.client(), 7)
        self.assertFalse(result["validation"]["claims"]["required_ci_verified"])
        self.assertIn("workflow conclusion", result["validation"]["errors"][0])

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
        with self.assertRaisesRegex(EvidenceError, "current attempt"):
            collect(fixture.client(), 7)

    def test_rerun_selects_current_artifact_among_retained_older_artifacts(
        self,
    ) -> None:
        fixture = ProviderFixture()
        fixture.run["run_attempt"] = 2
        fixture.jobs[2] = [fixture._job(check, 2) for check in fixture.checks]
        earlier = {
            **fixture.artifacts[0],
            "id": 2,
            "created_at": "2026-09-23T08:00:00Z",
        }
        fixture.artifacts.append(earlier)
        result = collect(fixture.client(), 7)
        self.assertTrue(result["validation"]["claims"]["required_ci_verified"])
        self.assertEqual(len(result["observations"]["run_artifacts"]), 2)


if __name__ == "__main__":
    unittest.main()
