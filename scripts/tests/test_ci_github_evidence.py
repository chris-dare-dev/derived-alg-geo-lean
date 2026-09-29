#!/usr/bin/env python3
"""Provider-response tests for the read-only GitHub evidence collector."""

from __future__ import annotations

import base64
import copy
import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from urllib.parse import urlsplit

from scripts.ci_github_evidence import (
    EvidenceError,
    GitHubClient,
    collect,
    collect_post_merge_health,
    collect_publication,
    verify_publication_provider_evidence,
    write_bundle,
)
from scripts import ci_contract, ci_publication

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


class PublicationClient:
    def __init__(self, *, published_tree: str = SHA_TREE, conclusion: str = "success") -> None:
        self.repository = REPO
        self._prefix = BASE + "/"
        self.base = SHA_BASE
        self.head = SHA_HEAD
        self.reviewed = SHA_HEAD
        self.candidate = SHA_MERGE
        self.published = "e" * 40
        self.tree = published_tree
        self.conclusion = conclusion
        self.pull_reads = 0
        self.race_on_final_read = False
        self.pre_provider = ProviderFixture()
        self.pre_provider.add_dynamic_scan("failure")
        self.run = {
            "id": 909,
            "name": "CI",
            "run_attempt": 1,
            "check_suite_id": 910,
            "head_sha": self.published,
            "event": "push",
            "path": ".github/workflows/ci.yml",
            "status": "completed",
            "conclusion": conclusion,
            "html_url": f"https://github.com/{REPO}/actions/runs/909",
        }

    def get_object(self, path: str) -> dict:
        if path == "/pulls/7":
            self.pull_reads += 1
            head = "f" * 40 if self.race_on_final_read and self.pull_reads > 1 else self.head
            return {
                "number": 7,
                "state": "closed",
                "merged": True,
                "merge_commit_sha": self.published,
                "html_url": f"https://github.com/{REPO}/pull/7",
                "base": {"sha": self.base},
                "head": {"sha": head},
            }
        if path.startswith("/git/commits/"):
            sha = path.rsplit("/", 1)[-1]
            records = {
                self.reviewed: {
                    "sha": self.reviewed, "tree": {"sha": SHA_TREE},
                    "parents": [{"sha": self.base}],
                },
                self.head: {
                    "sha": self.head, "tree": {"sha": SHA_TREE},
                    "parents": [{"sha": self.base}],
                },
                self.candidate: {
                    "sha": self.candidate, "tree": {"sha": SHA_TREE},
                    "parents": [{"sha": self.base}, {"sha": self.head}],
                },
                self.published: {
                    "sha": self.published, "tree": {"sha": self.tree},
                    "parents": [{"sha": self.base}, {"sha": self.head}],
                },
            }
            if sha in records:
                return records[sha]
        if path == "/actions/runs/909":
            return self.run
        return self.pre_provider.transport(BASE + path)[0]

    def get_all(self, path: str, *, key: str | None = None) -> list[dict]:
        if path == f"/actions/runs?head_sha={self.published}":
            return [self.run]
        response, _ = self.pre_provider.transport(BASE + path)
        if isinstance(response, dict):
            if key is None:
                raise AssertionError(f"unexpected unkeyed list fixture response: {path}")
            return response[key]
        if isinstance(response, list):
            return response
        raise AssertionError(f"unexpected list response: {path}")

    def _get(self, url: str):
        raise AssertionError(f"unexpected comparison request: {url}")


def publication_inputs(client: PublicationClient) -> tuple[dict, dict]:
    collected = collect(client.pre_provider.client(), 7)
    observations = {
        "workflow_run": collected["observations"]["workflow_run"],
        "suites": collected["observations"]["suites"],
        "check_runs": collected["observations"]["check_runs"],
        "statuses": collected["observations"]["statuses"],
    }
    readiness = ci_publication.evaluate_merge_readiness(
        {
            "state": "OPEN",
            "isDraft": False,
            "baseRefOid": client.base,
            "headRefOid": client.head,
            "mergeStateStatus": "CLEAN",
            "reviewDecision": "APPROVED",
        },
        checked_base=client.base,
        checked_head=client.head,
        reviewed_tree=SHA_TREE,
        head_tree=SHA_TREE,
        required_ci_verified=True,
    )
    return {
        "evidence": collected["evidence"],
        "validation": collected["validation"],
        "observations": observations,
        "inventory": collected["inventory"],
        "payloads": collected["payloads"],
    }, readiness


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
        pages = client.get_pages("/commits/example/check-suites", key="check_suites")
        self.assertEqual([page["request_url"] for page in pages], [first, second])
        self.assertEqual(pages[0]["response_headers"]["link"], f'<{second}>; rel="next"')
        self.assertEqual(pages[0]["pagination_links"]["next"], second)
        self.assertEqual([page["response"]["total_count"] for page in pages], [2, 2])

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
                self.assertEqual(result["evidence"]["security_scan"]["state"], state)
                self.assertTrue(any(
                    f"github-advanced-security is {state}" in warning
                    for warning in result["validation"]["warnings"]
                ))
                self.assertFalse(result["validation"]["claims"]["auxiliary_checks_healthy"])
                self.assertTrue(result["validation"]["claims"]["required_ci_verified"])

    def test_queued_dynamic_run_without_check_is_visible_and_optional(self) -> None:
        fixture = ProviderFixture()
        fixture.add_dynamic_scan()
        fixture.security_setting = {"pr_scan": "enabled"}
        fixture.security_check = None
        fixture.security_jobs = []
        fixture.dynamic_run.update(status="queued", conclusion=None)

        result = collect(fixture.client(), 7)
        scan = result["observations"]["security_scan"]
        self.assertEqual(scan["state"], "pending")
        self.assertEqual(scan["run_id"], 77777)
        self.assertEqual(scan["matching_check_ids"], [])
        self.assertEqual(result["evidence"]["security_scan"]["state"], "pending")
        self.assertTrue(result["validation"]["claims"]["required_ci_verified"])
        self.assertFalse(result["validation"]["claims"]["auxiliary_checks_healthy"])
        self.assertTrue(any(
            "github-advanced-security is pending" in warning
            for warning in result["validation"]["warnings"]
        ))
        self.assertFalse(any(
            "github-advanced-security is missing" in warning
            for warning in result["validation"]["warnings"]
        ))
        self.assertFalse(any(
            gate["id"] == "github-advanced-security" for gate in result["evidence"]["gates"]
        ))

        fixture.dynamic_run.update(status="completed", conclusion="success")
        with self.assertRaisesRegex(EvidenceError, "missing or ambiguous"):
            collect(fixture.client(), 7)

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


class PublicationTests(unittest.TestCase):
    def collect(self, client: PublicationClient) -> dict:
        premerge, readiness = publication_inputs(client)
        return collect_publication(
            client, 7, reviewed_commit=client.reviewed, reviewed_tree=SHA_TREE,
            premerge=premerge, merge_readiness=readiness,
        )

    def test_exact_publication_receipt_binds_tree_commit_parents_and_post_merge_health(self) -> None:
        passed = self.collect(PublicationClient(conclusion="success"))
        ci_publication.verify_receipt(passed)
        self.assertEqual(passed["publication"]["commit"], "e" * 40)
        self.assertEqual(passed["publication"]["tree"], SHA_TREE)
        self.assertEqual(passed["publication"]["parents"], [SHA_BASE, SHA_HEAD])
        self.assertTrue(passed["claims"]["operationally_verified"])
        self.assertFalse(passed["claims"]["auxiliary_checks_healthy"])
        self.assertFalse(passed["claims"]["all_pipelines_green"])

        failed = self.collect(PublicationClient(conclusion="failure"))
        ci_publication.verify_receipt(failed)
        self.assertEqual(failed["claims"]["post_merge_health"], "failed")
        self.assertFalse(failed["claims"]["operationally_verified"])

    def test_publication_rejects_incomplete_tree_and_provider_identity_race(self) -> None:
        with self.assertRaisesRegex(EvidenceError, "published tree differs"):
            self.collect(PublicationClient(published_tree="9" * 40))

        raced = PublicationClient()
        raced.race_on_final_read = True
        with self.assertRaisesRegex(EvidenceError, "identity changed"):
            self.collect(raced)

    def test_publication_rejects_same_blob_with_changed_mode_and_deleted_tree_entry(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repository = Path(temporary)
            subprocess.run(
                ["git", "init", "--quiet", "--bare", str(repository)], check=True
            )
            blob = subprocess.run(
                ["git", "-C", str(repository), "hash-object", "-w", "--stdin"],
                input=b"same audit checker bytes\n",
                check=True,
                capture_output=True,
            ).stdout.decode().strip()

            def tree_with(entries: bytes) -> str:
                return subprocess.run(
                    ["git", "-C", str(repository), "mktree"],
                    input=entries,
                    check=True,
                    capture_output=True,
                ).stdout.decode().strip()

            reviewed_tree = tree_with(
                f"100755 blob {blob}\tcheck_audit_complete.py\n".encode()
            )
            mode_regressed_tree = tree_with(
                f"100644 blob {blob}\tcheck_audit_complete.py\n".encode()
            )
            symlink_blob = subprocess.run(
                ["git", "-C", str(repository), "hash-object", "-w", "--stdin"],
                input=b"check_audit_complete.py",
                check=True,
                capture_output=True,
            ).stdout.decode().strip()
            symlink_tree = tree_with(
                f"120000 blob {symlink_blob}\tlinked_checker\n".encode()
            )
            deleted_entry_tree = subprocess.run(
                ["git", "-C", str(repository), "mktree"],
                input=b"",
                check=True,
                capture_output=True,
            ).stdout.decode().strip()
            self.assertNotEqual(reviewed_tree, mode_regressed_tree)
            self.assertNotEqual(reviewed_tree, symlink_tree)
            self.assertNotEqual(reviewed_tree, deleted_entry_tree)

        for published_tree in (mode_regressed_tree, symlink_tree, deleted_entry_tree):
            client = PublicationClient(published_tree=published_tree)
            with self.assertRaisesRegex(EvidenceError, "published tree differs"):
                self.collect(client)

    @staticmethod
    def resign_receipt(receipt: dict) -> None:
        receipt["receipt_sha256"] = ci_publication.receipt_digest(receipt)

    @staticmethod
    def flatten_contract_gates(receipt: dict) -> None:
        premerge = receipt["premerge"]
        evidence = premerge["contract_evidence"]
        definitions = {gate["id"]: gate for gate in INVENTORY["gates"]}
        premerge["gates"] = [
            {
                "id": gate["id"],
                "name": gate["name"],
                "provider_id": gate["provider_id"],
                "commit": gate["commit"],
                "status": gate["status"],
                "conclusion": gate["conclusion"],
                "class": definitions[gate["id"]]["class"],
                "required": definitions[gate["id"]]["required"],
            }
            for gate in evidence["gates"]
        ]

    def test_provider_verifier_rejects_omitted_required_gate_even_after_rehash(self) -> None:
        client = PublicationClient()
        receipt = self.collect(client)
        evidence = receipt["premerge"]["contract_evidence"]
        evidence["gates"] = [gate for gate in evidence["gates"] if gate["id"] != "build"]
        self.flatten_contract_gates(receipt)
        receipt["premerge"]["required_gate_ids"] = []
        self.resign_receipt(receipt)

        with self.assertRaisesRegex(EvidenceError, "CI1.01 evidence is invalid"):
            verify_publication_provider_evidence(client, receipt)

    def test_provider_verifier_rejects_omitted_failed_auxiliary_gate_even_after_rehash(self) -> None:
        client = PublicationClient()
        receipt = self.collect(client)
        premerge = receipt["premerge"]
        evidence = premerge["contract_evidence"]
        gate = next(item for item in evidence["gates"] if item["id"] == "github-advanced-security")
        artifact_refs = set(gate["artifact_refs"])
        evidence["gates"] = [item for item in evidence["gates"] if item is not gate]
        evidence["artifacts"] = [
            item for item in evidence["artifacts"] if item["id"] not in artifact_refs
        ]
        self.flatten_contract_gates(receipt)
        premerge["applicable_auxiliary_gate_ids"] = []
        for claims in (premerge["claims"], receipt["claims"]):
            claims["auxiliary_checks_healthy"] = True
            claims["all_pipelines_green"] = True
        self.resign_receipt(receipt)

        with self.assertRaises(EvidenceError):
            verify_publication_provider_evidence(client, receipt)

    def test_dynamic_publication_verifier_rechecks_run_job_and_payload(self) -> None:
        client = PublicationClient()
        receipt = self.collect(client)
        artifact = next(
            item for item in receipt["premerge"]["contract_evidence"]["artifacts"]
            if item["subject"] == "github-advanced-security"
        )
        payloads = receipt["premerge"]["artifact_payloads"]
        payload = json.loads(payloads[artifact["path"]])
        payload["job"]["run_id"] = 987654
        content = (
            json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            + "\n"
        ).encode("utf-8")
        payloads[artifact["path"]] = content.decode("utf-8")
        artifact["sha256"] = hashlib.sha256(content).hexdigest()
        artifact["size_bytes"] = len(content)
        self.resign_receipt(receipt)
        with self.assertRaisesRegex(EvidenceError, "retained dynamic job differs"):
            verify_publication_provider_evidence(client, receipt)

        client = PublicationClient()
        receipt = self.collect(client)
        client.pre_provider.dynamic_run["actor"]["id"] = 1
        with self.assertRaisesRegex(EvidenceError, "head-run query differs from GitHub"):
            verify_publication_provider_evidence(client, receipt)

    def test_dynamic_publication_rejects_retained_setting_contradiction(self) -> None:
        client = PublicationClient()
        receipt = self.collect(client)
        artifact = next(
            item for item in receipt["premerge"]["contract_evidence"]["artifacts"]
            if item["subject"] == "github-advanced-security"
        )
        payloads = receipt["premerge"]["artifact_payloads"]
        payload = json.loads(payloads[artifact["path"]])
        self.assertEqual(payload["setting"]["response"]["pr_scan"], "disabled")
        payload["setting"]["state"] = "enabled"
        content = (
            json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            + "\n"
        ).encode("utf-8")
        payloads[artifact["path"]] = content.decode("utf-8")
        artifact["sha256"] = hashlib.sha256(content).hexdigest()
        artifact["size_bytes"] = len(content)
        self.resign_receipt(receipt)

        with self.assertRaisesRegex(EvidenceError, "contradicts its raw provider response"):
            verify_publication_provider_evidence(client, receipt)

    def test_rehashed_dynamic_artifact_setting_must_equal_verified_scan(self) -> None:
        client = PublicationClient()
        receipt = self.collect(client)
        artifact = next(
            item for item in receipt["premerge"]["contract_evidence"]["artifacts"]
            if item["subject"] == "github-advanced-security"
        )
        payloads = receipt["premerge"]["artifact_payloads"]
        payload = json.loads(payloads[artifact["path"]])
        payload["setting"]["state"] = "enabled"
        payload["setting"]["response"] = {"pr_scan": "enabled"}
        content = (
            json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            + "\n"
        ).encode("utf-8")
        payloads[artifact["path"]] = content.decode("utf-8")
        artifact["sha256"] = hashlib.sha256(content).hexdigest()
        artifact["size_bytes"] = len(content)
        self.resign_receipt(receipt)
        with self.assertRaisesRegex(EvidenceError, "artifact setting differs"):
            verify_publication_provider_evidence(client, receipt)

    def test_pending_scan_attempt_is_bound_to_retained_and_live_run(self) -> None:
        client = PublicationClient()
        client.pre_provider.add_dynamic_scan("failure")
        client.pre_provider.security_check = None
        client.pre_provider.security_jobs = []
        client.pre_provider.dynamic_run["status"] = "queued"
        client.pre_provider.dynamic_run["conclusion"] = None
        receipt = self.collect(client)
        scan = receipt["premerge"]["contract_evidence"]["security_scan"]
        self.assertEqual(scan["state"], "pending")
        verify_publication_provider_evidence(client, receipt)
        scan["run_attempt"] = 999
        self.resign_receipt(receipt)
        with self.assertRaisesRegex(EvidenceError, "pending run differs"):
            verify_publication_provider_evidence(client, receipt)

    def test_gate_present_scan_cannot_invent_run_status(self) -> None:
        for status in ("queued", "completed"):
            with self.subTest(status=status):
                client = PublicationClient()
                receipt = self.collect(client)
                receipt["premerge"]["contract_evidence"]["security_scan"]["run_status"] = status
                self.resign_receipt(receipt)
                with self.assertRaisesRegex(EvidenceError, "CI1.01 evidence is invalid"):
                    verify_publication_provider_evidence(client, receipt)

    def test_dynamic_run_projection_ignores_unrelated_provider_field(self) -> None:
        client = PublicationClient()
        receipt = self.collect(client)
        client.pre_provider.dynamic_run["new_api_field"] = {"provider_added": True}
        verify_publication_provider_evidence(client, receipt)
        client.pre_provider.dynamic_run["run_attempt"] = 2
        with self.assertRaisesRegex(EvidenceError, "head-run query differs"):
            verify_publication_provider_evidence(client, receipt)

    def test_postmerge_primary_association_loss_keeps_stable_scan_receipt(self) -> None:
        client = PublicationClient()
        receipt = self.collect(client)
        client.pre_provider.run["pull_requests"] = []
        verify_publication_provider_evidence(client, receipt)
        client.pre_provider.run["run_attempt"] = 2
        with self.assertRaises(EvidenceError):
            verify_publication_provider_evidence(client, receipt)

        client = PublicationClient()
        receipt = self.collect(client)
        retained_runs = receipt["premerge"]["contract_evidence"]["security_scan"]["head_workflow_runs"]
        primary = next(run for run in retained_runs if run["id"] == client.pre_provider.run["id"])
        primary["pull_requests"][0]["number"] = 8
        client.pre_provider.run["pull_requests"] = []
        self.resign_receipt(receipt)
        with self.assertRaisesRegex(EvidenceError, "head-run query differs"):
            verify_publication_provider_evidence(client, receipt)

    def test_absent_scan_state_survives_receipt_and_provider_reread(self) -> None:
        client = PublicationClient()
        client.pre_provider.security_check = None
        client.pre_provider.dynamic_run = None
        client.pre_provider.security_jobs = []
        receipt = self.collect(client)
        scan = receipt["premerge"]["contract_evidence"]["security_scan"]
        self.assertEqual(scan["state"], "disabled_by_setting")
        self.assertEqual(scan["matching_run_ids"], [])
        self.assertEqual(scan["matching_check_ids"], [])
        verify_publication_provider_evidence(client, receipt)

        client.pre_provider.security_setting = {"pr_scan": "enabled"}
        with self.assertRaisesRegex(EvidenceError, "setting differs from the current provider"):
            verify_publication_provider_evidence(client, receipt)

    def test_provider_verifier_rejects_forged_candidate_and_copied_pr_association(self) -> None:
        client = PublicationClient()
        receipt = self.collect(client)
        premerge = receipt["premerge"]
        evidence = premerge["contract_evidence"]
        forged = "9" * 40
        evidence["candidate_commit"] = forged
        evidence["revision_binding"]["candidate_commit"] = forged
        evidence["provider_binding"]["commit"] = forged
        proof_body = {
            key: value
            for key, value in evidence["provider_binding"].items()
            if key != "proof_sha256"
        }
        evidence["provider_binding"]["proof_sha256"] = ci_contract._canonical_sha256(
            proof_body
        )
        for gate in evidence["gates"]:
            if gate["id"] != "github-advanced-security":
                gate["commit"] = forged
        for artifact in evidence["artifacts"]:
            if artifact["subject"] != "github-advanced-security":
                artifact["commit"] = forged
        premerge["candidate_commit"] = forged
        premerge["provider_binding"] = evidence["provider_binding"]
        premerge["provider_proof_sha256"] = evidence["provider_binding"]["proof_sha256"]
        self.flatten_contract_gates(receipt)
        self.resign_receipt(receipt)

        with self.assertRaisesRegex(EvidenceError, "candidate differs"):
            verify_publication_provider_evidence(client, receipt)

        associated = PublicationClient()
        associated_receipt = self.collect(associated)
        associated.pre_provider.run["pull_requests"] = [
            {"number": 8, "base": {"sha": "f" * 40}, "head": {"sha": "1" * 40}}
        ]
        self.resign_receipt(associated_receipt)
        with self.assertRaisesRegex(EvidenceError, "associated with a different"):
            verify_publication_provider_evidence(associated, associated_receipt)

    def test_provider_verifier_rejects_forged_toolchain_pins_and_artifact_digests(self) -> None:
        fields = ("toolchain", "pins", "artifact-sha256", "artifact-size", "artifact-payload")
        for field in fields:
            with self.subTest(field=field):
                client = PublicationClient()
                receipt = self.collect(client)
                evidence = receipt["premerge"]["contract_evidence"]
                if field == "toolchain":
                    evidence["toolchain"] = "forged toolchain"
                elif field == "pins":
                    evidence["pins"] = {
                        path: "0" * 64 for path in ci_contract.REQUIRED_PINS
                    }
                elif field == "artifact-sha256":
                    for artifact in evidence["artifacts"]:
                        artifact["sha256"] = "0" * 64
                elif field == "artifact-size":
                    for artifact in evidence["artifacts"]:
                        artifact["size_bytes"] = 1
                else:
                    artifact = evidence["artifacts"][0]
                    payloads = receipt["premerge"]["artifact_payloads"]
                    payload = json.loads(payloads[artifact["path"]])
                    payload["check_run"]["conclusion"] = "failure"
                    content = (
                        json.dumps(
                            payload,
                            sort_keys=True,
                            separators=(",", ":"),
                            ensure_ascii=False,
                        )
                        + "\n"
                    ).encode("utf-8")
                    payloads[artifact["path"]] = content.decode("utf-8")
                    artifact["sha256"] = hashlib.sha256(content).hexdigest()
                    artifact["size_bytes"] = len(content)
                self.resign_receipt(receipt)

                message = (
                    "candidate Git blob|candidate Git blobs|CI1.01 artifact|"
                    "retained CI1.01 artifact"
                )
                with self.assertRaisesRegex(EvidenceError, message):
                    verify_publication_provider_evidence(client, receipt)

    def test_provider_verifier_rejects_rehashed_contradictory_ready_claim(self) -> None:
        client = PublicationClient()
        receipt = self.collect(client)
        receipt["merge_readiness"].update(
            {
                "checked_base": "9" * 40,
                "checked_head": "8" * 40,
                "head_tree": "7" * 40,
                "merge_state": "BLOCKED",
                "reasons": ["merge is blocked"],
            }
        )
        self.resign_receipt(receipt)

        with self.assertRaisesRegex(ci_publication.PublicationError, "ready merge readiness"):
            verify_publication_provider_evidence(client, receipt)

    def test_post_merge_health_is_not_inferred_from_a_pr_check_or_missing_run(self) -> None:
        client = PublicationClient()
        client.run["event"] = "pull_request"
        self.assertEqual(
            collect_post_merge_health(client, client.published)["status"], "pending"
        )

    def test_checked_in_pr1500_receipt_keeps_historical_unknowns_explicit(self) -> None:
        path = ROOT / "scripts/tests/fixtures/ci_contract/publication-receipt-pr1500.json"
        receipt = json.loads(path.read_text(encoding="utf-8"))
        ci_publication.verify_receipt(receipt)
        self.assertEqual(receipt["publication"]["commit"], "767a363943e83b933799b3a57c8e48cc62801284")
        self.assertEqual(receipt["publication"]["tree"], "3f997549ff2c3ae629cd1136f9a0f218a9279225")
        self.assertEqual(
            receipt["publication"]["parents"],
            ["8018746ca89a0816c01de80cf9387f9e12c8cb60", "cdde9046c0ae29a62f0ddc127ccc724f85aa34f5"],
        )
        self.assertTrue(receipt["claims"]["required_ci_verified"])
        self.assertFalse(receipt["claims"]["auxiliary_checks_healthy"])
        self.assertFalse(receipt["claims"]["all_pipelines_green"])
        self.assertEqual(receipt["claims"]["merge_readiness"], "not_evaluated")
        self.assertEqual(receipt["post_merge_health"]["run"]["id"], 35974476682)


if __name__ == "__main__":
    unittest.main()
