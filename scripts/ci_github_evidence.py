#!/usr/bin/env python3
"""Read-only GitHub observations for the CI gate evidence contract.

Collection is deliberately separate from the provider-neutral validator in
``ci_contract.py``.  A page is never treated as complete merely because the
GitHub API returned HTTP 200.
"""

from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import subprocess
import sys
import urllib.error
import urllib.request
from collections.abc import Callable
from pathlib import Path
from typing import Any
from urllib.parse import urlencode, urlsplit

if __package__:
    from . import ci_contract
    from . import ci_publication
else:  # Imported by the standalone loop_engine.py entry point.
    import ci_contract
    import ci_publication


API_ROOT = "https://api.github.com"
LINK = re.compile(r'<([^>]+)>;\s*rel="([^"]+)"')


class EvidenceError(ValueError):
    """The provider did not supply complete, trustworthy observations."""


def _github_token() -> str:
    token = os.environ.get("GH_TOKEN") or os.environ.get("GITHUB_TOKEN")
    if token:
        return token
    result = subprocess.run(
        ["gh", "auth", "token"], capture_output=True, text=True, check=False
    )
    if result.returncode or not result.stdout.strip():
        raise EvidenceError(
            "GitHub read token unavailable; run gh auth login or set GH_TOKEN"
        )
    return result.stdout.strip()


def _http_get(url: str) -> tuple[Any, dict[str, str]]:
    request = urllib.request.Request(
        url,
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {_github_token()}",
            "X-GitHub-Api-Version": "2022-11-28",
            "User-Agent": "derived-alg-geo-ci-evidence",
        },
        method="GET",
    )
    try:
        with urllib.request.urlopen(request, timeout=20) as response:
            raw = response.read()
            headers = {key.lower(): value for key, value in response.headers.items()}
    except urllib.error.HTTPError as exc:
        if exc.code in {403, 429}:
            raise EvidenceError(
                f"GitHub API rate limit or permission error ({exc.code}) at {url}"
            ) from exc
        raise EvidenceError(f"GitHub API HTTP {exc.code} at {url}") from exc
    except (urllib.error.URLError, TimeoutError) as exc:
        raise EvidenceError(f"GitHub API request failed at {url}: {exc}") from exc
    try:
        return json.loads(raw), headers
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EvidenceError(f"GitHub API returned invalid JSON at {url}") from exc


class GitHubClient:
    def __init__(
        self,
        repository: str,
        *,
        transport: Callable[[str], tuple[Any, dict[str, str]]] = _http_get,
        max_pages: int = 20,
    ) -> None:
        if not re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository):
            raise EvidenceError("repository must be an owner/name pair")
        if max_pages < 1:
            raise EvidenceError("max_pages must be positive")
        self.repository = repository
        self._prefix = f"{API_ROOT}/repos/{repository}/"
        self._transport = transport
        self.max_pages = max_pages

    def _url(self, path: str, *, per_page: int | None = None) -> str:
        if not path.startswith("/") or ".." in path or "//" in path:
            raise EvidenceError("invalid GitHub API path")
        url = self._prefix + path.lstrip("/")
        if per_page is not None:
            url += ("&" if "?" in url else "?") + urlencode({"per_page": per_page})
        return url

    def _get(self, url: str) -> tuple[Any, dict[str, str]]:
        parts = urlsplit(url)
        if (
            parts.scheme != "https"
            or parts.netloc != "api.github.com"
            or not url.startswith(self._prefix)
        ):
            raise EvidenceError(f"pagination escaped repository API scope: {url}")
        value, headers = self._transport(url)
        if not isinstance(headers, dict):
            raise EvidenceError("GitHub API response headers are malformed")
        return value, {str(key).lower(): str(val) for key, val in headers.items()}

    def get_object(self, path: str) -> dict[str, Any]:
        value, headers = self._get(self._url(path))
        if not isinstance(value, dict):
            raise EvidenceError(f"GitHub API object response is malformed: {path}")
        if "next" in self._links(headers.get("link", "")):
            raise EvidenceError(f"unexpected pagination on object response: {path}")
        return value

    @staticmethod
    def _links(header: str) -> dict[str, str]:
        links: dict[str, str] = {}
        if header and not LINK.findall(header):
            raise EvidenceError("GitHub API Link header is malformed")
        for url, relation in LINK.findall(header):
            if relation in links:
                raise EvidenceError(f"duplicate GitHub API Link relation {relation!r}")
            links[relation] = url
        return links

    def get_all(self, path: str, *, key: str | None = None) -> list[dict[str, Any]]:
        """Follow every Link page and check the advertised total when present."""
        url: str | None = self._url(path, per_page=100)
        seen_urls: set[str] = set()
        items: list[dict[str, Any]] = []
        total: int | None = None
        while url is not None:
            if url in seen_urls or len(seen_urls) >= self.max_pages:
                raise EvidenceError(
                    f"GitHub API pagination loop or page limit at {path}"
                )
            seen_urls.add(url)
            value, headers = self._get(url)
            if key is None:
                page = value
            else:
                if not isinstance(value, dict) or not isinstance(value.get(key), list):
                    raise EvidenceError(f"GitHub API page lacks {key!r}: {path}")
                count = value.get("total_count")
                if isinstance(count, bool) or not isinstance(count, int) or count < 0:
                    raise EvidenceError(
                        f"GitHub API page lacks valid total_count: {path}"
                    )
                if total is not None and total != count:
                    raise EvidenceError(
                        f"GitHub API total_count changed during pagination: {path}"
                    )
                total = count
                page = value[key]
            if not isinstance(page, list) or any(
                not isinstance(item, dict) for item in page
            ):
                raise EvidenceError(f"GitHub API list response is malformed: {path}")
            items.extend(page)
            links = self._links(headers.get("link", ""))
            next_url = links.get("next")
            if next_url is not None and urlsplit(next_url).path != urlsplit(url).path:
                raise EvidenceError(
                    f"GitHub API pagination changed resource path: {path}"
                )
            if next_url is None and total is not None and len(items) != total:
                raise EvidenceError(
                    f"GitHub API page count is truncated: {path}: {len(items)}/{total}"
                )
            if next_url is None and total is None and len(page) == 100:
                # A bare array has no total_count; exactly full final pages are
                # ambiguous unless the provider explicitly reports another link.
                raise EvidenceError(
                    f"GitHub API full page has no completeness proof: {path}"
                )
            url = next_url
        if total is not None and len(items) != total:
            raise EvidenceError(f"GitHub API page count is inconsistent: {path}")
        return items


def _sha(value: Any, label: str) -> str:
    if not ci_contract._is_sha(value):
        raise EvidenceError(f"{label} is not a full Git SHA")
    return value.lower()


def _positive(value: Any, label: str) -> int:
    if not ci_contract._is_positive_int(value):
        raise EvidenceError(f"{label} is not a positive integer")
    return value


def _required_object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise EvidenceError(f"{label} is missing or malformed")
    return value


def _canonical(value: Any) -> bytes:
    return (
        json.dumps(
            value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")
        + b"\n"
    )


def _blob(client: GitHubClient, commit: str, path: str) -> bytes:
    value = client.get_object(f"/contents/{path}?ref={commit}")
    if value.get("type") != "file" or value.get("encoding") != "base64":
        raise EvidenceError(f"Git object {commit}:{path} is not a readable file")
    try:
        data = base64.b64decode("".join(value["content"].split()), validate=True)
    except (KeyError, TypeError, ValueError) as exc:
        raise EvidenceError(
            f"Git object {commit}:{path} has malformed content"
        ) from exc
    if len(data) != value.get("size"):
        raise EvidenceError(f"Git object {commit}:{path} has inconsistent size")
    return data


def _commit(client: GitHubClient, sha: str) -> tuple[str, list[str]]:
    value = client.get_object(f"/git/commits/{sha}")
    if _sha(value.get("sha"), "Git commit") != sha:
        raise EvidenceError("Git commit response differs from requested SHA")
    tree = _sha(_required_object(value.get("tree"), "Git tree").get("sha"), "Git tree")
    parents = value.get("parents")
    if not isinstance(parents, list):
        raise EvidenceError("Git commit parents are missing")
    return tree, [
        _sha(_required_object(parent, "Git parent").get("sha"), "Git parent")
        for parent in parents
    ]


def _current_identity(
    client: GitHubClient, pr_number: int
) -> tuple[str, str, dict[str, Any]]:
    branch = client.get_object("/branches/main")
    if branch.get("name") != "main" or branch.get("protected") is not True:
        raise EvidenceError("main is not reported as the protected base branch")
    base = _sha(
        _required_object(branch.get("commit"), "main commit").get("sha"), "main commit"
    )
    pr = client.get_object(f"/pulls/{pr_number}")
    if pr.get("number") != pr_number or pr.get("state") != "open":
        raise EvidenceError("pull request is not the requested open PR")
    base_record = _required_object(pr.get("base"), "PR base")
    head_record = _required_object(pr.get("head"), "PR head")
    if (
        base_record.get("ref") != "main"
        or _sha(base_record.get("sha"), "PR base") != base
    ):
        raise EvidenceError("pull request base differs from current protected main")
    head = _sha(head_record.get("sha"), "PR head")
    return base, head, pr


def _policy(client: GitHubClient, base: str) -> tuple[dict[str, Any], dict[str, Any]]:
    try:
        inventory = json.loads(_blob(client, base, "scripts/ci_gate_inventory.json"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EvidenceError("protected-base inventory is invalid JSON") from exc
    problems = ci_contract.validate_inventory(inventory)
    if problems:
        raise EvidenceError(
            "protected-base inventory is invalid: " + "; ".join(problems)
        )
    if inventory.get("repository") != client.repository:
        raise EvidenceError("protected-base inventory names another repository")
    protection = client.get_object("/branches/main/protection/required_status_checks")
    if protection.get("strict") is not True:
        raise EvidenceError("main protection does not require up-to-date checks")
    contexts = protection.get("contexts")
    checks = protection.get("checks")
    if not isinstance(contexts, list) or not isinstance(checks, list):
        raise EvidenceError("required status-check policy is incomplete")
    names = set()
    app_by_name: dict[str, int] = {}
    for item in contexts:
        if not isinstance(item, str) or not item:
            raise EvidenceError("protection has a malformed required context")
        if item in names:
            raise EvidenceError(f"protection has duplicate required context {item!r}")
        names.add(item)
    seen_checks: set[str] = set()
    for item in checks:
        if not isinstance(item, dict) or not isinstance(item.get("context"), str):
            raise EvidenceError("protection has a malformed required check")
        name = item["context"]
        if name in seen_checks:
            raise EvidenceError(f"protection has duplicate required check {name!r}")
        seen_checks.add(name)
        names.add(name)
        app_id = item.get("app_id")
        if app_id is not None:
            app_by_name[name] = _positive(app_id, "required-check app_id")
    definitions: dict[str, dict[str, Any]] = {}
    for gate in inventory["gates"]:
        if gate["required"]:
            if gate["name"] in definitions:
                raise EvidenceError(
                    f"ambiguous required inventory context {gate['name']!r}"
                )
            definitions[gate["name"]] = gate
    unknown = names - definitions.keys()
    if unknown:
        raise EvidenceError(
            "unaccounted protected context: " + ", ".join(sorted(unknown))
        )
    if not names:
        raise EvidenceError("main protection has no required checks")
    merge_contexts = {
        gate["name"]
        for gate in inventory["gates"]
        if gate["required"] and gate["class"] == "merge_readiness"
    }
    if not merge_contexts <= names:
        raise EvidenceError(
            "main protection omitted the inventory merge-readiness context"
        )
    return inventory, {
        "contexts": sorted(names),
        "app_by_name": app_by_name,
        "raw": protection,
    }


def _select_run(
    client: GitHubClient, pr_number: int, base: str, head: str
) -> dict[str, Any]:
    runs = client.get_all(f"/actions/runs?head_sha={head}", key="workflow_runs")
    ci_runs = [
        run for run in runs if run.get("name") == "CI" and run.get("head_sha") == head
    ]
    # GitHub branch protection can aggregate an older red check on the same
    # commit even when a later distinct run is green. A rerun of one run ID is
    # handled through its attempt, but distinct runs deny this claim.
    if len(ci_runs) != 1:
        raise EvidenceError(
            "expected one distinct CI workflow run on the PR head; branch-protection outcome is ambiguous"
        )
    run = ci_runs[0]
    associations = run.get("pull_requests")
    if not isinstance(associations, list) or not any(
        isinstance(item, dict)
        and item.get("number") == pr_number
        and isinstance(item.get("base"), dict)
        and item["base"].get("sha") == base
        and isinstance(item.get("head"), dict)
        and item["head"].get("sha") == head
        for item in associations
    ):
        raise EvidenceError("CI run lacks the current PR/base/head association")
    if (
        run.get("event") != "pull_request"
        or run.get("path") != ".github/workflows/ci.yml"
    ):
        raise EvidenceError(
            "CI run event or workflow path is not the protected PR workflow"
        )
    _positive(run.get("check_suite_id"), "workflow check_suite_id")
    _positive(run.get("run_attempt"), "workflow run_attempt")
    run_id = _positive(run.get("id"), "workflow run ID")
    exact_run = client.get_object(f"/actions/runs/{run_id}")
    if _run_identity(exact_run) != _run_identity(run):
        raise EvidenceError("CI run changed between listing and direct read")
    if run.get("status") != "completed":
        raise EvidenceError("current PR CI workflow run is not completed")
    return run


def _run_identity(run: dict[str, Any]) -> tuple[Any, ...]:
    return tuple(
        run.get(field)
        for field in (
            "id",
            "run_attempt",
            "check_suite_id",
            "head_sha",
            "event",
            "status",
            "conclusion",
        )
    )


def _candidate(
    client: GitHubClient, base: str, head: str, run: dict[str, Any]
) -> tuple[str, str, list[str], list[dict[str, Any]]]:
    run_id = run["id"]
    attempt = run["run_attempt"]
    artifacts = client.get_all(f"/actions/runs/{run_id}/artifacts", key="artifacts")
    matches = []
    for artifact in artifacts:
        name = artifact.get("name")
        if not isinstance(name, str) or not name.startswith("trust-artifacts-"):
            continue
        provenance = _required_object(
            artifact.get("workflow_run"), "run artifact provenance"
        )
        if (
            provenance.get("id") != run_id
            or provenance.get("head_sha") != head
            or artifact.get("expired") is not False
        ):
            raise EvidenceError(
                "candidate artifact has wrong run/head identity or expired"
            )
        matches.append(artifact)
    if attempt > 1:
        current = client.get_object(f"/actions/runs/{run_id}/attempts/{attempt}")
        if current.get("run_attempt") != attempt or current.get("head_sha") != head:
            raise EvidenceError("current run attempt identity is inconsistent")
        started = current.get("run_started_at")
        if not isinstance(started, str):
            raise EvidenceError("current run attempt has no start time")
        matches = [
            item
            for item in matches
            if isinstance(item.get("created_at"), str) and item["created_at"] >= started
        ]
    if len(matches) != 1:
        raise EvidenceError(
            "run lacks one unambiguous trust-artifacts candidate binding for its current attempt"
        )
    artifact = matches[0]
    candidate = _sha(
        artifact["name"].removeprefix("trust-artifacts-"), "run artifact candidate"
    )
    base_workflow = _blob(client, base, ".github/workflows/ci.yml")
    candidate_workflow = _blob(client, candidate, ".github/workflows/ci.yml")
    if (
        base_workflow != candidate_workflow
        or b"name: trust-artifacts-${{ github.sha }}" not in base_workflow
    ):
        raise EvidenceError(
            "candidate workflow changed the trusted merge-SHA artifact rule"
        )
    tree, parents = _commit(client, candidate)
    if len(parents) != 2 or parents != [base, head] or candidate in {base, head}:
        raise EvidenceError(
            "run artifact candidate is not the current base/head merge commit"
        )
    return candidate, tree, parents, artifacts


def _conclusion(check: dict[str, Any]) -> tuple[str, str]:
    raw = check.get("conclusion")
    if check.get("status") != "completed":
        return "pending", str(raw or "pending")
    return {
        "success": "passed",
        "failure": "failed",
        "cancelled": "cancelled",
        "timed_out": "timed_out",
        "skipped": "skipped",
    }.get(raw, "unknown"), str(raw or "unknown")


def _observations(
    client: GitHubClient, head: str, run: dict[str, Any]
) -> dict[str, Any]:
    suites = client.get_all(f"/commits/{head}/check-suites", key="check_suites")
    check_runs: list[dict[str, Any]] = []
    primary_check_ids: set[int] = set()
    suite_ids: set[int] = set()
    primary_suite = None
    for suite in suites:
        suite_id = _positive(suite.get("id"), "check suite ID")
        if suite_id in suite_ids or suite.get("head_sha") != head:
            raise EvidenceError("duplicate or foreign check suite")
        suite_ids.add(suite_id)
        runs = client.get_all(
            f"/check-suites/{suite_id}/check-runs?filter=all", key="check_runs"
        )
        if (
            suite.get("latest_check_runs_count") is not None
            and len(runs) < suite["latest_check_runs_count"]
        ):
            raise EvidenceError("check suite run count is truncated")
        for check in runs:
            if check.get("head_sha") != head:
                raise EvidenceError("check run is not on the PR head")
        check_runs.extend(runs)
        if suite_id == run["check_suite_id"]:
            primary_suite = suite
            primary_check_ids = {
                _positive(check.get("id"), "primary check ID") for check in runs
            }
    if primary_suite is None:
        raise EvidenceError("primary workflow check suite is missing")
    statuses = client.get_all(f"/commits/{head}/statuses")
    for status in statuses:
        if status.get("sha") != head:
            raise EvidenceError("commit status is not on the PR head")
    attempt_jobs: dict[int, list[dict[str, Any]]] = {}
    for number in range(1, run["run_attempt"] + 1):
        jobs = client.get_all(
            f"/actions/runs/{run['id']}/attempts/{number}/jobs", key="jobs"
        )
        for job in jobs:
            if (
                job.get("run_id") != run["id"]
                or job.get("run_attempt") != number
                or job.get("head_sha") != head
            ):
                raise EvidenceError(
                    "workflow job run/attempt/head identity is inconsistent"
                )
        attempt_jobs[number] = jobs
    return {
        "suites": suites,
        "check_runs": check_runs,
        "statuses": statuses,
        "attempt_jobs": attempt_jobs,
        "primary_suite": primary_suite,
        "primary_check_ids": sorted(primary_check_ids),
    }


def collect(client: GitHubClient, pr_number: int) -> dict[str, Any]:
    """Collect a candidate-bound bundle without mutating GitHub or Git state."""
    pr_number = _positive(pr_number, "pull request number")
    base, head, pr = _current_identity(client, pr_number)
    inventory, protection = _policy(client, base)
    run = _select_run(client, pr_number, base, head)
    candidate, tree, parents, run_artifacts = _candidate(client, base, head, run)
    if _sha(pr.get("merge_commit_sha"), "PR merge commit") != candidate:
        raise EvidenceError(
            "run artifact candidate differs from current PR merge commit"
        )
    observed = _observations(client, head, run)
    observed["run_artifacts"] = run_artifacts
    observed["workflow_run"] = run
    app = _required_object(observed["primary_suite"].get("app"), "primary suite app")
    app_id = _positive(app.get("id"), "primary suite app ID")
    if app.get("slug") != "github-actions":
        raise EvidenceError("primary suite is not produced by GitHub Actions")
    for name, expected_app in protection["app_by_name"].items():
        if expected_app != app_id:
            raise EvidenceError(f"protected check {name!r} requires a different app")

    pins = {}
    for path in sorted(ci_contract.REQUIRED_PINS):
        pins[path] = hashlib.sha256(_blob(client, candidate, path)).hexdigest()
    toolchain = _blob(client, candidate, "lean-toolchain").decode("utf-8").strip()
    if not toolchain:
        raise EvidenceError("candidate lean-toolchain is empty")

    run_id, attempt = run["id"], run["run_attempt"]
    by_check_id: dict[int, dict[str, Any]] = {}
    for check in observed["check_runs"]:
        check_id = _positive(check.get("id"), "check run ID")
        if check_id in by_check_id:
            raise EvidenceError("duplicate check run ID across suites")
        by_check_id[check_id] = check
    current_jobs = observed["attempt_jobs"][attempt]
    jobs_by_name: dict[str, list[dict[str, Any]]] = {}
    for job in current_jobs:
        jobs_by_name.setdefault(str(job.get("name")), []).append(job)
    gates: list[dict[str, Any]] = []
    artifacts: list[dict[str, Any]] = []
    payloads: dict[str, bytes] = {}
    for definition in inventory["gates"]:
        if not ci_contract._event_applies(
            definition,
            {
                "event": "pull_request",
                "ref": f"refs/pull/{pr_number}/merge",
                "producer": "github-actions/CI",
            },
        ):
            continue
        if definition["run_binding"] == "check":
            matches = [
                check
                for check in observed["check_runs"]
                if check.get("name") == definition["name"]
                and isinstance(check.get("app"), dict)
                and check["app"].get("slug") == definition["producer"]
            ]
            if len(matches) > 1:
                raise EvidenceError(
                    f"ambiguous check-app observations for {definition['name']!r}"
                )
            if not matches:
                continue  # Missing optional check is reported by the validator.
            check = matches[0]
            check_id = _positive(check.get("id"), "check-app run ID")
            _positive(
                _required_object(check.get("app"), "check app").get("id"),
                "check app ID",
            )
            status, raw = _conclusion(check)
            path = f"results/check-run-{check_id}.json"
            body = _canonical(
                {"check_run": check, "head": head, "candidate": candidate}
            )
            payloads[path] = body
            artifact_id = f"github-check-run-{check_id}"
            artifacts.append(
                {
                    "id": artifact_id,
                    "path": path,
                    "sha256": hashlib.sha256(body).hexdigest(),
                    "media_type": "application/json",
                    "size_bytes": len(body),
                    "producer": definition["producer"],
                    "kind": definition["artifact"],
                    "subject": definition["id"],
                    "commit": head,
                }
            )
            gate = {
                "id": definition["id"],
                "name": definition["name"],
                "producer": definition["producer"],
                "platform": "github-checks",
                "provider_id": str(check_id),
                "commit": head,
                "status": status,
                "conclusion": raw,
                "applicable": True,
                "prerequisites": definition["prerequisites"],
                "artifact_refs": [artifact_id],
            }
            if status == "skipped":
                gate["skip_reason"] = "provider reported skipped"
            gates.append(gate)
            continue
        if definition["run_binding"] != "primary":
            # Independent workflows require their own proven run/candidate
            # identity. No such inventory gate applies to this PR event.
            continue
        matches = jobs_by_name.get(definition["name"], [])
        if len(matches) > 1:
            raise EvidenceError(
                f"ambiguous current workflow jobs for {definition['name']!r}"
            )
        if not matches:
            continue  # The validator reports a missing required gate.
        job = matches[0]
        check_url = job.get("check_run_url")
        if not isinstance(check_url, str) or not check_url.startswith(
            client._prefix + "check-runs/"
        ):
            raise EvidenceError("workflow job lacks a trusted check-run URL")
        check_id = _positive(job.get("id"), "workflow job ID")
        if check_url != f"{client._prefix}check-runs/{check_id}":
            raise EvidenceError("workflow job check-run URL and ID differ")
        check = by_check_id.get(check_id)
        if (
            check is None
            or check_id not in observed["primary_check_ids"]
            or check.get("name") != definition["name"]
            or _required_object(check.get("app"), "check app").get("id") != app_id
        ):
            raise EvidenceError("workflow job has no matching GitHub Actions check run")
        if job.get("status") != check.get("status") or job.get(
            "conclusion"
        ) != check.get("conclusion"):
            raise EvidenceError(
                f"workflow job and check run outcomes conflict for {definition['name']!r}"
            )
        status, raw = _conclusion(check)
        payload = {
            "check_run": check,
            "job": job,
            "candidate": candidate,
            "run_id": run_id,
            "run_attempt": attempt,
        }
        path = f"results/check-run-{check_id}.json"
        body = _canonical(payload)
        payloads[path] = body
        artifact_id = f"github-check-run-{check_id}"
        artifacts.append(
            {
                "id": artifact_id,
                "path": path,
                "sha256": hashlib.sha256(body).hexdigest(),
                "media_type": "application/json",
                "size_bytes": len(body),
                "producer": definition["producer"],
                "kind": definition["artifact"],
                "subject": definition["id"],
                "commit": candidate,
                "run_id": run_id,
                "run_attempt": attempt,
            }
        )
        gate = {
            "id": definition["id"],
            "name": definition["name"],
            "producer": definition["producer"],
            "platform": "github-actions",
            "provider_id": str(check_id),
            "commit": candidate,
            "run_id": run_id,
            "run_attempt": attempt,
            "status": status,
            "conclusion": raw,
            "applicable": True,
            "prerequisites": definition["prerequisites"],
            "artifact_refs": [artifact_id],
        }
        if status == "skipped" and not definition["required"]:
            gate["skip_reason"] = "provider reported skipped"
        gates.append(gate)

    revision = {
        "base_commit": base,
        "head_commit": head,
        "candidate_commit": candidate,
        "candidate_tree": tree,
        "event": "pull_request",
        "ref": f"refs/pull/{pr_number}/merge",
    }
    proof = {
        "source": "github-api",
        "repository": client.repository,
        "producer": "github-actions/CI",
        "run_id": run_id,
        "run_attempt": attempt,
        "event": "pull_request",
        "ref": revision["ref"],
        "commit": candidate,
        "tree": tree,
        "parents": parents,
    }
    proof["proof_sha256"] = ci_contract._canonical_sha256(proof)
    evidence = {
        "schema_version": inventory["schema_version"],
        "repository": client.repository,
        **revision,
        "revision_binding": revision.copy(),
        "policy_binding": {
            "source": "protected-base",
            "commit": base,
            "inventory_sha256": ci_contract._canonical_sha256(inventory),
        },
        "provider_binding": proof,
        "platform": "github-actions",
        "run_id": run_id,
        "run_attempt": attempt,
        "producer": "github-actions/CI",
        "toolchain": toolchain,
        "pins": pins,
        "artifacts": artifacts,
        "gates": gates,
    }

    final_base, final_head, final_pr = _current_identity(client, pr_number)
    if final_base != base or final_head != head:
        raise EvidenceError("protected base or PR head moved during collection")
    if _sha(final_pr.get("merge_commit_sha"), "final PR merge commit") != candidate:
        raise EvidenceError("PR merge candidate moved during collection")
    final_protection = client.get_object(
        "/branches/main/protection/required_status_checks"
    )
    if final_protection != protection["raw"]:
        raise EvidenceError("required-check protection changed during collection")
    final_run = _select_run(client, pr_number, final_base, final_head)
    if _run_identity(final_run) != _run_identity(run):
        raise EvidenceError("CI run or attempt changed during collection")
    validation = ci_contract.validate_evidence(
        inventory,
        evidence,
        trusted_base_commit=final_base,
        trusted_head_commit=final_head,
        trusted_inventory_sha256=ci_contract._canonical_sha256(inventory),
    )
    if run.get("conclusion") != "success":
        validation["valid"] = False
        validation["errors"].append(
            f"primary CI workflow conclusion is {run.get('conclusion')!r}, not success"
        )
        validation["claims"]["required_ci_verified"] = False
        validation["claims"]["all_pipelines_green"] = False
    if not artifacts:
        validation["valid"] = False
        validation["errors"].append("no provider-bound gate artifacts were collected")
        validation["claims"]["required_ci_verified"] = False
        validation["claims"]["all_pipelines_green"] = False
    # Unknown auxiliary observations remain visible, and cannot support an
    # all-pipelines-green statement from this collector.
    foreign = [
        check
        for check in observed["check_runs"]
        if check.get("id") not in {int(g["provider_id"]) for g in gates}
    ]
    if foreign or observed["statuses"]:
        validation["warnings"].append(
            f"{len(foreign)} unclassified check runs and {len(observed['statuses'])} commit statuses retained"
        )
        validation["claims"]["all_pipelines_green"] = False
    return {
        "evidence": evidence,
        "validation": validation,
        "inventory": inventory,
        "observations": observed,
        "payloads": payloads,
        "protection": protection["raw"],
    }


def collect_post_merge_health(client: GitHubClient, commit: str) -> dict[str, Any]:
    """Observe the protected CI workflow on the exact published commit.

    This is deliberately a separate claim from premerge required CI. A merge
    receipt made before the main-branch workflow finishes stays pending and
    cannot claim operational verification.
    """

    commit = _sha(commit, "published commit")
    runs = client.get_all(f"/actions/runs?head_sha={commit}", key="workflow_runs")
    matches = [
        run
        for run in runs
        if run.get("head_sha") == commit
        and run.get("name") == "CI"
        and run.get("path") == ".github/workflows/ci.yml"
        and run.get("event") == "push"
    ]
    if not matches:
        return {"status": "pending", "commit": commit, "run": None}
    if len(matches) != 1:
        return {
            "status": "unknown",
            "commit": commit,
            "run": None,
            "reason": "multiple post-merge CI runs are ambiguous",
        }
    listed = matches[0]
    run_id = _positive(listed.get("id"), "post-merge CI run ID")
    run = client.get_object(f"/actions/runs/{run_id}")
    if _run_identity(run) != _run_identity(listed):
        raise EvidenceError("post-merge CI run changed between listing and direct read")
    if run.get("head_sha") != commit or run.get("event") != "push" or run.get(
        "path"
    ) != ".github/workflows/ci.yml":
        raise EvidenceError("post-merge CI run is not bound to the published commit")
    if run.get("status") != "completed":
        status = "pending"
    elif run.get("conclusion") == "success":
        status = "passed"
    elif run.get("conclusion") in {"failure", "cancelled", "timed_out", "action_required"}:
        status = "failed"
    else:
        status = "unknown"
    return {
        "status": status,
        "commit": commit,
        "run": {
            "id": run_id,
            "attempt": _positive(run.get("run_attempt"), "post-merge CI run attempt"),
            "url": run.get("html_url"),
            "status": run.get("status"),
            "conclusion": run.get("conclusion"),
        },
    }


def collect_publication(
    client: GitHubClient,
    pr_number: int,
    *,
    reviewed_commit: str,
    reviewed_tree: str,
    premerge: dict[str, Any],
    merge_readiness: dict[str, Any],
) -> dict[str, Any]:
    """Verify a merged PR's actual Git object and return an exact receipt."""

    pr_number = _positive(pr_number, "pull request number")
    evidence = premerge.get("evidence")
    validation = premerge.get("validation")
    observations = premerge.get("observations")
    inventory = premerge.get("inventory")
    if not all(isinstance(value, dict) for value in (evidence, validation, observations, inventory)):
        raise EvidenceError("premerge evidence bundle is malformed")
    base = _sha(evidence.get("base_commit"), "checked base")
    head = _sha(evidence.get("head_commit"), "checked head")
    candidate_tree = _sha(evidence.get("candidate_tree"), "CI candidate tree")
    reviewed_commit = _sha(reviewed_commit, "reviewed commit")
    reviewed_tree = _sha(reviewed_tree, "reviewed tree")

    pr = client.get_object(f"/pulls/{pr_number}")
    if pr.get("number") != pr_number or pr.get("state") != "closed" or pr.get("merged") is not True:
        raise EvidenceError("pull request is not confirmed merged by GitHub")
    pr_base = _sha(_required_object(pr.get("base"), "PR base").get("sha"), "PR base")
    pr_head = _sha(_required_object(pr.get("head"), "PR head").get("sha"), "PR head")
    published = _sha(pr.get("merge_commit_sha"), "published merge commit")
    if pr_base != base or pr_head != head:
        raise EvidenceError("merged PR base or head differs from the checked revisions")

    reviewed_commit_tree, _ = _commit(client, reviewed_commit)
    head_tree, _ = _commit(client, head)
    published_tree, parents = _commit(client, published)
    if reviewed_commit_tree != reviewed_tree or head_tree != reviewed_tree:
        raise EvidenceError("PR head tree differs from the final reviewed tree; renew review")
    if published_tree != reviewed_tree or published_tree != candidate_tree:
        raise EvidenceError(
            "published tree differs from the final reviewed tree; renew review"
        )
    if not parents:
        raise EvidenceError("published commit has no parent")
    if len(parents) == 2:
        if parents != [base, head]:
            raise EvidenceError(
                "published merge commit parents differ from the checked base and head"
            )
        base_is_ancestor = True
    elif len(parents) == 1 and parents[0] == base:
        base_is_ancestor = True
    elif len(parents) == 1:
        # A rebase merge may publish a new final commit whose direct parent is
        # another commit from the PR. The compare endpoint gives the provider's
        # complete ancestry classification without treating a separate GET and
        # ref update as an atomic CAS.
        comparison_url = f"{client._prefix}compare/{base}...{published}"
        comparison, _ = client._get(comparison_url)
        if not isinstance(comparison, dict):
            raise EvidenceError("provider ancestry comparison is malformed")
        if (
            _required_object(comparison.get("base_commit"), "comparison base").get("sha")
            != base
            or comparison.get("status") not in {"ahead", "identical"}
        ):
            raise EvidenceError("published commit is not based on the checked base")
        base_is_ancestor = True
    else:
        raise EvidenceError("published commit has an unsupported parent set")

    # Re-read immutable PR identity after collecting Git objects. The provider
    # merge call uses --match-head-commit; this check records what actually
    # landed and does not claim that separate reads are an atomic CAS.
    final_pr = client.get_object(f"/pulls/{pr_number}")
    if (
        final_pr.get("state") != "closed"
        or final_pr.get("merged") is not True
        or _sha(final_pr.get("merge_commit_sha"), "final published commit") != published
        or _sha(_required_object(final_pr.get("head"), "final PR head").get("sha"), "final PR head") != head
    ):
        raise EvidenceError("publication identity changed during receipt collection")

    post_merge = collect_post_merge_health(client, published)
    receipt = ci_publication.build_receipt(
        repository=client.repository,
        pr_number=pr_number,
        pr_url=str(pr.get("html_url") or ""),
        reviewed_commit=reviewed_commit,
        reviewed_tree=reviewed_tree,
        premerge_evidence=evidence,
        premerge_validation=validation,
        premerge_observations=observations,
        premerge_inventory=inventory,
        published_commit=published,
        published_tree=published_tree,
        published_parents=parents,
        published_base_is_ancestor=base_is_ancestor,
        merge_readiness=merge_readiness,
        post_merge_health=post_merge,
    )
    verify_publication_provider_evidence(client, receipt)
    return receipt


def verify_publication_provider_evidence(
    client: GitHubClient, receipt: dict[str, Any]
) -> None:
    """Independently re-read the published commit and both CI evidence phases."""

    ci_publication.verify_receipt(receipt)
    if receipt.get("repository") != client.repository:
        raise EvidenceError("publication receipt names another repository")
    pr_number = _positive(receipt.get("pull_request", {}).get("number"), "receipt PR number")
    premerge = _required_object(receipt.get("premerge"), "receipt premerge")
    base = _sha(premerge.get("base_commit"), "receipt checked base")
    head = _sha(premerge.get("head_commit"), "receipt checked head")
    review = _required_object(receipt.get("review"), "receipt review")
    publication = _required_object(receipt.get("publication"), "receipt publication")
    reviewed_commit = _sha(review.get("commit"), "receipt reviewed commit")
    published_commit = _sha(publication.get("commit"), "receipt published commit")

    pr = client.get_object(f"/pulls/{pr_number}")
    if (
        pr.get("state") != "closed"
        or pr.get("merged") is not True
        or _sha(pr.get("merge_commit_sha"), "provider merge commit") != published_commit
        or _sha(_required_object(pr.get("base"), "provider PR base").get("sha"), "provider PR base") != base
        or _sha(_required_object(pr.get("head"), "provider PR head").get("sha"), "provider PR head") != head
    ):
        raise EvidenceError("provider PR identity differs from the publication receipt")
    reviewed_tree, _ = _commit(client, reviewed_commit)
    head_tree, _ = _commit(client, head)
    published_tree, parents = _commit(client, published_commit)
    expected_parents = [_sha(parent, "receipt parent") for parent in publication["parents"]]
    if (
        reviewed_tree != review.get("tree")
        or head_tree != review.get("tree")
        or published_tree != publication.get("tree")
        or parents != expected_parents
    ):
        raise EvidenceError("provider Git tree or parent list differs from the publication receipt")
    if not parents or parents[0] != base:
        compare_url = f"{client._prefix}compare/{base}...{published_commit}"
        comparison, _ = client._get(compare_url)
        if (
            not isinstance(comparison, dict)
            or _required_object(comparison.get("base_commit"), "comparison base").get("sha") != base
            or comparison.get("status") not in {"ahead", "identical"}
        ):
            raise EvidenceError("provider no longer proves the checked base is an ancestor")

    verify_premerge_provider_evidence(client, receipt)
    observed_post = collect_post_merge_health(client, published_commit)
    recorded_post = receipt.get("post_merge_health")
    if not isinstance(recorded_post, dict) or recorded_post.get("commit") != published_commit:
        raise EvidenceError("receipt post-merge observation is not bound to the published commit")
    if recorded_post.get("status") == "pending" and recorded_post.get("run") is None:
        # A run can start after the receipt was written; a pending snapshot is
        # conservative and must never be promoted to operational verification.
        return
    if observed_post != recorded_post:
        raise EvidenceError("provider post-merge CI differs from the publication receipt")


def verify_premerge_provider_evidence(
    client: GitHubClient, receipt: dict[str, Any]
) -> None:
    """Re-read the receipt's PR run, enumerated checks, and statuses by ID."""

    ci_publication.verify_receipt(receipt)
    premerge = receipt["premerge"]
    pr_number = receipt["pull_request"]["number"]
    base = _sha(premerge.get("base_commit"), "receipt base")
    head = _sha(premerge.get("head_commit"), "receipt head")
    run_summary = _required_object(premerge.get("workflow_run"), "receipt workflow run")
    run_id = _positive(premerge.get("run_id"), "receipt workflow run ID")
    run = client.get_object(f"/actions/runs/{run_id}")
    expected_run = (
        run_id,
        _positive(premerge.get("run_attempt"), "receipt workflow run attempt"),
        _positive(run_summary.get("check_suite_id"), "receipt primary suite ID"),
        head,
        "pull_request",
        "completed",
        "success",
    )
    if _run_identity(run) != expected_run or run.get("path") != ".github/workflows/ci.yml" or any(
        run.get(field) != run_summary.get(field)
        for field in (
            "id", "run_attempt", "check_suite_id", "head_sha", "event", "path",
            "status", "conclusion", "html_url",
        )
    ):
        raise EvidenceError("receipt premerge workflow run differs from GitHub")
    associations = run_summary.get("pull_requests")
    if not isinstance(associations, list) or not any(
        isinstance(item, dict)
        and item.get("number") == pr_number
        and item.get("base_sha") == base
        and item.get("head_sha") == head
        for item in associations
    ):
        raise EvidenceError("receipt CI run is not associated with its PR/base/head")

    suites = client.get_all(f"/commits/{head}/check-suites", key="check_suites")
    suite_map = {
        _positive(suite.get("id"), "live check suite ID"): suite for suite in suites
    }
    for expected in premerge.get("check_suites", []):
        if not isinstance(expected, dict):
            raise EvidenceError("receipt contains a malformed check-suite observation")
        suite_id = _positive(expected.get("id"), "receipt check suite ID")
        actual = suite_map.get(suite_id)
        if actual is None or actual.get("head_sha") != head:
            raise EvidenceError("receipt check suite is missing or on another head")
        app = actual.get("app") if isinstance(actual.get("app"), dict) else {}
        if app.get("id") != expected.get("app_id") or app.get("slug") != expected.get("app_slug"):
            raise EvidenceError("receipt check-suite producer differs from GitHub")

    live_checks: dict[int, dict[str, Any]] = {}
    for suite_id in sorted(suite_map):
        checks = client.get_all(
            f"/check-suites/{suite_id}/check-runs?filter=all", key="check_runs"
        )
        for check in checks:
            check_id = _positive(check.get("id"), "live check run ID")
            if check_id in live_checks:
                raise EvidenceError("duplicate live check-run ID across suites")
            if check.get("head_sha") != head:
                raise EvidenceError("live check run moved off the receipt head")
            live_checks[check_id] = check
    recorded_checks = premerge.get("check_runs")
    if not isinstance(recorded_checks, list):
        raise EvidenceError("receipt check-run observations are malformed")
    for expected in recorded_checks:
        if not isinstance(expected, dict):
            raise EvidenceError("receipt contains a malformed check-run observation")
        check_id = _positive(expected.get("id"), "receipt check run ID")
        actual = live_checks.get(check_id)
        if actual is None or ci_publication._provider_check_summary(actual) != expected:
            raise EvidenceError(f"receipt check run {check_id} differs from GitHub")

    statuses = client.get_all(f"/commits/{head}/statuses")
    status_map = {
        _positive(item.get("id"), "live commit status ID"): item for item in statuses
    }
    recorded_statuses = premerge.get("statuses")
    if not isinstance(recorded_statuses, list):
        raise EvidenceError("receipt commit-status observations are malformed")
    for expected in recorded_statuses:
        if not isinstance(expected, dict):
            raise EvidenceError("receipt contains a malformed commit-status observation")
        status_id = _positive(expected.get("id"), "receipt commit status ID")
        actual = status_map.get(status_id)
        summary = {
            "id": actual.get("id") if actual else None,
            "sha": actual.get("sha") if actual else None,
            "context": actual.get("context") if actual else None,
            "state": actual.get("state") if actual else None,
            "updated_at": actual.get("updated_at") if actual else None,
            "target_url": actual.get("target_url") if actual else None,
        }
        if actual is None or summary != expected or actual.get("sha") != head:
            raise EvidenceError(f"receipt commit status {status_id} differs from GitHub")

    gate_records = premerge.get("gates")
    required_ids = premerge.get("required_gate_ids")
    if not isinstance(gate_records, list) or not isinstance(required_ids, list):
        raise EvidenceError("receipt gate list is malformed")
    gate_by_id = {gate.get("id"): gate for gate in gate_records if isinstance(gate, dict)}
    inventory = json.loads(_blob(client, base, "scripts/ci_gate_inventory.json"))
    if ci_contract.validate_inventory(inventory):
        raise EvidenceError("receipt base gate inventory is invalid")
    definitions = {gate["id"]: gate for gate in inventory["gates"]}
    for gate_id, gate in gate_by_id.items():
        definition = definitions.get(gate_id)
        if not isinstance(definition, dict):
            raise EvidenceError("receipt gate is absent from the protected inventory")
        try:
            provider_id = int(gate.get("provider_id"))
        except (TypeError, ValueError) as exc:
            raise EvidenceError(f"receipt gate {gate_id!r} has a malformed provider ID") from exc
        if definition.get("run_binding") == "status":
            actual_status = status_map.get(provider_id)
            normalized = "passed" if actual_status and actual_status.get("state") == "success" else (
                "failed" if actual_status and actual_status.get("state") in {"failure", "error"}
                else "pending"
            )
            raw_conclusion = actual_status.get("state") if actual_status else "missing"
        else:
            actual_check = live_checks.get(provider_id)
            if actual_check is None:
                raise EvidenceError(f"receipt gate {gate_id!r} check run is missing")
            normalized, raw_conclusion = _conclusion(actual_check)
        if (
            gate.get("name") != definition.get("name")
            or gate.get("class") != definition.get("class")
            or gate.get("required") != definition.get("required")
            or gate.get("status") != normalized
            or gate.get("conclusion") != raw_conclusion
        ):
            raise EvidenceError(f"receipt gate {gate_id!r} differs from provider evidence")
    for gate_id in required_ids:
        gate = gate_by_id.get(gate_id)
        definition = definitions.get(gate_id)
        if not isinstance(gate, dict) or not isinstance(definition, dict) or not definition.get("required"):
            raise EvidenceError("receipt omits a required gate from the protected inventory")
        try:
            provider_id = int(gate.get("provider_id"))
        except (TypeError, ValueError) as exc:
            raise EvidenceError("receipt required gate has a malformed provider ID") from exc
        if definition.get("run_binding") == "status":
            actual = status_map.get(provider_id)
            if gate.get("status") != "passed" or actual is None or actual.get("state") != "success":
                raise EvidenceError(f"required commit status {gate_id!r} is not green")
        else:
            actual = live_checks.get(provider_id)
            if (
                gate.get("status") != "passed"
                or actual is None
                or actual.get("name") != definition.get("name")
                or actual.get("status") != "completed"
                or actual.get("conclusion") != "success"
            ):
                raise EvidenceError(f"required check run {gate_id!r} is not green")


def write_bundle(result: dict[str, Any], directory: Path) -> None:
    """Write actual retained bytes and their manifest; never trust claimed hashes."""
    # The contract's policy digest uses canonical JSON without the bundle's
    # usual trailing newline, so retain those exact digest-bound bytes.
    inventory = _canonical(result["inventory"])[:-1]
    if (
        hashlib.sha256(inventory).hexdigest()
        != result["evidence"]["policy_binding"]["inventory_sha256"]
    ):
        raise EvidenceError("retained inventory does not match evidence policy binding")
    observations = _canonical(result["observations"])
    protection = _canonical(result["protection"])
    directory.mkdir(parents=True, exist_ok=True)
    for path, content in result["payloads"].items():
        artifact = next(
            (item for item in result["evidence"]["artifacts"] if item["path"] == path),
            None,
        )
        if (
            artifact is None
            or hashlib.sha256(content).hexdigest() != artifact["sha256"]
            or len(content) != artifact["size_bytes"]
        ):
            raise EvidenceError(f"artifact bytes do not match evidence: {path}")
        target = directory / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
    (directory / "source-observations.json").write_bytes(observations)
    (directory / "protected-inventory.json").write_bytes(inventory)
    (directory / "live-protection.json").write_bytes(protection)
    (directory / "evidence.json").write_bytes(_canonical(result["evidence"]))
    (directory / "validation.json").write_bytes(_canonical(result["validation"]))
    (directory / "bundle-manifest.json").write_bytes(
        _canonical(
            {
                "source_observations_sha256": hashlib.sha256(observations).hexdigest(),
                "source_observations_size_bytes": len(observations),
                "protected_inventory_sha256": hashlib.sha256(inventory).hexdigest(),
                "protected_inventory_size_bytes": len(inventory),
                "live_protection_sha256": hashlib.sha256(protection).hexdigest(),
                "live_protection_size_bytes": len(protection),
                "candidate": result["evidence"]["candidate_commit"],
            }
        )
    )


def main(argv: list[str] | None = None) -> int:
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True)
    parser.add_argument("--pr", type=int, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        result = collect(GitHubClient(args.repo), args.pr)
        write_bundle(result, args.output)
    except EvidenceError as exc:
        print(
            json.dumps(
                {
                    "valid": False,
                    "errors": [str(exc)],
                    "claims": {"required_ci_verified": False},
                },
                indent=2,
            )
        )
        return 2
    print(
        json.dumps(
            {
                "base": result["evidence"]["base_commit"],
                "head": result["evidence"]["head_commit"],
                "candidate": result["evidence"]["candidate_commit"],
                **result["validation"],
            },
            indent=2,
        )
    )
    return 0 if result["validation"]["valid"] else 1


if __name__ == "__main__":
    sys.exit(main())
