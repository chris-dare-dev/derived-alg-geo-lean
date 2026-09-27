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
    payloads = premerge.get("payloads")
    if not isinstance(payloads, dict):
        raise EvidenceError("premerge evidence bundle does not retain provider artifact payloads")
    artifact_payloads: dict[str, str] = {}
    for artifact in evidence.get("artifacts", []):
        path = artifact.get("path") if isinstance(artifact, dict) else None
        content = payloads.get(path) if isinstance(path, str) else None
        if not isinstance(content, bytes):
            raise EvidenceError("premerge provider artifact payload is missing")
        artifact_payloads[path] = content.decode("utf-8")
    if set(artifact_payloads) != {artifact["path"] for artifact in evidence["artifacts"]}:
        raise EvidenceError("premerge provider artifact payload set is incomplete")
    receipt["premerge"]["artifact_payloads"] = artifact_payloads
    receipt["receipt_sha256"] = ci_publication.receipt_digest(receipt)
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
    """Rebuild CI1.01 claims from protected policy and live provider facts."""

    ci_publication.verify_receipt(receipt)
    premerge = receipt["premerge"]
    pr_number = receipt["pull_request"]["number"]
    base = _sha(premerge.get("base_commit"), "receipt base")
    head = _sha(premerge.get("head_commit"), "receipt head")
    contract_evidence = _required_object(
        premerge.get("contract_evidence"), "receipt CI1.01 evidence"
    )
    run_summary = _required_object(premerge.get("workflow_run"), "receipt workflow run")
    run_id = _positive(premerge.get("run_id"), "receipt workflow run ID")
    attempt = _positive(premerge.get("run_attempt"), "receipt workflow run attempt")
    run = client.get_object(f"/actions/runs/{run_id}")
    expected_run = (
        run_id,
        attempt,
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
    live_associations = run.get("pull_requests")
    matching_associations = [
        {
            "number": item.get("number"),
            "base_sha": item["base"].get("sha"),
            "head_sha": item["head"].get("sha"),
        }
        for item in live_associations or []
        if isinstance(item, dict)
        and item.get("number") == pr_number
        and isinstance(item.get("base"), dict)
        and item["base"].get("sha") == base
        and isinstance(item.get("head"), dict)
        and item["head"].get("sha") == head
    ]
    recorded_associations = run_summary.get("pull_requests")
    if len(matching_associations) == 1:
        if recorded_associations != matching_associations:
            raise EvidenceError("receipt PR association differs from the live CI run")
    elif not live_associations:
        # GitHub currently clears Actions-run PR associations after merge. The
        # receipt retains the premerge association, and the published-PR check
        # plus the run-bound candidate's ordered base/head parents re-establish
        # the same revisions below. A nonempty but conflicting association is
        # never accepted as this fallback.
        pr = client.get_object(f"/pulls/{pr_number}")
        if (
            pr.get("state") != "closed"
            or pr.get("merged") is not True
            or _sha(_required_object(pr.get("base"), "associated PR base").get("sha"), "associated PR base") != base
            or _sha(_required_object(pr.get("head"), "associated PR head").get("sha"), "associated PR head") != head
            or recorded_associations != [{"number": pr_number, "base_sha": base, "head_sha": head}]
        ):
            raise EvidenceError("live CI run no longer proves the receipt PR/base/head association")
    else:
        raise EvidenceError("live CI run is associated with a different PR/base/head")

    candidate, candidate_tree, candidate_parents, _ = _candidate(
        client, base, head, run
    )
    provider_binding = _required_object(
        contract_evidence.get("provider_binding"), "receipt provider binding"
    )
    if (
        candidate != premerge.get("candidate_commit")
        or candidate_tree != premerge.get("candidate_tree")
        or candidate_parents != provider_binding.get("parents")
    ):
        raise EvidenceError(
            "receipt CI candidate differs from the current run artifact or Git object"
        )

    try:
        inventory = json.loads(_blob(client, base, "scripts/ci_gate_inventory.json"))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise EvidenceError("receipt base gate inventory is invalid JSON") from exc
    if ci_contract.validate_inventory(inventory):
        raise EvidenceError("receipt base gate inventory is invalid")
    if inventory.get("repository") != client.repository:
        raise EvidenceError("receipt base gate inventory names another repository")
    validation = ci_contract.validate_evidence(
        inventory,
        contract_evidence,
        trusted_base_commit=base,
        trusted_head_commit=head,
        trusted_inventory_sha256=ci_contract._canonical_sha256(inventory),
    )
    if not validation.get("valid"):
        errors = validation.get("errors")
        detail = "; ".join(errors) if isinstance(errors, list) else "unknown validation error"
        raise EvidenceError("receipt CI1.01 evidence is invalid: " + detail)
    try:
        candidate_toolchain = _blob(client, candidate, "lean-toolchain").decode("utf-8").strip()
    except UnicodeDecodeError as exc:
        raise EvidenceError("candidate lean-toolchain is not UTF-8") from exc
    if not candidate_toolchain or contract_evidence.get("toolchain") != candidate_toolchain:
        raise EvidenceError("receipt toolchain differs from the candidate Git blob")
    candidate_pins = {
        path: hashlib.sha256(_blob(client, candidate, path)).hexdigest()
        for path in sorted(ci_contract.REQUIRED_PINS)
    }
    if contract_evidence.get("pins") != candidate_pins:
        raise EvidenceError("receipt pin digests differ from candidate Git blobs")
    definitions = {gate["id"]: gate for gate in inventory["gates"]}
    applicable_auxiliary_ids = sorted(
        gate_id
        for gate_id, definition in definitions.items()
        if definition.get("class") == "auxiliary"
        and ci_contract._event_applies(definition, contract_evidence)
    )
    required_ids = premerge.get("required_gate_ids")
    if required_ids != validation.get("required_gates"):
        raise EvidenceError("receipt required-gate set differs from the protected inventory")
    if premerge.get("applicable_auxiliary_gate_ids") != applicable_auxiliary_ids:
        raise EvidenceError("receipt auxiliary-gate set differs from the protected inventory")
    validation_claims = validation.get("claims", {})
    claims = premerge.get("claims")
    if not isinstance(claims, dict) or claims.get("required_ci_verified") is not True:
        raise EvidenceError("receipt does not establish required CI")

    expected_contract_gate_records = []
    expected_artifacts: dict[str, dict[str, Any]] = {}
    provider_payload_facts: dict[str, dict[str, Any]] = {}
    for gate in contract_evidence.get("gates", []):
        definition = definitions.get(gate.get("id"))
        if not isinstance(definition, dict):
            raise EvidenceError("receipt contains a gate absent from protected inventory")
        expected_contract_gate_records.append(
            {
                "id": gate.get("id"),
                "name": gate.get("name"),
                "provider_id": gate.get("provider_id"),
                "commit": gate.get("commit"),
                "status": gate.get("status"),
                "conclusion": gate.get("conclusion"),
                "class": definition.get("class"),
                "required": definition.get("required"),
            }
        )
    gate_records = premerge.get("gates")
    if gate_records != expected_contract_gate_records:
        raise EvidenceError("receipt flattened gates differ from CI1.01 contract evidence")

    suites = client.get_all(f"/commits/{head}/check-suites", key="check_suites")
    suite_map: dict[int, dict[str, Any]] = {}
    suite_summaries: dict[int, dict[str, Any]] = {}
    for suite in suites:
        suite_id = _positive(suite.get("id"), "live check suite ID")
        if suite_id in suite_map or suite.get("head_sha") != head:
            raise EvidenceError("duplicate or foreign live check suite")
        suite_map[suite_id] = suite
        app = suite.get("app") if isinstance(suite.get("app"), dict) else {}
        suite_summaries[suite_id] = {
            "id": suite_id,
            "head_sha": suite.get("head_sha"),
            "app_id": app.get("id"),
            "app_slug": app.get("slug"),
        }
    recorded_suites = premerge.get("check_suites")
    if not isinstance(recorded_suites, list):
        raise EvidenceError("receipt check-suite observations are malformed")
    try:
        recorded_suite_map = {
            _positive(item.get("id"), "receipt check suite ID"): item
            for item in recorded_suites
            if isinstance(item, dict)
        }
    except EvidenceError:
        raise
    if len(recorded_suite_map) != len(recorded_suites) or recorded_suite_map != suite_summaries:
        raise EvidenceError("receipt does not enumerate the complete live check-suite set")
    primary_suite_id = expected_run[2]
    primary_suite = suite_map.get(primary_suite_id)
    if primary_suite is None or _required_object(
        primary_suite.get("app"), "primary check-suite app"
    ).get("slug") != "github-actions":
        raise EvidenceError("live CI run is not bound to its GitHub Actions check suite")

    live_checks: dict[int, dict[str, Any]] = {}
    check_suite_by_id: dict[int, int] = {}
    for suite_id, suite in suite_map.items():
        checks = client.get_all(
            f"/check-suites/{suite_id}/check-runs?filter=all", key="check_runs"
        )
        if (
            suite.get("latest_check_runs_count") is not None
            and len(checks) < suite["latest_check_runs_count"]
        ):
            raise EvidenceError("live check suite run count is truncated")
        for check in checks:
            check_id = _positive(check.get("id"), "live check run ID")
            if check_id in live_checks or check.get("head_sha") != head:
                raise EvidenceError("duplicate or foreign live check run")
            live_checks[check_id] = check
            check_suite_by_id[check_id] = suite_id
    recorded_checks = premerge.get("check_runs")
    if not isinstance(recorded_checks, list):
        raise EvidenceError("receipt check-run observations are malformed")
    try:
        recorded_check_map = {
            _positive(item.get("id"), "receipt check run ID"): item
            for item in recorded_checks
            if isinstance(item, dict)
        }
    except EvidenceError:
        raise
    live_check_summaries = {
        check_id: ci_publication._provider_check_summary(check)
        for check_id, check in live_checks.items()
    }
    if len(recorded_check_map) != len(recorded_checks) or recorded_check_map != live_check_summaries:
        raise EvidenceError("receipt does not enumerate the complete live check-run set")

    statuses = client.get_all(f"/commits/{head}/statuses")
    status_map: dict[int, dict[str, Any]] = {}
    for item in statuses:
        status_id = _positive(item.get("id"), "live commit status ID")
        if status_id in status_map or item.get("sha") != head:
            raise EvidenceError("duplicate or foreign live commit status")
        status_map[status_id] = item
    recorded_statuses = premerge.get("statuses")
    if not isinstance(recorded_statuses, list):
        raise EvidenceError("receipt commit-status observations are malformed")
    live_status_summaries = {
        status_id: {
            "id": item.get("id"),
            "sha": item.get("sha"),
            "context": item.get("context"),
            "state": item.get("state"),
            "updated_at": item.get("updated_at"),
            "target_url": item.get("target_url"),
        }
        for status_id, item in status_map.items()
    }
    try:
        recorded_status_map = {
            _positive(item.get("id"), "receipt commit status ID"): item
            for item in recorded_statuses
            if isinstance(item, dict)
        }
    except EvidenceError:
        raise
    if len(recorded_status_map) != len(recorded_statuses) or recorded_status_map != live_status_summaries:
        raise EvidenceError("receipt does not enumerate the complete live commit-status set")

    observed_provider_ids = {
        str(gate.get("provider_id"))
        for gate in contract_evidence.get("gates", [])
        if isinstance(gate, dict)
    }
    unclassified_check_ids = sorted(
        str(check_id) for check_id in live_checks if str(check_id) not in observed_provider_ids
    )
    unclassified_status_ids = sorted(str(status_id) for status_id in status_map)
    if premerge.get("unclassified_check_ids") != unclassified_check_ids or premerge.get(
        "unclassified_status_ids"
    ) != unclassified_status_ids:
        raise EvidenceError("receipt unclassified-provider observations are incomplete")
    expected_claims = {
        "required_ci_verified": validation_claims.get("required_ci_verified") is True,
        "auxiliary_checks_healthy": validation_claims.get("auxiliary_checks_healthy") is True,
        "all_pipelines_green": (
            validation_claims.get("all_pipelines_green") is True
            and not unclassified_check_ids
            and not unclassified_status_ids
        ),
    }
    if claims != expected_claims:
        raise EvidenceError("receipt CI claims differ from validated provider evidence")

    primary_jobs = client.get_all(
        f"/actions/runs/{run_id}/attempts/{attempt}/jobs", key="jobs"
    )
    jobs_by_name: dict[str, list[dict[str, Any]]] = {}
    for job in primary_jobs:
        if (
            job.get("run_id") != run_id
            or job.get("run_attempt") != attempt
            or job.get("head_sha") != head
        ):
            raise EvidenceError("live workflow job is bound to another run, attempt, or head")
        jobs_by_name.setdefault(str(job.get("name")), []).append(job)

    for gate in contract_evidence.get("gates", []):
        definition = definitions.get(gate.get("id"))
        if not isinstance(definition, dict):
            raise EvidenceError("receipt contains a gate absent from protected inventory")
        try:
            provider_id = int(gate.get("provider_id"))
        except (TypeError, ValueError) as exc:
            raise EvidenceError("receipt gate provider ID is malformed") from exc
        if provider_id <= 0:
            raise EvidenceError("receipt gate provider ID is not positive")
        binding = definition.get("run_binding")
        if binding == "primary":
            matches = jobs_by_name.get(definition.get("name"), [])
            if len(matches) != 1:
                raise EvidenceError(f"primary gate {gate['id']!r} lacks one current workflow job")
            job = matches[0]
            check_url = job.get("check_run_url")
            job_id = _positive(job.get("id"), "live workflow job ID")
            if (
                check_url != f"{client._prefix}check-runs/{job_id}"
                or job_id != provider_id
                or job.get("status") != live_checks.get(provider_id, {}).get("status")
                or job.get("conclusion") != live_checks.get(provider_id, {}).get("conclusion")
                or check_suite_by_id.get(provider_id) != primary_suite_id
            ):
                raise EvidenceError(f"primary gate {gate['id']!r} differs from its live workflow job")
            actual = live_checks.get(provider_id)
            app = actual.get("app") if isinstance(actual, dict) and isinstance(actual.get("app"), dict) else {}
            primary_app = _required_object(primary_suite.get("app"), "primary suite app")
            if app.get("id") != primary_app.get("id") or app.get("slug") != "github-actions":
                raise EvidenceError(f"primary gate {gate['id']!r} has the wrong provider")
            artifact_commit = candidate
            artifact_run_fields = {"run_id": run_id, "run_attempt": attempt}
        elif binding == "check":
            matches = [
                (check_id, check)
                for check_id, check in live_checks.items()
                if check.get("name") == definition.get("name")
                and isinstance(check.get("app"), dict)
                and check["app"].get("slug") == definition.get("producer")
            ]
            if len(matches) != 1 or matches[0][0] != provider_id:
                raise EvidenceError(f"check gate {gate['id']!r} differs from its live provider run")
            actual = matches[0][1]
            artifact_commit = head
            artifact_run_fields = {}
        else:
            raise EvidenceError(
                f"receipt claims unsupported PR publication evidence for {binding!r} gate {gate['id']!r}"
            )
        status, conclusion = _conclusion(actual)
        if gate.get("status") != status or gate.get("conclusion") != conclusion:
            raise EvidenceError(f"receipt gate {gate['id']!r} differs from provider outcome")
        artifact_id = f"github-check-run-{provider_id}"
        artifact_path = f"results/check-run-{provider_id}.json"
        if gate.get("artifact_refs") != [artifact_id]:
            raise EvidenceError(f"receipt gate {gate['id']!r} does not reference its canonical provider artifact")
        expected_artifacts[artifact_id] = {
            "id": artifact_id,
            "path": artifact_path,
            "media_type": "application/json",
            "producer": definition["producer"],
            "kind": definition["artifact"],
            "subject": gate["id"],
            "commit": artifact_commit,
            **artifact_run_fields,
        }
        provider_payload_facts[artifact_id] = {
            "binding": binding,
            "check_run": actual,
            "job": job if binding == "primary" else None,
            "candidate": candidate,
            "head": head,
            "run_id": run_id,
            "run_attempt": attempt,
        }

    artifacts = contract_evidence.get("artifacts")
    if not isinstance(artifacts, list):
        raise EvidenceError("receipt CI1.01 artifacts are malformed")
    payload_texts = premerge.get("artifact_payloads")
    if not isinstance(payload_texts, dict):
        raise EvidenceError("receipt does not retain CI1.01 provider artifact payloads")
    if set(payload_texts) != {item["path"] for item in expected_artifacts.values()}:
        raise EvidenceError("receipt provider artifact payload set is incomplete")
    recorded_artifacts = {
        artifact.get("id"): artifact
        for artifact in artifacts
        if isinstance(artifact, dict)
    }
    if len(recorded_artifacts) != len(artifacts) or set(recorded_artifacts) != set(expected_artifacts):
        raise EvidenceError("receipt CI1.01 artifact records differ from live provider gates")
    for artifact_id, expected in expected_artifacts.items():
        artifact = recorded_artifacts[artifact_id]
        facts = provider_payload_facts[artifact_id]
        metadata = {key: value for key, value in artifact.items() if key not in {"sha256", "size_bytes"}}
        if metadata != expected:
            raise EvidenceError("receipt CI1.01 artifact metadata differs from live provider gates")
        payload_text = payload_texts.get(expected["path"])
        if not isinstance(payload_text, str):
            raise EvidenceError("receipt CI1.01 artifact payload is not retained text")
        payload_bytes = payload_text.encode("utf-8")
        if (
            hashlib.sha256(payload_bytes).hexdigest() != artifact.get("sha256")
            or len(payload_bytes) != artifact.get("size_bytes")
        ):
            raise EvidenceError("receipt CI1.01 artifact digest or size differs from retained bytes")
        try:
            payload_value = json.loads(payload_text)
        except json.JSONDecodeError as exc:
            raise EvidenceError("receipt CI1.01 artifact payload is invalid JSON") from exc
        if not isinstance(payload_value, dict) or _canonical(payload_value).decode("utf-8") != payload_text:
            raise EvidenceError("receipt CI1.01 artifact payload is not canonical JSON")
        if facts["binding"] == "primary":
            expected_keys = {"check_run", "job", "candidate", "run_id", "run_attempt"}
            snapshot_job = payload_value.get("job")
            job_fields = (
                "id", "name", "head_sha", "run_id", "run_attempt", "check_run_url",
                "status", "conclusion",
            )
            if not isinstance(snapshot_job, dict) or any(
                snapshot_job.get(field) != facts["job"].get(field) for field in job_fields
            ):
                raise EvidenceError("retained primary artifact job differs from its live workflow job")
            if (
                payload_value.get("candidate") != facts["candidate"]
                or payload_value.get("run_id") != facts["run_id"]
                or payload_value.get("run_attempt") != facts["run_attempt"]
            ):
                raise EvidenceError("retained primary artifact has a different candidate or workflow run")
        else:
            expected_keys = {"check_run", "head", "candidate"}
            if (
                payload_value.get("head") != facts["head"]
                or payload_value.get("candidate") != facts["candidate"]
            ):
                raise EvidenceError("retained check artifact has a different head or candidate")
        snapshot_check = payload_value.get("check_run")
        if (
            set(payload_value) != expected_keys
            or not isinstance(snapshot_check, dict)
            or ci_publication._provider_check_summary(snapshot_check)
            != ci_publication._provider_check_summary(facts["check_run"])
        ):
            raise EvidenceError("retained CI1.01 artifact check differs from its live provider run")


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
