#!/usr/bin/env python3
"""Read-only, reproducible observations about a merged pull request.

This is a post-publication auditor, not a merge guard. A Git tree ID includes
file modes, symlink targets, names and deletions. A receipt is only a snapshot:
``verify`` fetches the provider again; its JSON digest authenticates nothing.
Historical review identity, merge-time protection and the PR test-merge commit
are intentionally unknown until a trusted source supplies them.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime
from pathlib import Path
from typing import Any

if __package__:
    from .ci_github_evidence import EvidenceError, GitHubClient, _commit, _sha
else:
    from ci_github_evidence import EvidenceError, GitHubClient, _commit, _sha


SCHEMA = "derived-alg-geo-lean.publication-audit/v1"
UNKNOWN = "not_evaluable"


def _date(value: Any) -> datetime | None:
    if not isinstance(value, str):
        return None
    try:
        result = datetime.fromisoformat(value.replace("Z", "+00:00"))
    except ValueError:
        return None
    return result if result.tzinfo is not None else None


def _digest(value: dict[str, Any]) -> str:
    payload = {key: item for key, item in value.items() if key != "receipt_sha256"}
    raw = json.dumps(payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def tree_comparison(reviewed_tree: str | None, published_tree: str) -> str:
    """Compare whole object IDs; caller must establish final review provenance."""
    if reviewed_tree is None:
        return UNKNOWN
    return "identical" if reviewed_tree == published_tree else "different"


def _check_summary(check: dict[str, Any]) -> dict[str, Any]:
    app = check.get("app") if isinstance(check.get("app"), dict) else {}
    suite = check.get("check_suite") if isinstance(check.get("check_suite"), dict) else {}
    return {
        "id": check.get("id"),
        "name": check.get("name"),
        "head_sha": check.get("head_sha"),
        "suite_id": suite.get("id"),
        "app_slug": app.get("slug"),
        "status": check.get("status"),
        "conclusion": check.get("conclusion"),
        "completed_at": check.get("completed_at"),
        "url": check.get("html_url"),
    }


def _checks(client: GitHubClient, commit: str) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    checks = client.get_all(f"/commits/{commit}/check-runs?filter=all", key="check_runs")
    statuses = client.get_all(f"/commits/{commit}/statuses")
    ids: set[int] = set()
    for check in checks:
        identifier = check.get("id")
        if not isinstance(identifier, int) or isinstance(identifier, bool) or identifier <= 0:
            raise EvidenceError("check run has invalid ID")
        if identifier in ids or check.get("head_sha") != commit:
            raise EvidenceError("duplicate or foreign check run")
        ids.add(identifier)
    for status in statuses:
        if status.get("sha") != commit:
            raise EvidenceError("foreign commit status")
    return checks, statuses


def _ci_observation(
    client: GitHubClient, head: str, merged_at: datetime, checks: list[dict[str, Any]]
) -> dict[str, Any]:
    """Report a CI observation, never historical required-check compliance."""
    matches = [
        check for check in checks
        if check.get("name") == "ci"
        and isinstance(check.get("app"), dict)
        and check["app"].get("slug") == "github-actions"
    ]
    runs = client.get_all(f"/actions/runs?head_sha={head}", key="workflow_runs")
    ci_runs = [
        run for run in runs
        if run.get("name") == "CI"
        and run.get("path") == ".github/workflows/ci.yml"
        and run.get("event") == "pull_request"
        and run.get("head_sha") == head
    ]
    result: dict[str, Any] = {
        "state": UNKNOWN,
        "reason": "CI check or workflow run is missing or ambiguous",
        "checks": [_check_summary(check) for check in matches],
        "workflow_runs": [
            {key: run.get(key) for key in ("id", "run_attempt", "check_suite_id", "status", "conclusion", "html_url", "updated_at")}
            for run in ci_runs
        ],
        "tested_candidate": UNKNOWN,
        "historical_required_policy": UNKNOWN,
    }
    if not matches:
        result["state"] = "no_ci_check_observed"
        return result
    if len(matches) != 1 or len(ci_runs) != 1:
        return result
    check, run = matches[0], ci_runs[0]
    suite = check.get("check_suite")
    attempt = run.get("run_attempt")
    if (
        not isinstance(suite, dict)
        or suite.get("id") != run.get("check_suite_id")
        or not isinstance(attempt, int)
        or isinstance(attempt, bool)
        or attempt < 1
        or not isinstance(run.get("id"), int)
    ):
        result["reason"] = "check-suite or attempt identity is ambiguous"
        return result
    completed = _date(check.get("completed_at"))
    if completed is None or completed > merged_at:
        result["state"] = "not_successful_before_merge"
        result["reason"] = "CI check completed after merge or has no completion time"
        return result
    if attempt != 1 or _date(run.get("updated_at")) is None or _date(run["updated_at"]) > merged_at:
        result["reason"] = "workflow was rerun or updated after merge; merge-time attempt is ambiguous"
        return result
    if (
        check.get("status") == "completed"
        and check.get("conclusion") == "success"
        and run.get("status") == "completed"
        and run.get("conclusion") == "success"
    ):
        result["state"] = "observed_success_before_merge"
        result["reason"] = "head check and CI workflow agree; tested merge candidate is unverified"
    else:
        result["state"] = "not_successful_before_merge"
        result["reason"] = "head check or CI workflow did not succeed"
    return result


def collect(
    client: GitHubClient, number: int, reviewed_commit: str | None = None
) -> dict[str, Any]:
    """Derive a receipt from GitHub; a supplied commit is not proof of review."""
    if not isinstance(number, int) or isinstance(number, bool) or number < 1:
        raise EvidenceError("PR number must be positive")
    reviewed = _sha(reviewed_commit, "reviewed commit") if reviewed_commit else None
    pr = client.get_object(f"/pulls/{number}")
    if pr.get("number") != number or pr.get("merged") is not True:
        raise EvidenceError("pull request is not the requested merged PR")
    merged_at = _date(pr.get("merged_at"))
    if merged_at is None:
        raise EvidenceError("merged PR has no valid merge timestamp")
    head_record = pr.get("head")
    base_record = pr.get("base")
    if not isinstance(head_record, dict) or not isinstance(base_record, dict):
        raise EvidenceError("PR revision identity is incomplete")
    head = _sha(head_record.get("sha"), "PR head")
    base = _sha(base_record.get("sha"), "PR recorded base")
    published = _sha(pr.get("merge_commit_sha"), "published commit")
    published_tree, parents = _commit(client, published)
    head_tree, _ = _commit(client, head)
    if not parents:
        raise EvidenceError("published commit has no parent")
    reviewed_tree = _commit(client, reviewed)[0] if reviewed else None
    head_checks, head_statuses = _checks(client, head)
    published_checks, published_statuses = _checks(client, published)
    ci = _ci_observation(client, head, merged_at, head_checks)
    auxiliary = [
        _check_summary(check) for check in head_checks
        if check.get("name") != "ci" and check.get("conclusion") in {"failure", "timed_out", "cancelled", "action_required"}
        and _date(check.get("completed_at")) is not None
        and _date(check["completed_at"]) <= merged_at
    ]
    post_ci = [
        _check_summary(check) for check in published_checks
        if check.get("name") == "ci" and isinstance(check.get("app"), dict)
        and check["app"].get("slug") == "github-actions"
    ]
    post_state = UNKNOWN
    if len(post_ci) == 1:
        if post_ci[0]["status"] == "completed":
            post_state = "passed" if post_ci[0]["conclusion"] == "success" else "failed"
        else:
            post_state = "pending"
    receipt: dict[str, Any] = {
        "schema": SCHEMA,
        "repository": client.repository,
        "pull_request": number,
        "pull_request_url": pr.get("html_url"),
        "merged_at": pr["merged_at"],
        "recorded_base": base,
        "head_commit": head,
        "head_tree": head_tree,
        "reviewed_commit": reviewed,
        "reviewed_tree": reviewed_tree,
        "review_provenance": UNKNOWN,
        "published_commit": published,
        "published_parent": parents[0],
        "published_tree": published_tree,
        "published_equals_head_tree": published_tree == head_tree,
        "published_equals_supplied_reviewed_tree": tree_comparison(reviewed_tree, published_tree),
        "recorded_base_equals_published_parent": base == parents[0],
        "premerge_ci": ci,
        "auxiliary_failed_checks": auxiliary,
        "head_commit_statuses": head_statuses,
        "postmerge_ci": {"state": post_state, "checks": post_ci},
        "published_commit_statuses": published_statuses,
        "merge_time_readiness": UNKNOWN,
        "operationally_verified": False,
    }
    receipt["receipt_sha256"] = _digest(receipt)
    return receipt


def verify_saved(
    client: GitHubClient, number: int, saved: Any, reviewed_commit: str | None = None
) -> dict[str, Any]:
    """Recollect primary observations; a self-rehashed edit cannot verify."""
    if not isinstance(saved, dict) or saved.get("receipt_sha256") != _digest(saved):
        raise EvidenceError("saved receipt digest is invalid")
    fresh = collect(client, number, reviewed_commit)
    if saved != fresh:
        raise EvidenceError("saved receipt differs from current provider observations")
    return fresh


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repository", help="GitHub owner/name")
    parser.add_argument("pr", type=int, help="merged pull request number")
    parser.add_argument("--reviewed-commit", help="commit claimed to be finally reviewed; provenance remains unknown")
    parser.add_argument("--verify", type=Path, help="compare saved receipt with fresh provider observations")
    parser.add_argument("--out", type=Path, help="write receipt to a separate file")
    args = parser.parse_args(argv)
    try:
        client = GitHubClient(args.repository)
        if args.verify is not None:
            saved = json.loads(args.verify.read_text(encoding="utf-8"))
            receipt = verify_saved(client, args.pr, saved, args.reviewed_commit)
        else:
            receipt = collect(client, args.pr, args.reviewed_commit)
        body = json.dumps(receipt, sort_keys=True, indent=2, ensure_ascii=False) + "\n"
        if args.out:
            args.out.write_text(body, encoding="utf-8")
        else:
            sys.stdout.write(body)
    except (EvidenceError, OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"publication audit unavailable: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    from _output import force_utf8_output

    force_utf8_output()
    raise SystemExit(main())
