"""Pure reconciliation for the known dynamic AI Scan provider identity.

The GitHub adapter and the provider-neutral contract use the same match and
state rules. This module performs no API reads and grants no scan verdict from
the colour of a check.
"""

from __future__ import annotations

from typing import Any


WORKFLOW_ID = 360047049
BOT_ID = 62310815
PATH = "dynamic/agents/github-advanced-security"
NAME = "github-advanced-security"
PRODUCER = "github-actions/AI Scan"
PENDING = {"requested", "waiting", "pending", "queued", "in_progress"}


def _nonempty(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _positive(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def matching_checks(checks: list[dict[str, Any]]) -> list[dict[str, Any]]:
    return [
        check for check in checks
        if check.get("name") == NAME
        and isinstance(check.get("app"), dict)
        and check["app"].get("slug") == "github-actions"
    ]


def matching_runs(
    runs: list[dict[str, Any]], pr_number: int, head: str
) -> list[dict[str, Any]]:
    return [
        run for run in runs
        if run.get("workflow_id") == WORKFLOW_ID
        and run.get("path") == PATH
        and run.get("event") == "dynamic"
        and run.get("head_sha") == head
        and run.get("name") == f"Code scanning AI findings on PR #{pr_number}"
        and isinstance(run.get("actor"), dict)
        and run["actor"].get("id") == BOT_ID
        and run["actor"].get("login") == "github-advanced-security[bot]"
    ]


def reconcile(
    scan: Any, head: Any, pr_number: int | None, gate: dict[str, Any] | None
) -> tuple[str | None, list[str]]:
    """Reject a retained scan record that contradicts its own raw facts."""
    if not isinstance(scan, dict):
        return None, ["evidence.security_scan is required for the dynamic gate"]
    errors: list[str] = []
    if scan.get("head_sha") != head or not _nonempty(head):
        errors.append("evidence.security_scan.head_sha differs from the PR head")
    if not _positive(pr_number):
        errors.append("evidence.security_scan cannot identify the pull request")
    setting = scan.get("setting")
    setting_state: str | None = None
    if (
        not isinstance(setting, dict)
        or setting.get("head_sha") != head
        or setting.get("api_path") != "/code-scanning/ai-scan"
    ):
        errors.append("evidence.security_scan.setting is not bound to the PR head and provider API")
    else:
        setting_state = setting.get("state")
        if not isinstance(setting_state, str) or setting_state not in {"enabled", "disabled", "unknown"}:
            errors.append("evidence.security_scan.setting has an unknown state")
        response = setting.get("response")
        if response is None:
            if setting_state != "unknown" or not _nonempty(setting.get("error")):
                errors.append("evidence.security_scan.setting contradicts its API error")
        elif not isinstance(response, dict) or "error" in setting:
            errors.append("evidence.security_scan.setting response and error disagree")
        else:
            raw = response.get("pr_scan")
            expected = raw if isinstance(raw, str) and raw in {"enabled", "disabled"} else "unknown"
            if setting_state != expected:
                errors.append("evidence.security_scan.setting contradicts its raw response")
        if not all(_nonempty(setting.get(key)) for key in ("requested_at_utc", "completed_at_utc")):
            errors.append("evidence.security_scan.setting lacks observation times")
    query = scan.get("run_query")
    runs = scan.get("head_workflow_runs")
    if (
        not isinstance(query, dict)
        or query.get("api_path") != f"/actions/runs?head_sha={head}"
        or query.get("pagination") != "all_link_pages_and_advertised_total_checked"
        or not all(_nonempty(query.get(key)) for key in ("requested_at_utc", "completed_at_utc"))
        or not isinstance(runs, list)
        or any(not isinstance(run, dict) or not _positive(run.get("id")) for run in runs)
        or isinstance(query.get("total_observed"), bool)
        or not isinstance(query.get("total_observed"), int)
        or query["total_observed"] != len(runs)
    ):
        errors.append("evidence.security_scan.run_query does not retain a complete head-run observation")
        runs = []
    run_ids = scan.get("matching_run_ids")
    check_ids = scan.get("matching_check_ids")
    for label, ids in (("matching_run_ids", run_ids), ("matching_check_ids", check_ids)):
        if not isinstance(ids, list) or any(not _positive(item) for item in ids) or len(ids) != len(set(ids)):
            errors.append(f"evidence.security_scan.{label} must list unique positive IDs")
    if errors:
        return None, errors
    assert isinstance(runs, list) and isinstance(run_ids, list) and isinstance(check_ids, list)
    assert isinstance(pr_number, int) and isinstance(head, str)
    exact_runs = matching_runs(runs, pr_number, head)
    if run_ids != [run["id"] for run in exact_runs]:
        errors.append("evidence.security_scan matching runs differ from the retained provider query")
    state = scan.get("state")
    if gate is None:
        if check_ids:
            errors.append("evidence.security_scan has a check but omits its gate")
        if not exact_runs:
            expected = {
                "enabled": "missing", "disabled": "disabled_by_setting",
                "unknown": "provider_state_unknown",
            }.get(setting_state)
            if state != expected or any(
                key in scan for key in ("run_id", "run_attempt", "run_status", "check_id", "raw_conclusion")
            ):
                errors.append("evidence.security_scan absent-run state contradicts its setting")
        elif len(exact_runs) == 1:
            run = exact_runs[0]
            if (
                state != "pending"
                or run.get("status") not in PENDING
                or run.get("conclusion") is not None
                or scan.get("run_id") != run["id"]
                or not _positive(run.get("run_attempt"))
                or scan.get("run_attempt") != run.get("run_attempt")
                or scan.get("run_status") != run.get("status")
                or "check_id" in scan or "raw_conclusion" in scan
            ):
                errors.append("evidence.security_scan pending run differs from its retained workflow")
        else:
            errors.append("evidence.security_scan has ambiguous runs without a gate")
    else:
        try:
            provider_id = int(gate.get("provider_id"))
        except (TypeError, ValueError):
            provider_id = None
        status = gate.get("status")
        expected = {
            "failed": "unclassified_failure",
            "pending": "pending",
            "unknown": "execution_observed_result_unknown",
        }.get(status) if isinstance(status, str) else None
        run = exact_runs[0] if len(exact_runs) == 1 else {}
        run_status = run.get("status")
        run_conclusion = run.get("conclusion")
        outcome_consistent = (
            status == "failed" and run_status == "completed" and run_conclusion == "failure"
        ) or (
            status == "pending" and isinstance(run_status, str)
            and run_status in PENDING and run_conclusion is None
        ) or (
            status == "unknown" and run_status == "completed"
            and run_conclusion is not None and run_conclusion != "failure"
        )
        if (
            expected is None or state != expected
            or len(exact_runs) != 1
            or not outcome_consistent
            or not _positive(provider_id)
            or check_ids != [provider_id]
            or run_ids != [gate.get("run_id")]
            or scan.get("run_id") != gate.get("run_id")
            or scan.get("run_attempt") != gate.get("run_attempt")
            or scan.get("run_attempt") != run.get("run_attempt")
            or "run_status" in scan
            or scan.get("check_id") != provider_id
            or scan.get("raw_conclusion") != gate.get("conclusion")
            or scan.get("raw_conclusion") != str(run.get("conclusion") or "unknown")
        ):
            errors.append("evidence.security_scan disagrees with its observed gate or run")
    return state if not errors and isinstance(state, str) else None, errors
