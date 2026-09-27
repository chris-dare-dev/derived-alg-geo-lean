#!/usr/bin/env python3
"""Profile Actions run fixtures or captured attempts and evaluate replay cases.

This module is offline: it reads immutable observations and never changes a
workflow, production check, or cache.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path, PurePosixPath
from typing import Any


SCHEMA_VERSION = 2
FULL_SHA = re.compile(r"^[0-9a-fA-F]{40}$")
EVENTS = {"pull_request", "push", "merge_group", "workflow_dispatch"}
TERMINAL_CONCLUSIONS = {"success", "neutral", "failure", "cancelled", "timed_out", "skipped"}
PHASES = (
    "queue",
    "dependency_wait",
    "checkout",
    "reset",
    "cache_restore",
    "lake_build",
    "audit",
    "emitter",
    "contract",
    "upload",
    "other",
)


def _canonical_repo_path(value: Any) -> bool:
    """Accept only normalized POSIX paths relative to the repository root."""
    if not isinstance(value, str) or not value or value != value.strip():
        return False
    if "\\" in value or any(ord(char) < 32 or ord(char) == 127 for char in value):
        return False
    path = PurePosixPath(value)
    parts = value.split("/")
    return (
        not path.is_absolute()
        and not re.match(r"^[A-Za-z]:", value)
        and all(part not in {"", ".", ".."} for part in parts)
        and path.as_posix() == value
    )


def _load(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot load JSON fixture {path}: {exc}") from exc


def _timestamp(value: Any) -> datetime:
    if not isinstance(value, str) or not value.strip():
        raise ValueError("timestamp is required")
    text = value.replace("Z", "+00:00")
    try:
        parsed = datetime.fromisoformat(text)
    except ValueError as exc:
        raise ValueError(f"invalid timestamp {value!r}") from exc
    if parsed.tzinfo is None or parsed.utcoffset() is None:
        raise ValueError(f"timestamp must include a timezone offset: {value!r}")
    return parsed.astimezone(timezone.utc)


def _seconds(start: Any, end: Any) -> float:
    delta = (_timestamp(end) - _timestamp(start)).total_seconds()
    if delta < 0:
        raise ValueError(f"end timestamp precedes start timestamp: {start!r} -> {end!r}")
    return round(delta, 3)


def _observed_seconds(
    start: Any, end: Any, label: str, anomalies: list[str]
) -> float | None:
    """Keep provider timestamp inversions visible without inventing durations."""
    try:
        return _seconds(start, end)
    except ValueError as exc:
        if "end timestamp precedes start timestamp" not in str(exc):
            raise
        anomalies.append(f"{label}: {exc}")
        return None


def _phase(name: str) -> str:
    lowered = name.casefold()
    patterns = (
        ("leanprover/lean-action@", "lake_build"),
        ("checkout", "checkout"),
        ("reset", "reset"),
        ("restore", "cache_restore"),
        ("cache", "cache_restore"),
        ("audit", "audit"),
        ("single instantiation", "audit"),
        ("emit", "emitter"),
        ("contract", "contract"),
        ("upload", "upload"),
        ("lake", "lake_build"),
        ("build", "lake_build"),
    )
    for needle, result in patterns:
        if needle in lowered:
            return result
    return "other"


def _failure_class(job: dict[str, Any]) -> str | None:
    if job.get("conclusion") in {"cancelled", "timed_out", "failure", "success", "neutral"}:
        conclusion = job.get("conclusion")
        if conclusion in {"success", "neutral"}:
            return None
        if conclusion == "cancelled":
            return "cancelled"
        if conclusion == "timed_out":
            return "timeout"
        return str(job.get("failure_class") or "unknown")
    return None


def _union_seconds(intervals: list[tuple[datetime, datetime]]) -> float:
    if not intervals:
        return 0.0
    ordered = sorted(intervals)
    total = 0.0
    current_start, current_end = ordered[0]
    for start, end in ordered[1:]:
        if start <= current_end:
            current_end = max(current_end, end)
            continue
        total += (current_end - current_start).total_seconds()
        current_start, current_end = start, end
    total += (current_end - current_start).total_seconds()
    return round(total, 3)


def profile_run(payload: Any) -> dict[str, Any]:
    if not isinstance(payload, dict):
        raise ValueError("run fixture must be an object")
    required = ("id", "run_attempt", "head_sha", "event", "status", "created_at", "run_started_at")
    missing = [field for field in required if field not in payload]
    if missing:
        raise ValueError("run fixture is missing " + ", ".join(missing))
    if not isinstance(payload["id"], int) or payload["id"] <= 0:
        raise ValueError("run id must be a positive integer")
    if not isinstance(payload["run_attempt"], int) or payload["run_attempt"] <= 0:
        raise ValueError("run attempt must be a positive integer")
    if not isinstance(payload["head_sha"], str) or not FULL_SHA.fullmatch(payload["head_sha"]):
        raise ValueError("head_sha must be a full 40-character SHA")
    if payload.get("base_sha") is not None and (
        not isinstance(payload["base_sha"], str) or not FULL_SHA.fullmatch(payload["base_sha"])
    ):
        raise ValueError("base_sha must be a full 40-character SHA when present")
    if payload["event"] not in EVENTS:
        raise ValueError("event is not recognized")
    if payload.get("status") not in {"completed", "queued", "in_progress"}:
        raise ValueError("status must be completed, queued, or in_progress")
    jobs = payload.get("jobs", [])
    if not isinstance(jobs, list) or not jobs:
        raise ValueError("jobs must be a non-empty array")
    anomalies: list[str] = []
    attempt_created = (
        _timestamp(payload["attempt_created_at"])
        if payload.get("attempt_created_at") is not None else None
    )
    attempt_started = _timestamp(payload["run_started_at"])
    run_start_delay = _observed_seconds(
        payload["created_at"], payload["run_started_at"], "workflow start", anomalies
    )
    job_needs = payload.get("job_needs")
    if job_needs is not None and (
        not isinstance(job_needs, dict)
        or any(
            not isinstance(name, str)
            or not isinstance(needs, list)
            or any(not isinstance(item, str) for item in needs)
            for name, needs in job_needs.items()
        )
    ):
        raise ValueError("job_needs must map job names to prerequisite name arrays")
    failures: list[dict[str, Any]] = []
    pending_jobs: list[dict[str, Any]] = []
    job_rows: list[dict[str, Any]] = []
    seen_ids: set[int] = set()
    seen_names: set[str] = set()
    phase_intervals: dict[str, list[tuple[datetime, datetime]]] = {
        name: [] for name in PHASES
    }
    phase_unknown: set[str] = set()
    job_intervals: list[tuple[datetime, datetime]] = []
    terminal_jobs = 0
    incomplete_job_interval = False
    carried_forward_jobs: list[dict[str, Any]] = []
    uncertain_jobs: list[dict[str, Any]] = []
    for job_index, job in enumerate(jobs):
        if not isinstance(job, dict):
            raise ValueError(f"jobs[{job_index}] must be an object")
        if isinstance(job.get("id"), bool) or not isinstance(job.get("id"), int) or job["id"] <= 0:
            raise ValueError(f"jobs[{job_index}].id must be a positive integer")
        if job["id"] in seen_ids:
            raise ValueError(f"jobs[{job_index}].id is duplicated")
        seen_ids.add(job["id"])
        job_name = job.get("name")
        if not isinstance(job_name, str) or not job_name.strip():
            raise ValueError(f"jobs[{job_index}].name is required")
        if job_name in seen_names:
            raise ValueError(f"job name is duplicated: {job_name}")
        seen_names.add(job_name)
        conclusion = job.get("conclusion")
        if conclusion is not None and conclusion not in TERMINAL_CONCLUSIONS | {"queued", "in_progress"}:
            raise ValueError(f"{job_name}.conclusion is not recognized")
        is_terminal = conclusion in TERMINAL_CONCLUSIONS
        start_time = _timestamp(job["started_at"]) if job.get("started_at") else None
        end_time = _timestamp(job["completed_at"]) if job.get("completed_at") else None
        carried_forward = (
            attempt_created is not None
            and end_time is not None
            and end_time < attempt_created
        )
        attribution_uncertain = (
            attempt_created is not None
            and not carried_forward
            and start_time is not None
            and start_time < attempt_created
            and (start_time < attempt_started or end_time is None)
        )
        if carried_forward:
            carried_forward_jobs.append({
                "id": job["id"], "name": job_name,
                "started_at": job.get("started_at"),
                "completed_at": job.get("completed_at"),
                "conclusion": conclusion,
            })
            anomalies.append(f"{job_name}: job execution predates the selected attempt")
        elif attribution_uncertain:
            uncertain_jobs.append({
                "id": job["id"], "name": job_name,
                "started_at": job.get("started_at"),
                "completed_at": job.get("completed_at"),
                "conclusion": conclusion,
            })
            anomalies.append(f"{job_name}: job overlaps the selected attempt boundary")
            phase_unknown.update(PHASES[2:])
            incomplete_job_interval = True
        elif is_terminal:
            terminal_jobs += 1
        if is_terminal and not carried_forward and not attribution_uncertain and (not job.get("started_at") or not job.get("completed_at")):
            anomalies.append(f"{job_name}: terminal job lacks complete timestamps")
        job_duration = None
        if not carried_forward and not attribution_uncertain and job.get("started_at") and job.get("completed_at"):
            job_duration = _observed_seconds(
                job["started_at"], job["completed_at"], f"{job_name} job", anomalies
            )
            if job_duration is not None:
                job_intervals.append((_timestamp(job["started_at"]), _timestamp(job["completed_at"])))
        if is_terminal and not carried_forward and not attribution_uncertain and conclusion != "skipped" and job_duration is None:
            incomplete_job_interval = True
        row = {
            "id": job["id"],
            "name": job_name,
            "carried_forward": carried_forward,
            "attribution_uncertain": attribution_uncertain,
            "runner_name": job.get("runner_name"),
            "labels": job.get("labels", []),
            "duration_seconds": job_duration,
            "conclusion": conclusion,
            "created_at": job.get("created_at"),
            "started_at": job.get("started_at"),
            "completed_at": job.get("completed_at"),
            "dispatch_wait_seconds": None,
            "runner_queue_seconds": None,
            "dependency_wait_seconds": None,
            "scheduler_gap_seconds": None,
        }
        job_rows.append(row)
        if carried_forward or attribution_uncertain:
            continue
        failure = _failure_class(job)
        if failure:
            failures.append({"job": job_name, "class": failure, "conclusion": job.get("conclusion")})
        elif not is_terminal:
            pending_jobs.append({"job": job_name, "conclusion": conclusion or "pending"})
        steps = job.get("steps", [])
        if not isinstance(steps, list):
            raise ValueError(f"{job_name}.steps must be an array")
        if is_terminal and not steps:
            anomalies.append(f"{job_name}: terminal job has no step data")
            if conclusion != "skipped" and (job_duration is None or job_duration > 0):
                phase_unknown.update(PHASES[2:])
        for step_index, step in enumerate(steps):
            if not isinstance(step, dict):
                raise ValueError(f"{job_name}.steps[{step_index}] must be an object")
            if not step.get("started_at") or not step.get("completed_at"):
                if is_terminal:
                    anomalies.append(f"{job_name}.steps[{step_index}] lacks complete timestamps")
                    phase_unknown.add(_phase(str(step.get("name", ""))))
                continue
            phase = _phase(str(step.get("name", "")))
            start = _timestamp(step["started_at"])
            end = _timestamp(step["completed_at"])
            if _observed_seconds(
                step["started_at"], step["completed_at"],
                f"{job_name}.steps[{step_index}]", anomalies,
            ) is not None:
                phase_intervals[phase].append((start, end))
            else:
                phase_unknown.add(phase)
    if terminal_jobs == 0:
        raise ValueError("run has no terminal job; pending data is not a completed profile")
    completion_by_name: dict[str, datetime] = {}
    for row in job_rows:
        if row["completed_at"] and (
            row["duration_seconds"] is not None or row["carried_forward"]
        ):
            completion_by_name[row["name"]] = _timestamp(row["completed_at"])
    workflow_created = _timestamp(payload["created_at"])
    queue_complete = True
    for row in job_rows:
        if row["carried_forward"] or row["attribution_uncertain"]:
            continue
        created_at, started_at = row["created_at"], row["started_at"]
        if not created_at or not started_at:
            queue_complete = False
            continue
        dispatch = _observed_seconds(
            created_at, started_at, f"{row['name']} dispatch wait", anomalies
        )
        row["dispatch_wait_seconds"] = dispatch
        if dispatch is None or not isinstance(job_needs, dict) or row["name"] not in job_needs:
            queue_complete = False
            continue
        prerequisite_names = job_needs[row["name"]]
        if any(name not in completion_by_name for name in prerequisite_names):
            queue_complete = False
            continue
        created = _timestamp(created_at)
        started = _timestamp(started_at)
        # GitHub often creates a dependent job only after its prerequisites
        # finish. Job created_at -> started_at alone is therefore not its
        # dependency wait. Keep the later scheduler gap separate from queue.
        ready = max([workflow_created, *(completion_by_name[name] for name in prerequisite_names)])
        if ready > started or created < workflow_created:
            anomalies.append(f"{row['name']}: job started before its prerequisites completed")
            queue_complete = False
            continue
        eligible = max(created, ready)
        row["dependency_wait_seconds"] = round((ready - workflow_created).total_seconds(), 3)
        row["scheduler_gap_seconds"] = round(max(0.0, (created - ready).total_seconds()), 3)
        row["runner_queue_seconds"] = round((started - eligible).total_seconds(), 3)
        if ready > workflow_created:
            phase_intervals["dependency_wait"].append((workflow_created, ready))
        if started > eligible:
            phase_intervals["queue"].append((eligible, started))
    phases: dict[str, float | None] = {
        name: None if name in phase_unknown else _union_seconds(intervals)
        for name, intervals in phase_intervals.items()
    }
    if not queue_complete:
        phases["queue"] = None
        phases["dependency_wait"] = None
    return {
        "schema_version": SCHEMA_VERSION,
        "run": {
            "id": payload["id"],
            "attempt": payload["run_attempt"],
            "head_sha": payload["head_sha"],
            "base_sha": payload.get("base_sha"),
            "event": payload["event"],
            "platform": payload.get("platform", "unknown"),
            "cache_state": payload.get("cache_state", "unknown"),
            "host_pressure": payload.get("host_pressure"),
            "status": payload.get("status"),
            "conclusion": payload.get("conclusion"),
        },
        "phase_durations_seconds": phases,
        "jobs": job_rows,
        "failures": failures,
        "pending_jobs": pending_jobs,
        "wall_clock_seconds": (
            _union_seconds(job_intervals) if job_intervals and not incomplete_job_interval
            else None
        ),
        "workflow_start_delay_seconds": run_start_delay,
        "terminal_job_count": terminal_jobs,
        "measurement_notes": payload.get("measurement_notes", []),
        "timestamp_anomalies": anomalies,
        "carried_forward_jobs": carried_forward_jobs,
        "attribution_uncertain_jobs": uncertain_jobs,
    }


def profile_bundle(bundle: Any, job_needs: dict[str, list[str]] | None = None) -> dict[str, Any]:
    """Normalize one captured provider attempt without inventing missing context."""
    if not isinstance(bundle, dict) or bundle.get("schema_version") not in {1, 2}:
        raise ValueError("provider bundle schema is not recognized")
    run, attempt, jobs = (bundle.get(key) for key in ("run", "attempt", "jobs"))
    if not isinstance(run, dict) or not isinstance(attempt, dict) or not isinstance(jobs, list):
        raise ValueError("provider bundle needs run, attempt, and jobs")
    if bundle["schema_version"] == 2:
        pages = bundle.get("jobs_pages")
        if not isinstance(pages, list) or not pages:
            raise ValueError("provider bundle has no retained jobs pages")
        flattened: list[dict[str, Any]] = []
        total: int | None = None
        for index, page in enumerate(pages):
            if not isinstance(page, dict):
                raise ValueError("provider jobs page is malformed")
            response = page.get("response")
            links = page.get("pagination_links")
            headers = page.get("response_headers")
            if (
                not isinstance(page.get("request_url"), str)
                or not isinstance(response, dict)
                or not isinstance(response.get("jobs"), list)
                or not isinstance(links, dict)
                or not isinstance(headers, dict)
            ):
                raise ValueError("provider jobs page envelope is malformed")
            count = response.get("total_count")
            if isinstance(count, bool) or not isinstance(count, int) or count < 0:
                raise ValueError("provider jobs page lacks total_count")
            if total is not None and count != total:
                raise ValueError("provider jobs page totals differ")
            total = count
            flattened.extend(response["jobs"])
            next_url = links.get("next")
            if index + 1 < len(pages):
                next_page = pages[index + 1]
                if not isinstance(next_page, dict) or next_url != next_page.get("request_url"):
                    raise ValueError("provider jobs page chain is inconsistent")
            elif next_url is not None:
                raise ValueError("provider jobs page chain is incomplete")
        if flattened != jobs or total != len(jobs):
            raise ValueError("retained jobs pages differ from flattened jobs")
    if (
        run.get("id") != attempt.get("id")
        or run.get("head_sha") != attempt.get("head_sha")
        or not isinstance(attempt.get("run_attempt"), int)
        or any(
            not isinstance(job, dict)
            or job.get("run_id") != run.get("id")
            or job.get("run_attempt") != attempt.get("run_attempt")
            or job.get("head_sha") != run.get("head_sha")
            for job in jobs
        )
    ):
        raise ValueError("provider bundle identity is inconsistent")
    for job in jobs:
        labels = job.get("labels") or []
        if not isinstance(labels, list):
            raise ValueError("provider job labels must be an array")
    payload = {
        key: attempt.get(key)
        for key in ("id", "run_attempt", "head_sha", "event", "status", "conclusion", "created_at", "run_started_at")
    }
    payload.update({
        "jobs": jobs,
        "attempt_created_at": attempt.get("created_at"),
        "job_needs": job_needs,
        "platform": "unknown",
        "cache_state": "unknown",
        "host_pressure": None,
        "measurement_notes": [
            "Raw GitHub Actions attempt; cache state and host pressure require separate observations.",
            "Job prerequisites were supplied separately." if job_needs is not None
            else "Job prerequisites are unknown; runner queue is unattributed.",
        ],
    })
    result = profile_run(payload)
    platform_classes = set()
    for row in result["jobs"]:
        if row["carried_forward"] or row["attribution_uncertain"]:
            continue
        if "self-hosted" in row["labels"]:
            platform_classes.add("self-hosted")
        elif "ubuntu-latest" in row["labels"]:
            platform_classes.add("github-hosted-ubuntu")
        else:
            platform_classes.add("unknown")
    if result["attribution_uncertain_jobs"]:
        result["run"]["platform"] = "unknown"
    elif len(platform_classes) == 1:
        result["run"]["platform"] = next(iter(platform_classes))
    elif len(platform_classes) > 1:
        result["run"]["platform"] = "mixed"
    result["provider_bundle"] = {
        "repository": bundle.get("repository"),
        "captured_at_utc": bundle.get("captured_at_utc"),
        "run_path": bundle.get("provider_paths", {}).get("run"),
        "attempt_path": bundle.get("provider_paths", {}).get("attempt"),
        "job_count": len(jobs),
        "job_page_count": len(bundle["jobs_pages"]) if bundle["schema_version"] == 2 else None,
    }
    return result


def _load_verified_bundle(path: Path) -> dict[str, Any]:
    raw = path.read_bytes()
    sidecar = _load(path.with_suffix(path.suffix + ".sha256.json"))
    if (
        not isinstance(sidecar, dict)
        or sidecar.get("bundle_sha256") != hashlib.sha256(raw).hexdigest()
        or sidecar.get("bundle_size_bytes") != len(raw)
        or sidecar.get("bundle_file") != path.name
    ):
        raise ValueError("provider bundle digest sidecar does not match")
    bundle = json.loads(raw)
    if (
        not isinstance(bundle, dict)
        or bundle.get("repository") != sidecar.get("repository")
        or bundle.get("run", {}).get("id") != sidecar.get("run_id")
        or bundle.get("attempt", {}).get("run_attempt") != sidecar.get("run_attempt")
    ):
        raise ValueError("provider bundle identity differs from sidecar")
    return bundle


def replay_decision(case: Any) -> dict[str, Any]:
    if not isinstance(case, dict):
        raise ValueError("replay case must be an object")
    reasons: list[str] = []
    base = case.get("base_identity")
    candidate = case.get("candidate_identity")
    if not isinstance(base, dict) or not isinstance(candidate, dict):
        return {
            "decision": "full_rebuild",
            "reasons": ["explicit base and candidate cache identities are required"],
        }
    for label in ("base_commit", "candidate_commit"):
        value = case.get(label)
        if not isinstance(value, str) or not FULL_SHA.fullmatch(value):
            reasons.append(f"missing or invalid revision: {label}")
    for key in (
        "toolchain", "manifest", "target", "options", "pins", "emitter",
        "instances", "exported_axioms",
    ):
        if not isinstance(base.get(key), str) or not base[key]:
            reasons.append(f"missing base identity: {key}")
        if not isinstance(candidate.get(key), str) or not candidate[key]:
            reasons.append(f"missing candidate identity: {key}")
        if key in base and key in candidate and base[key] != candidate[key]:
            reasons.append(f"changed identity: {key}")
    for key in ("renames", "deletions", "unknown_inputs"):
        value = case.get(key)
        if not isinstance(value, list) or value:
            reasons.append(f"unsafe or unrecorded input: {key}")
    if case.get("dependency_graph_complete") is not True:
        reasons.append("dependency graph is not proven complete")
    if case.get("change_inventory_complete") is not True:
        reasons.append("revision change inventory is not proven complete")
    if reasons:
        return {"decision": "full_rebuild", "reasons": reasons}
    changed = case.get("changed_files")
    if not isinstance(changed, list):
        return {"decision": "full_rebuild", "reasons": ["changed_files is not an array"]}
    if any(not _canonical_repo_path(item) for item in changed):
        return {"decision": "full_rebuild", "reasons": ["changed_files contains an invalid path"]}
    if len(set(changed)) != len(changed):
        return {"decision": "full_rebuild", "reasons": ["changed_files contains duplicates"]}
    if changed and case["base_commit"] == case["candidate_commit"]:
        return {
            "decision": "full_rebuild",
            "reasons": ["identical revisions cannot have changed inputs"],
        }
    if not changed:
        if case.get("direct_changes") != [] or case.get("transitive_changes") != []:
            return {
                "decision": "full_rebuild",
                "reasons": ["empty changed_files requires empty dependency classifications"],
            }
        if case["base_commit"] != case["candidate_commit"]:
            return {
                "decision": "full_rebuild",
                "reasons": ["different revisions with no changed inputs need full verification"],
            }
        return {"decision": "cache_reuse", "reasons": ["identical revision and exact identity"]}
    direct = case.get("direct_changes")
    transitive = case.get("transitive_changes")
    if not isinstance(direct, list) or not isinstance(transitive, list):
        return {
            "decision": "full_rebuild",
            "reasons": ["changed inputs have no complete dependency classification"],
        }
    partitions = direct + transitive
    if any(not _canonical_repo_path(item) for item in partitions):
        return {
            "decision": "full_rebuild",
            "reasons": ["dependency classification contains an invalid path"],
        }
    if len(set(partitions)) != len(partitions):
        return {
            "decision": "full_rebuild",
            "reasons": ["dependency classifications contain duplicates or overlap"],
        }
    if set(partitions) != set(changed):
        return {
            "decision": "full_rebuild",
            "reasons": ["dependency classifications are not an exact partition of changed_files"],
        }
    if direct or transitive:
        return {
            "decision": "targeted_replay",
            "reasons": ["caller-attested dependency graph and explicit changed inputs"],
            "changed_files": changed,
        }
    return {"decision": "full_rebuild", "reasons": ["changed inputs have no proven dependency classification"]}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    profile = sub.add_parser("profile")
    profile.add_argument("fixture", type=Path)
    profile.add_argument("--output", type=Path)
    bundle = sub.add_parser("profile-bundle")
    bundle.add_argument("bundle", type=Path)
    bundle.add_argument("--job-needs", type=Path)
    bundle.add_argument("--output", type=Path)
    replay = sub.add_parser("replay")
    replay.add_argument("fixture", type=Path)
    replay.add_argument("--output", type=Path)
    return parser


def _emit(value: Any, output: Path | None) -> None:
    rendered = json.dumps(value, indent=2, sort_keys=True) + "\n"
    if output is None:
        print(rendered, end="")
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(rendered, encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "profile":
            result = profile_run(_load(args.fixture))
        elif args.command == "profile-bundle":
            needs = _load(args.job_needs) if args.job_needs else None
            result = profile_bundle(_load_verified_bundle(args.bundle), needs)
        else:
            payload = _load(args.fixture)
            if isinstance(payload, list):
                result = [
                    {"name": item.get("name", f"case-{index}"), **replay_decision(item)}
                    for index, item in enumerate(payload)
                ]
            else:
                result = replay_decision(payload)
        _emit(result, args.output)
    except (OSError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
