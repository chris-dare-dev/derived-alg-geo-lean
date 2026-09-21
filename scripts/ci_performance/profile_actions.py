#!/usr/bin/env python3
"""Profile Actions run fixtures and make conservative cache-reuse decisions.

The tool is intentionally offline by default.  A future collector may convert
GitHub API responses to the input shape; this module only normalizes immutable
run/job/step data and never changes a workflow or cache.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


SCHEMA_VERSION = 1
FULL_SHA = re.compile(r"^[0-9a-fA-F]{40}$")
EVENTS = {"pull_request", "push", "merge_group", "workflow_dispatch"}
TERMINAL_CONCLUSIONS = {"success", "neutral", "failure", "cancelled", "timed_out", "skipped"}
PHASES = (
    "queue",
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


def _phase(name: str) -> str:
    lowered = name.casefold()
    patterns = (
        ("checkout", "checkout"),
        ("reset", "reset"),
        ("restore", "cache_restore"),
        ("cache", "cache_restore"),
        ("audit", "audit"),
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
    phases = {name: 0.0 for name in PHASES}
    jobs = payload.get("jobs", [])
    if not isinstance(jobs, list) or not jobs:
        raise ValueError("jobs must be a non-empty array")
    failures: list[dict[str, Any]] = []
    pending_jobs: list[dict[str, Any]] = []
    job_rows: list[dict[str, Any]] = []
    phase_intervals: dict[str, list[tuple[datetime, datetime]]] = {
        name: [] for name in PHASES
    }
    phase_intervals["queue"].append(
        (_timestamp(payload["created_at"]), _timestamp(payload["run_started_at"]))
    )
    job_intervals: list[tuple[datetime, datetime]] = []
    terminal_jobs = 0
    for job_index, job in enumerate(jobs):
        if not isinstance(job, dict):
            raise ValueError(f"jobs[{job_index}] must be an object")
        if not isinstance(job.get("id"), int) or job["id"] <= 0:
            raise ValueError(f"jobs[{job_index}].id must be a positive integer")
        job_name = job.get("name")
        if not isinstance(job_name, str) or not job_name.strip():
            raise ValueError(f"jobs[{job_index}].name is required")
        conclusion = job.get("conclusion")
        if conclusion is not None and conclusion not in TERMINAL_CONCLUSIONS | {"queued", "in_progress"}:
            raise ValueError(f"{job_name}.conclusion is not recognized")
        is_terminal = conclusion in TERMINAL_CONCLUSIONS
        if is_terminal:
            terminal_jobs += 1
        if is_terminal and (not job.get("started_at") or not job.get("completed_at")):
            raise ValueError(f"{job_name} is terminal but lacks complete timestamps")
        job_duration = None
        if job.get("started_at") and job.get("completed_at"):
            job_duration = _seconds(job["started_at"], job["completed_at"])
            job_intervals.append((_timestamp(job["started_at"]), _timestamp(job["completed_at"])))
        row = {
            "id": job["id"],
            "name": job_name,
            "duration_seconds": job_duration,
            "conclusion": conclusion,
        }
        job_rows.append(row)
        failure = _failure_class(job)
        if failure:
            failures.append({"job": job_name, "class": failure, "conclusion": job.get("conclusion")})
        elif not is_terminal:
            pending_jobs.append({"job": job_name, "conclusion": conclusion or "pending"})
        steps = job.get("steps", [])
        if not isinstance(steps, list):
            raise ValueError(f"{job_name}.steps must be an array")
        if is_terminal and not steps:
            raise ValueError(f"{job_name} is terminal but has no step data")
        for step_index, step in enumerate(steps):
            if not isinstance(step, dict):
                raise ValueError(f"{job_name}.steps[{step_index}] must be an object")
            if not step.get("started_at") or not step.get("completed_at"):
                if is_terminal:
                    raise ValueError(f"{job_name}.steps[{step_index}] lacks complete timestamps")
                continue
            phase = _phase(str(step.get("name", "")))
            start = _timestamp(step["started_at"])
            end = _timestamp(step["completed_at"])
            _seconds(step["started_at"], step["completed_at"])
            phase_intervals[phase].append((start, end))
    if terminal_jobs == 0:
        raise ValueError("run has no terminal job; pending data is not a completed profile")
    phases = {name: _union_seconds(intervals) for name, intervals in phase_intervals.items()}
    phases = {name: round(value, 3) for name, value in phases.items()}
    return {
        "schema_version": SCHEMA_VERSION,
        "run": {
            "id": payload["id"],
            "attempt": payload["run_attempt"],
            "head_sha": payload["head_sha"],
            "base_sha": payload.get("base_sha"),
            "event": payload["event"],
            "platform": payload.get("platform", "unknown"),
            "status": payload.get("status"),
            "conclusion": payload.get("conclusion"),
        },
        "phase_durations_seconds": phases,
        "jobs": job_rows,
        "failures": failures,
        "pending_jobs": pending_jobs,
        "wall_clock_seconds": _union_seconds(job_intervals),
        "terminal_job_count": terminal_jobs,
        "measurement_notes": payload.get("measurement_notes", []),
    }


def replay_decision(case: Any) -> dict[str, Any]:
    if not isinstance(case, dict):
        raise ValueError("replay case must be an object")
    reasons: list[str] = []
    identity = case.get("identity")
    if not isinstance(identity, dict):
        return {"decision": "full_rebuild", "reasons": ["missing cache identity"]}
    for key in ("toolchain", "manifest", "target", "options", "pins", "emitter"):
        if not identity.get(key):
            reasons.append(f"missing identity: {key}")
    for key in ("renames", "deletions", "unknown_inputs"):
        value = identity.get(key)
        if value:
            reasons.append(f"unsafe input: {key}")
    if identity.get("dependency_graph_complete") is not True:
        reasons.append("dependency graph is not proven complete")
    if reasons:
        return {"decision": "full_rebuild", "reasons": reasons}
    changed = identity.get("changed_files")
    if not isinstance(changed, list):
        return {"decision": "full_rebuild", "reasons": ["changed_files is not an array"]}
    if any(not isinstance(item, str) or not item.strip() for item in changed):
        return {"decision": "full_rebuild", "reasons": ["changed_files contains an invalid path"]}
    if len(set(changed)) != len(changed):
        return {"decision": "full_rebuild", "reasons": ["changed_files contains duplicates"]}
    if not changed:
        if identity.get("direct_changes") not in ([], None) or identity.get("transitive_changes") not in (
            [],
            None,
        ):
            return {
                "decision": "full_rebuild",
                "reasons": ["empty changed_files requires empty dependency classifications"],
            }
        return {"decision": "cache_reuse", "reasons": ["exact identity and no changed inputs"]}
    direct = identity.get("direct_changes")
    transitive = identity.get("transitive_changes")
    if not isinstance(direct, list) or not isinstance(transitive, list):
        return {
            "decision": "full_rebuild",
            "reasons": ["changed inputs have no complete dependency classification"],
        }
    partitions = direct + transitive
    if any(not isinstance(item, str) or not item.strip() for item in partitions):
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
            "reasons": ["complete dependency graph and explicit changed inputs"],
            "changed_files": changed,
        }
    return {"decision": "full_rebuild", "reasons": ["changed inputs have no proven dependency classification"]}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    profile = sub.add_parser("profile")
    profile.add_argument("fixture", type=Path)
    profile.add_argument("--output", type=Path)
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
        payload = _load(args.fixture)
        if args.command == "profile":
            result = profile_run(payload)
        elif isinstance(payload, list):
            result = [
                {"name": item.get("name", f"case-{index}"), **replay_decision(item)}
                for index, item in enumerate(payload)
            ]
        else:
            result = replay_decision(payload)
        _emit(result, args.output)
    except ValueError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
