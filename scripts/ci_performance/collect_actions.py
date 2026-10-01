#!/usr/bin/env python3
"""Collect an exact GitHub Actions run attempt without changing provider state.

The JSON bundle keeps the provider's run, attempt, and every jobs page. Its
sidecar binds the bytes to a digest; neither file is a gate verdict.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

if __package__:
    from ..ci_github_evidence import EvidenceError, GitHubClient
else:
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    from scripts.ci_github_evidence import EvidenceError, GitHubClient


def _positive(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f"{label} must be a positive integer")
    return value


def _snapshot_identity(run: dict[str, Any]) -> tuple[Any, ...]:
    return tuple(run.get(key) for key in (
        "id", "run_attempt", "head_sha", "event", "path", "status", "conclusion",
    ))


def collect_attempt(
    client: GitHubClient, run_id: int, attempt: int | None = None
) -> dict[str, Any]:
    """Fetch complete attempt jobs and reject a changing run during collection."""
    run_id = _positive(run_id, "run ID")
    run_path = f"/actions/runs/{run_id}"
    before = client.get_object(run_path)
    if before.get("id") != run_id:
        raise ValueError("provider returned another run ID")
    if before.get("status") != "completed":
        raise ValueError("run is not completed; job and step pages may still change")
    current_attempt = _positive(before.get("run_attempt"), "provider run attempt")
    selected = current_attempt if attempt is None else _positive(attempt, "selected attempt")
    if selected > current_attempt:
        raise ValueError("selected attempt does not exist on the provider run")
    attempt_path = f"{run_path}/attempts/{selected}"
    attempt_run = client.get_object(attempt_path)
    if (
        attempt_run.get("id") != run_id
        or attempt_run.get("run_attempt") != selected
        or attempt_run.get("head_sha") != before.get("head_sha")
        or attempt_run.get("status") != "completed"
    ):
        raise ValueError("attempt identity differs from the parent run")
    jobs_path = f"{attempt_path}/jobs"
    jobs_pages = client.get_pages(jobs_path, key="jobs")
    jobs = [job for page in jobs_pages for job in page["response"]["jobs"]]
    seen: set[int] = set()
    for job in jobs:
        job_id = _positive(job.get("id"), "job ID")
        if job_id in seen:
            raise ValueError("provider returned a duplicate job ID")
        seen.add(job_id)
        if (
            job.get("run_id") != run_id
            or job.get("run_attempt") != selected
            or job.get("head_sha") != before.get("head_sha")
        ):
            raise ValueError("job is bound to another run, attempt, or revision")
    after = client.get_object(run_path)
    if _snapshot_identity(after) != _snapshot_identity(before):
        raise ValueError("provider run changed during collection")
    return {
        "schema_version": 2,
        "repository": client.repository,
        "captured_at_utc": datetime.now(timezone.utc).isoformat(timespec="microseconds"),
        "provider_paths": {
            "run": run_path,
            "attempt": attempt_path,
            "jobs": jobs_path,
            "jobs_pagination": "all_link_pages_and_advertised_total_checked",
        },
        "run": before,
        "attempt": attempt_run,
        "jobs_pages": jobs_pages,
        "jobs": jobs,
    }


def write_snapshot(bundle: dict[str, Any], output: Path) -> dict[str, Any]:
    """Write one immutable raw bundle and a separate SHA-256 sidecar."""
    if output.exists() or output.with_suffix(output.suffix + ".sha256.json").exists():
        raise ValueError("snapshot output already exists; choose a new path")
    raw = (json.dumps(bundle, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode()
    manifest = {
        "schema_version": bundle["schema_version"],
        "repository": bundle["repository"],
        "run_id": bundle["run"]["id"],
        "run_attempt": bundle["attempt"]["run_attempt"],
        "captured_at_utc": bundle["captured_at_utc"],
        "bundle_sha256": hashlib.sha256(raw).hexdigest(),
        "bundle_size_bytes": len(raw),
        "bundle_file": output.name,
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("xb") as stream:
        stream.write(raw)
    sidecar = output.with_suffix(output.suffix + ".sha256.json")
    with sidecar.open("x", encoding="utf-8") as stream:
        stream.write(json.dumps(manifest, sort_keys=True, indent=2) + "\n")
    return manifest


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", required=True)
    parser.add_argument("--run-id", type=int, required=True)
    parser.add_argument("--attempt", type=int)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args(argv)
    try:
        bundle = collect_attempt(
            GitHubClient(args.repository), args.run_id, args.attempt
        )
        manifest = write_snapshot(bundle, args.output)
    except (EvidenceError, ValueError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(json.dumps(manifest, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
