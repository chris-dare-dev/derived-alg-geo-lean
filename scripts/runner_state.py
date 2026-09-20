#!/usr/bin/env python3
"""Fail-closed identity and admission checks for shared self-hosted runners.

This is intentionally a portable, report-only/admission utility.  It does not
delete worktrees, kill processes, modify runner services, or change workflow
routing.  An operator or future bootstrap can feed it a snapshot of active
jobs and the physical host capacity before admitting another writable job.
"""

from __future__ import annotations

import argparse
import json
import ntpath
import os
import sys
from pathlib import Path
from typing import Any


WRITABLE_PATHS = (
    "checkout",
    "git_index",
    "lake_build",
    "lake_packages",
    "elan",
    "temp",
    "outputs",
    "artifacts",
)
REQUIRED_IDENTITY = ("host_id", "runner_id", "job_id", "run_id", "run_attempt", "namespace")


def _load(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot load JSON snapshot {path}: {exc}") from exc


def _positive_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value > 0


def canonical_path(value: Any) -> str:
    """Resolve symlink/junction-like aliases and normalize Windows spelling."""

    if not isinstance(value, str) or not value.strip():
        raise ValueError("path must be a non-empty string")
    raw = os.path.expandvars(os.path.expanduser(value.strip()))
    windows_style = bool(ntpath.splitdrive(raw)[0]) or "\\" in raw
    if windows_style:
        return ntpath.normcase(ntpath.normpath(raw)).rstrip("\\") or "\\"
    # ntpath normalization is useful on Linux when validating a Windows runner
    # snapshot captured on another host; Path.resolve supplies local symlink
    # resolution when the path exists here.
    try:
        resolved = str(Path(raw).resolve(strict=False))
    except OSError:
        resolved = raw
    normalized = resolved.replace("/", "\\").rstrip("\\") or "\\"
    return ntpath.normcase(ntpath.normpath(normalized))


def _overlap(left: str, right: str) -> bool:
    a = left.rstrip("\\")
    b = right.rstrip("\\")
    return a == b or a.startswith(b + "\\") or b.startswith(a + "\\")


def validate_record(record: Any) -> list[str]:
    errors: list[str] = []
    if not isinstance(record, dict):
        return ["job record must be an object"]
    for field in REQUIRED_IDENTITY:
        value = record.get(field)
        if field in {"run_id", "run_attempt"}:
            if not _positive_int(value):
                errors.append(f"{field} must be a positive integer")
        elif not isinstance(value, str) or not value.strip():
            errors.append(f"{field} is required")
    resources = record.get("resources")
    if not isinstance(resources, dict):
        errors.append("resources must be an object")
    else:
        for field in ("cpu_threads", "memory_bytes", "disk_bytes"):
            if not _positive_int(resources.get(field)):
                errors.append(f"resources.{field} must be a positive integer")
    paths = record.get("paths")
    if not isinstance(paths, dict):
        return errors + ["paths must be an object"]
    for name in WRITABLE_PATHS:
        if name not in paths:
            errors.append(f"paths.{name} is required")
            continue
        value = paths[name]
        if not isinstance(value, dict):
            errors.append(f"paths.{name} must be an object")
            continue
        try:
            canonical_path(value.get("path"))
        except ValueError as exc:
            errors.append(f"paths.{name}.path: {exc}")
        if not isinstance(value.get("writable"), bool):
            errors.append(f"paths.{name}.writable must be boolean")
    return errors


def _path_rows(record: dict[str, Any]) -> list[tuple[str, str, bool]]:
    rows: list[tuple[str, str, bool]] = []
    for name, value in record.get("paths", {}).items():
        if not isinstance(value, dict):
            continue
        try:
            rows.append((name, canonical_path(value.get("path")), bool(value.get("writable"))))
        except ValueError:
            continue
    return rows


def validate_snapshot(snapshot: Any) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []
    if not isinstance(snapshot, dict):
        return {"valid": False, "errors": ["snapshot must be an object"], "warnings": []}
    capacity = snapshot.get("capacity")
    if not isinstance(capacity, dict):
        errors.append("capacity must be an object")
        capacity = {}
    for field in ("cpu_threads", "memory_bytes", "disk_bytes"):
        if not _positive_int(capacity.get(field)):
            errors.append(f"capacity.{field} must be a positive integer")
    jobs = snapshot.get("jobs")
    if not isinstance(jobs, list) or not jobs:
        errors.append("jobs must be a non-empty array")
        jobs = []
    namespaces: set[str] = set()
    host_ids: set[str] = set()
    totals = {"cpu_threads": 0, "memory_bytes": 0, "disk_bytes": 0}
    valid_jobs: list[dict[str, Any]] = []
    for index, job in enumerate(jobs):
        prefix = f"jobs[{index}]"
        job_errors = validate_record(job)
        errors.extend(f"{prefix}: {error}" for error in job_errors)
        if not isinstance(job, dict) or job_errors:
            continue
        if job["namespace"] in namespaces:
            errors.append(f"{prefix}: duplicate namespace {job['namespace']!r}")
        namespaces.add(job["namespace"])
        host_ids.add(job["host_id"])
        valid_jobs.append(job)
        for field in totals:
            totals[field] += job["resources"][field]
    if len(host_ids) > 1:
        warnings.append("snapshot includes more than one physical host; compare hosts separately")
    for field, total in totals.items():
        if _positive_int(capacity.get(field)) and total > capacity[field]:
            errors.append(f"resource budget exceeded for {field}: {total} > {capacity[field]}")

    path_owners: list[tuple[str, str, str, bool]] = []
    for job in valid_jobs:
        for path_name, path, writable in _path_rows(job):
            if not writable:
                continue
            for other_job, other_name, other_path, other_writable in path_owners:
                if other_job == job["namespace"]:
                    # A checkout necessarily contains its own index, build,
                    # output, and artifact children. Isolation is a cross-job
                    # invariant; intra-job containment is expected.
                    continue
                if other_writable and _overlap(path, other_path):
                    errors.append(
                        "writable path collision: "
                        f"{job['namespace']}:{path_name}={path} overlaps "
                        f"{other_job}:{other_name}={other_path}"
                    )
            path_owners.append((job["namespace"], path_name, path, writable))
    return {
        "valid": not errors,
        "errors": errors,
        "warnings": warnings,
        "job_count": len(valid_jobs),
        "resource_totals": totals,
    }


def acquire_lease(record: dict[str, Any], lease_dir: Path) -> dict[str, Any]:
    errors = validate_record(record)
    if errors:
        raise ValueError("cannot acquire invalid record: " + "; ".join(errors))
    lease_dir.mkdir(parents=True, exist_ok=True)
    lease_path = lease_dir / f"{record['namespace']}.json"
    payload = json.dumps(record, sort_keys=True, indent=2) + "\n"
    try:
        descriptor = os.open(lease_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
    except FileExistsError as exc:
        raise ValueError(f"lease already exists; recovery must inspect it: {lease_path}") from exc
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(payload)
    except Exception:
        lease_path.unlink(missing_ok=True)
        raise
    return {"acquired": True, "lease": str(lease_path), "namespace": record["namespace"]}


def release_lease(record: dict[str, Any], lease_dir: Path) -> dict[str, Any]:
    errors = validate_record(record)
    if errors:
        raise ValueError("cannot release invalid record: " + "; ".join(errors))
    lease_path = lease_dir / f"{record['namespace']}.json"
    if not lease_path.is_file() or lease_path.is_symlink():
        raise ValueError(f"lease is absent or unsafe: {lease_path}")
    current = _load(lease_path)
    if not isinstance(current, dict) or current.get("namespace") != record["namespace"]:
        raise ValueError("lease owner does not match requested namespace")
    lease_path.unlink()
    return {"released": True, "lease": str(lease_path), "namespace": record["namespace"]}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    report = sub.add_parser("report")
    report.add_argument("snapshot", type=Path)
    admit = sub.add_parser("admit")
    admit.add_argument("record", type=Path)
    admit.add_argument("--lease-dir", type=Path, required=True)
    release = sub.add_parser("release")
    release.add_argument("record", type=Path)
    release.add_argument("--lease-dir", type=Path, required=True)
    return parser


def main(argv: list[str] | None = None) -> int:
    args = _parser().parse_args(argv)
    try:
        if args.command == "report":
            result = validate_snapshot(_load(args.snapshot))
        elif args.command == "admit":
            result = acquire_lease(_load(args.record), args.lease_dir)
        else:
            result = release_lease(_load(args.record), args.lease_dir)
    except ValueError as exc:
        print(json.dumps({"valid": False, "errors": [str(exc)]}, indent=2))
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result.get("valid", result.get("acquired", result.get("released", False))) else 1


if __name__ == "__main__":
    sys.exit(main())
