#!/usr/bin/env python3
"""Fail-closed identity and admission checks for shared self-hosted runners.

This is intentionally a portable, report-only/admission utility.  It does not
delete worktrees, kill processes, modify runner services, or change workflow
routing.  An operator or future bootstrap can feed it a snapshot of active
jobs and the physical host capacity before admitting another writable job.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import ntpath
import os
import re
import stat
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
NAMESPACE_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]{0,127}$")
RESERVED_NAMESPACES = {"CON", "PRN", "AUX", "NUL"} | {
    f"{prefix}{number}" for prefix in ("COM", "LPT") for number in range(1, 10)
}
RESOURCE_FIELDS = ("cpu_threads", "memory_bytes", "disk_bytes")


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
        if not ntpath.isabs(raw):
            raise ValueError("path must be absolute")
        return ntpath.normcase(ntpath.normpath(raw)).rstrip("\\") or "\\"
    # ntpath normalization is useful on Linux when validating a Windows runner
    # snapshot captured on another host; Path.resolve supplies local symlink
    # resolution when the path exists here.
    if not Path(raw).is_absolute():
        raise ValueError("path must be absolute")
    try:
        resolved = str(Path(raw).resolve(strict=False))
    except OSError:
        resolved = raw
    normalized = resolved.replace("/", "\\").rstrip("\\") or "\\"
    # POSIX filesystems can distinguish Cache from cache. Keep their case
    # while using one separator for the overlap check below.
    return ntpath.normpath(normalized)


def _overlap(left: str, right: str) -> bool:
    a = left.rstrip("\\")
    b = right.rstrip("\\")
    return a == b or a.startswith(b + "\\") or b.startswith(a + "\\")


def _path_identity(value: Any) -> str:
    if not isinstance(value, dict):
        raise ValueError("path entry must be an object")
    raw = value.get("path")
    if not isinstance(raw, str) or not raw.strip():
        raise ValueError("path must be a non-empty string")
    windows_style = bool(ntpath.splitdrive(raw.strip())[0]) or "\\" in raw
    if windows_style:
        # Validate the observed path itself before trusting the collector's
        # OS-resolved identity. A drive-relative path must never be repaired by
        # a caller-supplied resolved_path.
        canonical_path(raw)
        resolved = value.get("resolved_path")
        if not isinstance(resolved, str) or not resolved.strip():
            raise ValueError("resolved_path is required for Windows path identity")
        return canonical_path(resolved)
    return canonical_path(raw)


def _record_digest(record: dict[str, Any]) -> str:
    encoded = json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _lease_path(record: dict[str, Any], lease_dir: Path) -> Path:
    namespace = record.get("namespace")
    if (
        not isinstance(namespace, str)
        or not NAMESPACE_RE.fullmatch(namespace)
        or namespace.upper() in RESERVED_NAMESPACES
    ):
        raise ValueError("namespace must contain only safe filename characters")
    root = lease_dir.resolve(strict=False)
    raw_candidate = root / f"{namespace}.json"
    if raw_candidate.is_symlink():
        raise ValueError(f"lease path is a symlink: {raw_candidate}")
    candidate = raw_candidate.resolve(strict=False)
    try:
        candidate.relative_to(root)
    except ValueError as exc:
        raise ValueError("lease namespace escapes the lease directory") from exc
    return candidate


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
    if isinstance(record.get("namespace"), str):
        namespace_upper = record["namespace"].upper()
        if not NAMESPACE_RE.fullmatch(record["namespace"]) or namespace_upper in RESERVED_NAMESPACES:
            errors.append("namespace must contain only safe filename characters")
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
            _path_identity(value)
        except ValueError as exc:
            errors.append(f"paths.{name}.path: {exc}")
        # These are mandatory mutable roots. In particular, Lake may update a
        # package tree originally linked by the seed helper. Letting a caller
        # mark any one of these read-only would skip collision detection.
        if value.get("writable") is not True:
            errors.append(f"paths.{name} must be job-owned writable state")
    if isinstance(paths.get("checkout"), dict):
        try:
            checkout = _path_identity(paths["checkout"])
            for name in ("lake_build", "lake_packages"):
                if isinstance(paths.get(name), dict):
                    resolved = _path_identity(paths[name])
                    if not resolved.startswith(checkout.rstrip("\\") + "\\"):
                        errors.append(f"paths.{name} resolves outside the job checkout")
        except ValueError:
            pass  # The invalid path was already reported above.
    return errors


def _path_rows(record: dict[str, Any]) -> list[tuple[str, str, bool]]:
    rows: list[tuple[str, str, bool]] = []
    for name, value in record.get("paths", {}).items():
        if not isinstance(value, dict):
            continue
        try:
            rows.append((name, _path_identity(value), bool(value.get("writable"))))
        except ValueError:
            continue
    return rows


def validate_snapshot(snapshot: Any) -> dict[str, Any]:
    errors: list[str] = []
    warnings: list[str] = []
    if not isinstance(snapshot, dict):
        return {"valid": False, "errors": ["snapshot must be an object"], "warnings": []}
    host_capacity = snapshot.get("host_capacity")
    if not isinstance(host_capacity, dict) or not host_capacity:
        errors.append("host_capacity must be a non-empty object keyed by physical host_id")
        host_capacity = {}
    for host_id, capacity in host_capacity.items():
        if not isinstance(host_id, str) or not host_id.strip():
            errors.append("host_capacity keys must be non-empty host ids")
            continue
        if not isinstance(capacity, dict):
            errors.append(f"host_capacity.{host_id} must be an object")
            continue
        for field in RESOURCE_FIELDS:
            if not _positive_int(capacity.get(field)):
                errors.append(f"host_capacity.{host_id}.{field} must be a positive integer")
    jobs = snapshot.get("jobs")
    if not isinstance(jobs, list) or not jobs:
        errors.append("jobs must be a non-empty array")
        jobs = []
    namespaces: set[str] = set()
    host_ids: set[str] = set()
    totals = {field: 0 for field in RESOURCE_FIELDS}
    host_totals: dict[str, dict[str, int]] = {}
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
        if job["host_id"] not in host_capacity:
            errors.append(f"{prefix}: host_id has no physical capacity record")
        valid_jobs.append(job)
        host_total = host_totals.setdefault(job["host_id"], {field: 0 for field in RESOURCE_FIELDS})
        for field in RESOURCE_FIELDS:
            amount = job["resources"][field]
            totals[field] += amount
            host_total[field] += amount
    for host_id, host_total in host_totals.items():
        capacity = host_capacity.get(host_id, {})
        for field, total in host_total.items():
            if _positive_int(capacity.get(field)) and total > capacity[field]:
                errors.append(
                    f"resource budget exceeded for host {host_id} {field}: "
                    f"{total} > {capacity[field]}"
                )

    path_owners: list[tuple[str, str, str, str, bool]] = []
    for job in valid_jobs:
        for path_name, path, writable in _path_rows(job):
            if not writable:
                continue
            for other_host, other_job, other_name, other_path, other_writable in path_owners:
                if other_host != job["host_id"]:
                    continue
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
            path_owners.append((job["host_id"], job["namespace"], path_name, path, writable))
    return {
        "valid": not errors,
        "errors": errors,
        "warnings": warnings,
        "job_count": len(valid_jobs),
        "resource_totals": totals,
    }


@contextmanager
def _locked_lease_dir(lease_dir: Path):
    """Serialize every admission and release through one host-owned directory."""
    if not lease_dir.is_absolute() or lease_dir.is_symlink():
        raise ValueError("lease directory must be an absolute, non-symlink host path")
    lease_dir.mkdir(parents=True, exist_ok=True, mode=0o700)
    directory_stat = lease_dir.stat()
    if directory_stat.st_uid != os.getuid() or stat.S_IMODE(directory_stat.st_mode) & 0o022:
        raise ValueError("lease directory must be owned by this user and not group/world-writable")
    lock_path = lease_dir / ".admission.lock"
    descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR | getattr(os, "O_NOFOLLOW", 0), 0o600)
    with os.fdopen(descriptor, "r+") as stream:
        lock_stat = os.fstat(stream.fileno())
        if (lock_stat.st_uid != os.getuid() or not stat.S_ISREG(lock_stat.st_mode)
                or stat.S_IMODE(lock_stat.st_mode) & 0o022):
            raise ValueError("admission lock must be an owned, non-writable-by-others regular file")
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


def _active_leases(lease_dir: Path) -> list[dict[str, Any]]:
    jobs = []
    for path in sorted(lease_dir.glob("*.json")):
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"unsafe active lease: {path}")
        payload = _load(path)
        if not isinstance(payload, dict) or not isinstance(payload.get("record"), dict):
            raise ValueError(f"invalid active lease: {path}")
        current = payload["record"]
        if current.get("namespace") != path.stem or payload.get("owner_digest") != _record_digest(current):
            raise ValueError(f"active lease owner identity is invalid: {path}")
        errors = validate_record(current)
        if errors:
            raise ValueError(f"invalid active lease {path}: {'; '.join(errors)}")
        jobs.append(current)
    return jobs


def _check_lease_dir_isolated(lease_dir: Path, records: list[dict[str, Any]]) -> None:
    """Keep the host lock outside every job-owned mutable root."""
    lease_path = canonical_path(str(lease_dir))
    for record in records:
        for name, path, writable in _path_rows(record):
            if writable and _overlap(lease_path, path):
                raise ValueError(
                    f"host lease directory overlaps {record['namespace']}:{name} writable state"
                )


def acquire_lease(
    record: dict[str, Any], lease_dir: Path, host_capacity: dict[str, Any]
) -> dict[str, Any]:
    """Atomically admit a job after checking every live host lease."""
    errors = validate_record(record)
    if errors:
        raise ValueError("cannot acquire invalid record: " + "; ".join(errors))
    if not isinstance(host_capacity, dict) or record["host_id"] not in host_capacity:
        raise ValueError("trusted physical host capacity is required")
    # Check the candidate before opening the lock: a job may place temp or
    # output roots outside its checkout, and cleanup of one must not unlink
    # the host-wide admission lock.
    _check_lease_dir_isolated(lease_dir, [record])
    with _locked_lease_dir(lease_dir):
        jobs = _active_leases(lease_dir)
        # The pre-lock check prevents creating a lock inside the candidate's
        # own writable root. Repeat it under the lock so a path retargeted
        # while waiting cannot be admitted.
        _check_lease_dir_isolated(lease_dir, [record, *jobs])
        if any(job["host_id"] != record["host_id"] for job in jobs):
            raise ValueError("one lease directory must describe one physical host")
        admission = validate_snapshot({"host_capacity": host_capacity, "jobs": [*jobs, record]})
        if not admission["valid"]:
            raise ValueError("admission denied: " + "; ".join(admission["errors"]))
        lease_path = _lease_path(record, lease_dir)
        owner_digest = _record_digest(record)
        payload = json.dumps(
            {"owner_digest": owner_digest, "record": record}, sort_keys=True, indent=2
        ) + "\n"
        try:
            descriptor = os.open(lease_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
        except FileExistsError as exc:
            raise ValueError(f"lease already exists; recovery must inspect it: {lease_path}") from exc
        try:
            with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
                stream.write(payload)
        except Exception:
            lease_path.unlink(missing_ok=True)
            raise
    return {
        "acquired": True,
        "lease": str(lease_path),
        "namespace": record["namespace"],
        "owner_digest": owner_digest,
    }


def release_lease(record: dict[str, Any], lease_dir: Path) -> dict[str, Any]:
    errors = validate_record(record)
    if errors:
        raise ValueError("cannot release invalid record: " + "; ".join(errors))
    with _locked_lease_dir(lease_dir):
        lease_path = _lease_path(record, lease_dir)
        if not lease_path.is_file() or lease_path.is_symlink():
            raise ValueError(f"lease is absent or unsafe: {lease_path}")
        current = _load(lease_path)
        owner_digest = _record_digest(record)
        if (
            not isinstance(current, dict)
            or current.get("owner_digest") != owner_digest
            or current.get("record") != record
        ):
            raise ValueError("lease owner identity does not match the requested record")
        lease_path.unlink()
    return {
        "released": True,
        "lease": str(lease_path),
        "namespace": record["namespace"],
        "owner_digest": owner_digest,
    }


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    report = sub.add_parser("report")
    report.add_argument("snapshot", type=Path)
    admit = sub.add_parser("admit")
    admit.add_argument("record", type=Path)
    admit.add_argument("--lease-dir", type=Path, required=True)
    admit.add_argument("--host-capacity", type=Path, required=True)
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
            result = acquire_lease(_load(args.record), args.lease_dir, _load(args.host_capacity))
        else:
            result = release_lease(_load(args.record), args.lease_dir)
    except (OSError, ValueError) as exc:
        print(json.dumps({"valid": False, "errors": [str(exc)]}, indent=2))
        return 1
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0 if result.get("valid", result.get("acquired", result.get("released", False))) else 1


if __name__ == "__main__":
    sys.exit(main())
