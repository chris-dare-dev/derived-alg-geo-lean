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
import errno
import fcntl
import hashlib
import json
import ntpath
import os
import posixpath
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


def _literal_path(value: Any) -> str:
    """Keep a path's spelling intact across classification and host checks."""
    if (not isinstance(value, str) or not value or value != value.strip() or
            "\x00" in value):
        raise ValueError("path must be a literal nonempty string without boundary whitespace")
    return value


def canonical_path(value: Any) -> str:
    """Resolve a local POSIX path or normalize a reported Windows path."""

    raw = _literal_path(value)
    # A double-leading-slash path is still a POSIX path on this Ubuntu host.
    # ntpath.splitdrive mistakes it for a UNC share, missing a real alias.
    if raw.startswith("/"):
        resolved = str(Path(raw).resolve(strict=False))
        return ntpath.normpath(resolved.replace("/", "\\").rstrip("\\") or "\\")
    windows_style = bool(ntpath.splitdrive(raw)[0]) or "\\" in raw
    if windows_style:
        if not ntpath.isabs(raw):
            raise ValueError("path must be absolute")
        if raw.startswith("\\\\?\\UNC\\"):
            raw = "\\\\" + raw[8:]
        elif raw.startswith("\\\\?\\"):
            raw = raw[4:]
        return ntpath.normcase(ntpath.normpath(raw)).rstrip("\\") or "\\"
    raise ValueError("path must be absolute")


def _overlap(left: str, right: str) -> bool:
    a = left.rstrip("\\")
    b = right.rstrip("\\")
    return a == b or a.startswith(b + "\\") or b.startswith(a + "\\")


def _path_identity(value: Any) -> str:
    if not isinstance(value, dict):
        raise ValueError("path entry must be an object")
    raw = _literal_path(value.get("path"))
    if raw.startswith("/"):
        canonical_path(raw)
        observed = value.get("resolved_path")
        if observed is not None:
            observed = _literal_path(observed)
            if not observed.startswith("/"):
                raise ValueError("resolved_path must be an absolute POSIX path")
            # Detached reports must compare the collector's observed identity,
            # not re-resolve it on the machine reading the report.
            observed = posixpath.normpath("/" + observed.lstrip("/"))
            return ntpath.normpath(observed.replace("/", "\\").rstrip("\\") or "\\")
        return canonical_path(raw)
    windows_style = bool(ntpath.splitdrive(raw)[0]) or "\\" in raw
    if windows_style:
        # Validate the observed path itself before trusting the collector's
        # OS-resolved identity. A drive-relative path must never be repaired by
        # a caller-supplied resolved_path.
        canonical_path(raw)
        resolved = value.get("resolved_path")
        if resolved is None:
            raise ValueError("resolved_path is required for Windows path identity")
        return canonical_path(resolved)
    return canonical_path(raw)


def _inode_identity(value: dict[str, Any], *, local: bool) -> tuple[int, int] | None:
    """Use observed identity, or stat an explicitly local POSIX path."""
    raw = _literal_path(value["path"])
    observed = None
    if "observed_device" in value or "observed_inode" in value:
        device = value.get("observed_device")
        inode = value.get("observed_inode")
        if (not isinstance(device, int) or isinstance(device, bool) or device < 0 or
                not _positive_int(inode)):
            raise ValueError("observed device/inode must be valid integers")
        observed = device, inode
    if raw.startswith("/") and (local or "resolved_path" not in value):
        try:
            info = os.stat(raw)
        except FileNotFoundError:
            if local and observed is not None:
                raise ValueError("observed inode no longer exists on admitting host")
        else:
            actual = (info.st_dev, info.st_ino)
            if local and observed is not None and actual != observed:
                raise ValueError("observed inode differs from admitting host")
            return actual
    return observed


def _record_digest(record: dict[str, Any]) -> str:
    encoded = json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
    return hashlib.sha256(encoded.encode("utf-8")).hexdigest()


def _lease_name(record: dict[str, Any]) -> str:
    namespace = record.get("namespace")
    if (
        not isinstance(namespace, str)
        or not NAMESPACE_RE.fullmatch(namespace)
        or namespace.upper() in RESERVED_NAMESPACES
    ):
        raise ValueError("namespace must contain only safe filename characters")
    return f"{namespace}.json"


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
    for name, value in paths.items():
        if not isinstance(name, str) or not name or name != name.strip():
            errors.append("paths keys must be nonempty literal names")
            continue
        if not isinstance(value, dict):
            errors.append(f"paths.{name} must be an object")
            continue
        try:
            _path_identity(value)
        except ValueError as exc:
            errors.append(f"paths.{name}.path: {exc}")
        # This record describes job-owned writable state. An additional root
        # such as controller_temp must be checked just like the eight required
        # roots; marking it read-only would skip collision detection.
        if value.get("writable") is not True:
            errors.append(f"paths.{name} must be job-owned writable state")
        has_device = "observed_device" in value
        has_inode = "observed_inode" in value
        if has_device != has_inode:
            errors.append(f"paths.{name} observed device/inode must appear together")
        elif has_device and (
            not isinstance(value["observed_device"], int)
            or isinstance(value["observed_device"], bool)
            or value["observed_device"] < 0
            or not _positive_int(value["observed_inode"])
        ):
            errors.append(f"paths.{name} observed device/inode must be nonnegative integers")
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


def _validate_local_path_identities(records: list[dict[str, Any]]) -> None:
    """An Ubuntu admission must verify POSIX observations on this host."""
    for record in records:
        for name, value in record["paths"].items():
            if not isinstance(value, dict):
                continue
            raw = _literal_path(value.get("path"))
            if raw.startswith("/"):
                observed = _path_identity(value)
                current = canonical_path(raw)
                if observed != current:
                    raise ValueError(
                        f"{record['namespace']}:{name} resolved_path differs from host identity"
                    )


def validate_snapshot(snapshot: Any, *, verify_local_inodes: bool = False) -> dict[str, Any]:
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
    namespaces: set[tuple[str, str]] = set()
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
        namespace_key = (job["host_id"], job["namespace"])
        if namespace_key in namespaces:
            errors.append(f"{prefix}: duplicate namespace {job['namespace']!r}")
        namespaces.add(namespace_key)
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
    inode_owners: dict[tuple[str, int, int], tuple[str, str]] = {}
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
            try:
                inode = _inode_identity(job["paths"][path_name], local=verify_local_inodes)
            except (OSError, ValueError) as exc:
                errors.append(f"{job['namespace']}:{path_name}: {exc}")
                continue
            if inode is None:
                continue
            key = job["host_id"], *inode
            earlier = inode_owners.get(key)
            if earlier is not None and earlier[0] != job["namespace"]:
                errors.append(
                    f"writable inode collision: {job['namespace']}:{path_name} "
                    f"shares device/inode with {earlier[0]}:{earlier[1]}"
                )
            else:
                inode_owners[key] = job["namespace"], path_name
    return {
        "valid": not errors,
        "errors": errors,
        "warnings": warnings,
        "job_count": len(valid_jobs),
        "resource_totals": totals,
    }


@contextmanager
def _locked_lease_dir(lease_dir: Path):
    """Bind the lock and every lease operation to one opened directory inode."""
    if not lease_dir.is_absolute() or ".." in lease_dir.parts:
        raise ValueError("lease directory must be an absolute host path without '..'")
    directory_fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for component in lease_dir.parts[1:]:
            try:
                child_fd = os.open(
                    component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                    dir_fd=directory_fd,
                )
            except FileNotFoundError:
                os.mkdir(component, mode=0o700, dir_fd=directory_fd)
                child_fd = os.open(
                    component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                    dir_fd=directory_fd,
                )
            except OSError as exc:
                if exc.errno in (errno.ELOOP, errno.ENOTDIR):
                    raise ValueError("lease directory has a symlink or non-directory component") from exc
                raise
            os.close(directory_fd)
            directory_fd = child_fd
        directory_stat = os.fstat(directory_fd)
        if (
            directory_stat.st_uid != os.getuid()
            or stat.S_IMODE(directory_stat.st_mode) & 0o022
        ):
            raise ValueError("lease directory must be owned by this user and not group/world-writable")
        descriptor = os.open(
            ".admission.lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW,
            0o600, dir_fd=directory_fd,
        )
        with os.fdopen(descriptor, "r+") as stream:
            lock_stat = os.fstat(stream.fileno())
            if (
                lock_stat.st_uid != os.getuid()
                or not stat.S_ISREG(lock_stat.st_mode)
                or stat.S_IMODE(lock_stat.st_mode) & 0o022
            ):
                raise ValueError("admission lock must be an owned, non-writable-by-others regular file")
            fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
            try:
                yield directory_fd
            finally:
                fcntl.flock(stream.fileno(), fcntl.LOCK_UN)
    finally:
        os.close(directory_fd)


def _lease_directory_path(directory_fd: int) -> Path:
    path = Path(os.readlink(f"/proc/self/fd/{directory_fd}"))
    if not path.is_absolute() or not path.is_dir():
        raise ValueError("opened lease directory is no longer reachable")
    opened = os.fstat(directory_fd)
    reached = path.stat()
    if (opened.st_dev, opened.st_ino) != (reached.st_dev, reached.st_ino):
        raise ValueError("opened lease directory changed identity")
    return path


def _assert_lease_path(directory_fd: int, requested: Path) -> None:
    try:
        opened = os.fstat(directory_fd)
        reached = requested.stat()
    except FileNotFoundError as exc:
        raise ValueError("lease directory moved while locked") from exc
    if (opened.st_dev, opened.st_ino) != (reached.st_dev, reached.st_ino):
        raise ValueError("lease directory moved while locked")


def _read_lease(directory_fd: int, name: str) -> Any:
    descriptor = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=directory_fd)
    with os.fdopen(descriptor, "r", encoding="utf-8") as stream:
        lease_stat = os.fstat(stream.fileno())
        if (
            not stat.S_ISREG(lease_stat.st_mode)
            or lease_stat.st_uid != os.getuid()
            or stat.S_IMODE(lease_stat.st_mode) & 0o022
        ):
            raise ValueError(f"unsafe active lease: {name}")
        try:
            return json.load(stream)
        except json.JSONDecodeError as exc:
            raise ValueError(f"invalid active lease: {name}: {exc}") from exc


def _active_leases(directory_fd: int) -> list[dict[str, Any]]:
    jobs = []
    for name in sorted(item for item in os.listdir(directory_fd) if item.endswith(".json")):
        payload = _read_lease(directory_fd, name)
        if not isinstance(payload, dict) or not isinstance(payload.get("record"), dict):
            raise ValueError(f"invalid active lease: {name}")
        current = payload["record"]
        if current.get("namespace") != Path(name).stem or payload.get("owner_digest") != _record_digest(current):
            raise ValueError(f"active lease owner identity is invalid: {name}")
        errors = validate_record(current)
        if errors:
            raise ValueError(f"invalid active lease {name}: {'; '.join(errors)}")
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
    _validate_local_path_identities([record])
    # Check the candidate before opening the lock: a job may place temp or
    # output roots outside its checkout, and cleanup of one must not unlink
    # the host-wide admission lock.
    _check_lease_dir_isolated(lease_dir, [record])
    with _locked_lease_dir(lease_dir) as directory_fd:
        _assert_lease_path(directory_fd, lease_dir)
        stable_dir = _lease_directory_path(directory_fd)
        jobs = _active_leases(directory_fd)
        _validate_local_path_identities([record, *jobs])
        # The pre-lock check prevents creating a lock inside the candidate's
        # own writable root. Repeat it under the lock so a path retargeted
        # while waiting cannot be admitted.
        _check_lease_dir_isolated(stable_dir, [record, *jobs])
        if any(job["host_id"] != record["host_id"] for job in jobs):
            raise ValueError("one lease directory must describe one physical host")
        admission = validate_snapshot(
            {"host_capacity": host_capacity, "jobs": [*jobs, record]},
            verify_local_inodes=True,
        )
        if not admission["valid"]:
            raise ValueError("admission denied: " + "; ".join(admission["errors"]))
        lease_name = _lease_name(record)
        lease_path = stable_dir / lease_name
        owner_digest = _record_digest(record)
        payload = json.dumps(
            {"owner_digest": owner_digest, "record": record}, sort_keys=True, indent=2
        ) + "\n"
        try:
            descriptor = os.open(
                lease_name, os.O_CREAT | os.O_EXCL | os.O_WRONLY | os.O_NOFOLLOW,
                0o600, dir_fd=directory_fd,
            )
        except FileExistsError as exc:
            raise ValueError(f"lease already exists; recovery must inspect it: {lease_path}") from exc
        try:
            with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
                stream.write(payload)
                stream.flush()
                os.fsync(stream.fileno())
        except Exception:
            os.unlink(lease_name, dir_fd=directory_fd)
            raise
        _assert_lease_path(directory_fd, lease_dir)
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
    with _locked_lease_dir(lease_dir) as directory_fd:
        _assert_lease_path(directory_fd, lease_dir)
        stable_dir = _lease_directory_path(directory_fd)
        lease_name = _lease_name(record)
        lease_path = stable_dir / lease_name
        try:
            current = _read_lease(directory_fd, lease_name)
        except FileNotFoundError as exc:
            raise ValueError(f"lease is absent or unsafe: {lease_path}") from exc
        owner_digest = _record_digest(record)
        if (
            not isinstance(current, dict)
            or current.get("owner_digest") != owner_digest
            or current.get("record") != record
        ):
            raise ValueError("lease owner identity does not match the requested record")
        os.unlink(lease_name, dir_fd=directory_fd)
        _assert_lease_path(directory_fd, lease_dir)
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
