#!/usr/bin/env python3
"""Ubuntu agent pickup with host admission and exact-owner cleanup.

This is installed host tooling, not code to run from an untrusted checkout.
The lease survives a controller crash or an uncleared systemd scope.  Recovery
is explicit; a fresh pickup never guesses that a stale lease is disposable.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import posixpath
import re
import secrets
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
from typing import Any

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scripts import runner_state


GIB = 1024 ** 3
PROFILES = {
    "probe": {"cpu_threads": 1, "memory_bytes": 2 * GIB, "disk_bytes": 2 * GIB},
    "build": {"cpu_threads": 3, "memory_bytes": 12 * GIB, "disk_bytes": 24 * GIB},
}
LEGACY_UNITS = ("main", "general-1", "general-2", "general-3")
LEGACY_DISK_RESERVATION = 16 * GIB  # measured roots are currently below this
HOST_CPU_HEADROOM = 1
HOST_MEMORY_HEADROOM = 8 * GIB
HOST_DISK_HEADROOM = 8 * GIB
REPOSITORY = "chris-dare-dev/derived-alg-geo-lean"


def _host_id() -> str:
    machine_id = Path("/etc/machine-id").read_text(encoding="ascii").strip()
    if not re.fullmatch(r"[0-9a-f]{32}", machine_id):
        raise ValueError("invalid /etc/machine-id")
    return machine_id


def _systemctl_show(unit: str, *properties: str) -> dict[str, str]:
    result = subprocess.run(
        ["systemctl", "--user", "show", unit, *(f"-p{prop}" for prop in properties)],
        check=True, capture_output=True, text=True,
    )
    return dict(line.split("=", 1) for line in result.stdout.splitlines() if "=" in line)


def _legacy_reservations() -> dict[str, int]:
    total = {name: 0 for name in runner_state.RESOURCE_FIELDS}
    for name in LEGACY_UNITS:
        data = _systemctl_show(
            f"dag-runner@{name}.service", "ActiveState", "UnitFileState",
            "CPUQuotaPerSecUSec", "MemoryMax"
        )
        if data.get("ActiveState") == "inactive" and data.get("UnitFileState") == "disabled":
            continue
        if data.get("ActiveState") not in ("active", "inactive"):
            raise ValueError(f"legacy runner {name} has unknown state; capacity denied")
        quota = data.get("CPUQuotaPerSecUSec", "")
        memory = data.get("MemoryMax", "")
        if not quota.endswith("s") or not quota[:-1].isdigit() or not memory.isdigit():
            raise ValueError(f"unmeasured active legacy runner: {name}")
        # systemd reports CPUQuotaPerSecUSec in seconds per second.
        total["cpu_threads"] += int(quota[:-1])
        total["memory_bytes"] += int(memory)
        total["disk_bytes"] += LEGACY_DISK_RESERVATION
    return total


def _capacity(base: Path) -> dict[str, dict[str, int]]:
    """Measure one physical host, reserving active old services first."""
    legacy = _legacy_reservations()
    cpu = len(os.sched_getaffinity(0)) - HOST_CPU_HEADROOM - legacy["cpu_threads"]
    available_memory = _mem_available() - HOST_MEMORY_HEADROOM - legacy["memory_bytes"]
    available_disk = shutil.disk_usage(base).free - HOST_DISK_HEADROOM - legacy["disk_bytes"]
    if min(cpu, available_memory, available_disk) <= 0:
        raise ValueError("host has no measured capacity after legacy reservations and headroom")
    return {_host_id(): {
        "cpu_threads": cpu, "memory_bytes": available_memory, "disk_bytes": available_disk,
    }}


def _mem_available() -> int:
    for line in Path("/proc/meminfo").read_text(encoding="ascii").splitlines():
        if line.startswith("MemAvailable:"):
            fields = line.split()
            if len(fields) == 3 and fields[2] == "kB":
                return int(fields[1]) * 1024
    raise ValueError("cannot measure MemAvailable")


def _record(namespace: str, root: Path, profile: str, kind: str = "agent") -> dict[str, Any]:
    if kind == "agent":
        workspace = root / "workspace"
        paths = {
            "checkout": workspace,
            "git_index": workspace / ".git/index",
            "lake_build": workspace / ".lake/build",
            "lake_packages": workspace / ".lake/packages",
        }
    elif kind == "runner":
        # Actions chooses a nested checkout path at job dispatch. Reserve its
        # whole _work envelope before runner startup; inventory actual leaves
        # after a job, rather than inventing an exact pre-job path.
        paths = {
            "checkout": root / "runner",
            "git_index": root / "runner/_work",
            "lake_build": root / "runner/_work",
            "lake_packages": root / "runner/_work",
            "temp": root / "runner/_work/_temp",
            "outputs": root / "runner/_work/_temp/_runner_file_commands",
            "artifacts": root / "runner/_work",
            "controller_temp": root / "tmp",
        }
    else:
        raise ValueError("unknown pickup kind")
    paths["elan"] = root / "home/.elan"
    if kind == "agent":
        paths.update({
            "temp": root / "tmp", "outputs": root / "outputs",
            "artifacts": root / "artifacts",
        })
    return {
        "host_id": _host_id(),
        "runner_id": "agent-pickup" if kind == "agent" else f"dag-{namespace}",
        "kind": kind, "job_id": namespace,
        "run_id": max(1, int(namespace[:12], 16)), "run_attempt": 1, "namespace": namespace,
        "resources": PROFILES[profile].copy(),
        "paths": {key: {
            "path": str(value), "resolved_path": str(value.resolve(strict=False)), "writable": True,
        } for key, value in paths.items()},
    }


def _open_base(base: Path) -> tuple[int, int]:
    """Open existing host base and jobs without following any path component."""
    with runner_state._locked_lease_dir(base) as base_fd:
        jobs_fd = os.open("jobs", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                          dir_fd=base_fd)
        if os.fstat(jobs_fd).st_uid != os.getuid() or stat.S_IMODE(os.fstat(jobs_fd).st_mode) != 0o700:
            os.close(jobs_fd)
            raise ValueError("jobs directory must be owned and mode 0700")
        return os.dup(base_fd), jobs_fd


def _prepare(base: Path, namespace: str) -> tuple[Path, tuple[int, int]]:
    base_fd, jobs_fd = _open_base(base)
    try:
        os.mkdir(namespace, 0o700, dir_fd=jobs_fd)
        root_fd = os.open(namespace, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                          dir_fd=jobs_fd)
        try:
            inode = os.fstat(root_fd)
            marker = {"namespace": namespace, "dev": inode.st_dev, "ino": inode.st_ino}
            marker_fd = os.open(".owner.json", os.O_CREAT | os.O_EXCL | os.O_WRONLY | os.O_NOFOLLOW,
                                0o600, dir_fd=root_fd)
            with os.fdopen(marker_fd, "w", encoding="utf-8") as stream:
                json.dump(marker, stream, sort_keys=True)
                stream.flush()
                os.fsync(stream.fileno())
            for child in ("home", "cache", "tmp", "outputs", "artifacts"):
                os.mkdir(child, 0o700, dir_fd=root_fd)
            home_fd = os.open("home", os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                              dir_fd=root_fd)
            try:
                os.mkdir(".elan", 0o700, dir_fd=home_fd)
            finally:
                os.close(home_fd)
            os.fsync(root_fd)
            return base / "jobs" / namespace, (inode.st_dev, inode.st_ino)
        finally:
            os.close(root_fd)
    finally:
        os.close(jobs_fd)
        os.close(base_fd)


def _root_identity_name(namespace: str) -> str:
    runner_state._lease_name({"namespace": namespace})
    return f"{namespace}.root"


def _store_root_identity(base: Path, record: dict[str, Any],
                         expected: tuple[int, int]) -> None:
    """Bind the job root inode outside the job's writable tree."""
    lease_dir = base / "leases"
    name = _root_identity_name(record["namespace"])
    with runner_state._locked_lease_dir(lease_dir) as directory_fd:
        runner_state._assert_lease_path(directory_fd, lease_dir)
        lease = runner_state._read_lease(
            directory_fd, runner_state._lease_name(record)
        )
        if (not isinstance(lease, dict) or lease.get("record") != record or
                lease.get("owner_digest") != runner_state._record_digest(record)):
            raise ValueError("lease changed before root identity was stored")
        payload = {"owner_digest": lease["owner_digest"],
                   "device": expected[0], "inode": expected[1]}
        descriptor = os.open(name, os.O_CREAT | os.O_EXCL | os.O_WRONLY | os.O_NOFOLLOW,
                             0o600, dir_fd=directory_fd)
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            json.dump(payload, stream, sort_keys=True)
            stream.flush()
            os.fsync(stream.fileno())


def _read_root_identity(base: Path, record: dict[str, Any]) -> tuple[int, int]:
    lease_dir = base / "leases"
    with runner_state._locked_lease_dir(lease_dir) as directory_fd:
        runner_state._assert_lease_path(directory_fd, lease_dir)
        payload = runner_state._read_lease(
            directory_fd, _root_identity_name(record["namespace"])
        )
    if (not isinstance(payload, dict) or
            payload.get("owner_digest") != runner_state._record_digest(record) or
            not isinstance(payload.get("device"), int) or
            not isinstance(payload.get("inode"), int)):
        raise ValueError("stored root identity is invalid")
    return payload["device"], payload["inode"]


def _remove_root_identity(base: Path, record: dict[str, Any]) -> None:
    lease_dir = base / "leases"
    with runner_state._locked_lease_dir(lease_dir) as directory_fd:
        runner_state._assert_lease_path(directory_fd, lease_dir)
        payload = runner_state._read_lease(
            directory_fd, _root_identity_name(record["namespace"])
        )
        if (not isinstance(payload, dict) or
                payload.get("owner_digest") != runner_state._record_digest(record)):
            raise ValueError("stored root identity owner changed")
        os.unlink(_root_identity_name(record["namespace"]), dir_fd=directory_fd)


def _rmtree_fd(fd: int) -> None:
    """Remove entries relative to a verified directory, never following links."""
    with os.scandir(fd) as entries:
        for entry in entries:
            info = entry.stat(follow_symlinks=False)
            if stat.S_ISDIR(info.st_mode):
                child_fd = os.open(entry.name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                                   dir_fd=fd)
                try:
                    if (os.fstat(child_fd).st_dev, os.fstat(child_fd).st_ino) != (info.st_dev, info.st_ino):
                        raise ValueError("cleanup target changed identity")
                    _rmtree_fd(child_fd)
                finally:
                    os.close(child_fd)
                os.rmdir(entry.name, dir_fd=fd)
            elif stat.S_ISREG(info.st_mode) or stat.S_ISLNK(info.st_mode):
                os.unlink(entry.name, dir_fd=fd)
            else:
                raise ValueError(f"unexpected file type during cleanup: {entry.name}")


def _mount_points() -> list[Path]:
    """Read mount points, including bind mounts on the same device."""
    points = []
    for line in Path("/proc/self/mountinfo").read_text(encoding="utf-8").splitlines():
        field = line.split(" ", 5)[4]
        decoded = re.sub(r"\\([0-7]{3})", lambda match: chr(int(match[1], 8)), field)
        points.append(Path(decoded))
    return points


def _cleanup(base: Path, namespace: str, expected: tuple[int, int]) -> None:
    base_fd, jobs_fd = _open_base(base)
    try:
        root_fd = os.open(namespace, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                          dir_fd=jobs_fd)
        try:
            info = os.fstat(root_fd)
            if (info.st_dev, info.st_ino) != expected:
                raise ValueError("job root changed identity; lease retained")
            marker = runner_state._read_lease(root_fd, ".owner.json")
            if marker != {"namespace": namespace, "dev": info.st_dev, "ino": info.st_ino}:
                raise ValueError("job root owner marker does not match; lease retained")
            root_path = Path(os.readlink(f"/proc/self/fd/{root_fd}"))
            if not root_path.is_absolute() or not root_path.is_dir():
                raise ValueError("job root no longer has a reachable path; lease retained")
            if any(point == root_path or root_path in point.parents for point in _mount_points()):
                raise ValueError("mount inside job root; lease retained")
            named = os.stat(namespace, dir_fd=jobs_fd, follow_symlinks=False)
            if (named.st_dev, named.st_ino) != expected:
                raise ValueError("job root name changed identity; lease retained")
            _rmtree_fd(root_fd)
        finally:
            os.close(root_fd)
        named = os.stat(namespace, dir_fd=jobs_fd, follow_symlinks=False)
        if (named.st_dev, named.st_ino) != expected:
            raise ValueError("job root name changed during cleanup; lease retained")
        os.rmdir(namespace, dir_fd=jobs_fd)
    finally:
        os.close(jobs_fd)
        os.close(base_fd)


def _scope_cleared(unit: str) -> bool:
    data = _systemctl_show(unit, "LoadState", "ActiveState", "ControlGroup")
    stopped = data.get("ActiveState") in ("inactive", "failed") \
        or data.get("LoadState") == "not-found"
    return stopped and not data.get("ControlGroup")


def _run_scope(unit: str, root: Path, profile: str, command: list[str]) -> int:
    resource = PROFILES[profile]
    isolated_env = {
        "PATH": "/home/chris-dare/.elan/bin:/usr/local/bin:/usr/bin:/bin",
        "HOME": str(root / "home"),
        "ELAN_HOME": str(root / "home/.elan"),
        "LAKE_HOME": str(root / "home/.lake"),
        "XDG_CACHE_HOME": str(root / "cache"),
        "XDG_CONFIG_HOME": str(root / "home/.config"),
        "XDG_DATA_HOME": str(root / "home/.local/share"),
        "XDG_STATE_HOME": str(root / "home/.local/state"),
        "TMPDIR": str(root / "tmp"),
        "LEAN_NUM_THREADS": str(resource["cpu_threads"]),
        "GIT_CONFIG_GLOBAL": "/dev/null",
    }
    args = [
        "systemd-run", "--user", "--scope", "--collect", "--quiet",
        "--slice=dag-runners.slice", f"--unit={unit}",
        f"--property=CPUQuota={resource['cpu_threads'] * 100}%",
        f"--property=MemoryMax={resource['memory_bytes']}",
        "--property=KillMode=control-group",
        f"--working-directory={root}",
        "/usr/bin/env", "-i", *(f"{key}={value}" for key, value in isolated_env.items()),
        *command,
    ]
    return subprocess.run(args, check=False).returncode


def _worker(repo: Path, revision: str, root: Path, expected: tuple[int, int],
            command: list[str]) -> int:
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("agent pickup requires a full immutable commit SHA")
    _verify_worker_root(root, expected)
    workspace = root / "workspace"
    subprocess.run(["git", "clone", "--no-local", "--no-checkout", str(repo), str(workspace)],
                   check=True)
    subprocess.run(["git", "checkout", "--detach", revision], cwd=workspace, check=True)
    for child in (workspace / ".lake", workspace / ".lake/build", workspace / ".lake/packages"):
        if child.is_symlink():
            raise ValueError(f"shared mutable package/build symlink in checkout: {child}")
        child.mkdir(mode=0o700, exist_ok=True)
    env = os.environ.copy()
    env["DAG_PICKUP_ROOT"] = str(root)
    return subprocess.run(command, cwd=workspace, env=env, check=False).returncode


def _verify_worker_root(root: Path, expected: tuple[int, int]) -> None:
    root_stat = root.lstat()
    if not stat.S_ISDIR(root_stat.st_mode) or (root_stat.st_dev, root_stat.st_ino) != expected:
        raise ValueError("worker root changed identity")
    with (root / ".owner.json").open(encoding="utf-8") as stream:
        owner = json.load(stream)
    if owner != {"namespace": root.name, "dev": expected[0], "ino": expected[1]}:
        raise ValueError("worker root owner marker does not match")


def _registration_token() -> str:
    result = subprocess.run(
        ["gh", "api", "-X", "POST", f"repos/{REPOSITORY}/actions/runners/registration-token"],
        capture_output=True, text=True, check=True,
    )
    token = json.loads(result.stdout).get("token")
    if not isinstance(token, str) or not token:
        raise ValueError("GitHub did not return a runner registration token")
    return token


def _runner_registered(name: str) -> bool:
    result = subprocess.run(
        ["gh", "api", f"repos/{REPOSITORY}/actions/runners?per_page=100"],
        capture_output=True, text=True, check=True,
    )
    # A missing name is not proof of deregistration if the list is truncated.
    payload = json.loads(result.stdout)
    if payload.get("total_count", 0) > len(payload.get("runners", [])):
        raise ValueError("runner list is truncated; cannot verify deregistration")
    return any(runner.get("name") == name for runner in payload["runners"])


def _verify_runner_archive(archive: Path, digest: str) -> None:
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise ValueError("runner archive requires a SHA-256 digest")
    if archive.is_symlink() or not archive.is_file():
        raise ValueError("runner archive must be a regular file")
    with archive.open("rb") as stream:
        measured = hashlib.file_digest(stream, "sha256").hexdigest()
    if measured != digest:
        raise ValueError("runner archive digest does not match")
    with tarfile.open(archive, mode="r:gz") as bundle:
        members: dict[str, tarfile.TarInfo] = {}
        for member in bundle.getmembers():
            parts = Path(member.name).parts
            if (member.name.startswith("/") or ".." in parts or
                    not (member.isfile() or member.isdir() or member.issym())):
                raise ValueError("runner archive contains an unsafe member")
            name = posixpath.normpath(member.name)
            if (name in members or
                    name == "." and not member.isdir()):
                raise ValueError("runner archive contains an unsafe member")
            members[name] = member
        for name, member in members.items():
            if not member.issym():
                continue
            link = member.linkname
            target = posixpath.normpath(posixpath.join(posixpath.dirname(name), link))
            if (not link or link.startswith("/") or
                    target == ".." or target.startswith("../") or
                    target not in members or not members[target].isfile()):
                raise ValueError("runner archive contains an unsafe symlink")
        for name in members:
            parent = posixpath.dirname(name)
            while parent not in ("", "."):
                if parent in members and members[parent].issym():
                    raise ValueError("runner archive contains a member below a symlink")
                parent = posixpath.dirname(parent)


def _runner_worker_started(archive: Path, digest: str, label: str, root: Path,
                           expected: tuple[int, int]) -> int:
    _verify_worker_root(root, expected)
    local_archive = root / "runner-archive.tar.gz"
    shutil.copyfile(archive, local_archive)
    _verify_runner_archive(local_archive, digest)
    runner_dir = root / "runner"
    runner_dir.mkdir(mode=0o700)
    with tarfile.open(local_archive, mode="r:gz") as bundle:
        bundle.extractall(runner_dir, filter="data")
    (runner_dir / "_work/_temp").mkdir(parents=True, mode=0o700, exist_ok=False)
    token_path = root / "registration-token"
    token = token_path.read_text(encoding="ascii").strip()
    if not token:
        raise ValueError("registration token is missing")
    name = f"dag-{root.name}"
    try:
        configured = subprocess.run([
            "./config.sh", "--unattended", "--ephemeral", "--disableupdate",
            "--url", f"https://github.com/{REPOSITORY}",
            "--name", name, "--labels", label, "--work", "_work",
        ], cwd=runner_dir, env={**os.environ, "ACTIONS_RUNNER_INPUT_TOKEN": token}, check=False)
    finally:
        _unlink_registration_token(root, expected)
    if configured.returncode != 0:
        raise ValueError(f"runner configuration failed with exit code {configured.returncode}")
    return subprocess.run(["./run.sh"], cwd=runner_dir, check=False).returncode


def _runner_worker(archive: Path, digest: str, label: str, root: Path,
                   expected: tuple[int, int]) -> int:
    _verify_worker_root(root, expected)
    root_fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    if (os.fstat(root_fd).st_dev, os.fstat(root_fd).st_ino) != expected:
        os.close(root_fd)
        raise ValueError("worker root changed before token cleanup")
    try:
        return _runner_worker_started(archive, digest, label, root, expected)
    finally:
        try:
            try:
                os.unlink("registration-token", dir_fd=root_fd)
            except FileNotFoundError:
                pass
        finally:
            os.close(root_fd)


def _unlink_registration_token(root: Path, expected: tuple[int, int]) -> None:
    root_fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        info = os.fstat(root_fd)
        if (info.st_dev, info.st_ino) != expected:
            raise ValueError("token cleanup root changed identity")
        try:
            os.unlink("registration-token", dir_fd=root_fd)
        except FileNotFoundError:
            pass
    finally:
        os.close(root_fd)


def _archive_runner_logs(base: Path, root: Path, namespace: str,
                         record: dict[str, Any], *, require_checkout: bool = True) -> None:
    logs = base / "logs"
    if (not logs.is_dir() or logs.is_symlink() or
            logs.stat().st_uid != os.getuid() or stat.S_IMODE(logs.stat().st_mode) != 0o700):
        raise ValueError("host logs directory is absent or unsafe; lease retained")
    destination = logs / namespace
    try:
        archived_info = destination.lstat()
    except FileNotFoundError:
        pass
    else:
        if (not stat.S_ISDIR(archived_info.st_mode) or archived_info.st_uid != os.getuid() or
                stat.S_IMODE(archived_info.st_mode) != 0o700):
            raise ValueError("runner log archive directory is unsafe")
        descriptor = os.open(destination, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            archived = runner_state._read_lease(descriptor, "pickup.json")
        except (FileNotFoundError, ValueError) as exc:
            raise ValueError("incomplete runner log archive; lease retained") from exc
        finally:
            os.close(descriptor)
        if (archived.get("namespace") != namespace or archived.get("inventory_valid") is not True or
                require_checkout and archived.get("checkout_observed") is not True):
            raise ValueError("runner log archive identity or inventory is invalid")
        return
    source = root / "runner/_diag"
    resolved_source = source.resolve(strict=False)
    if (source.is_symlink() or
            (resolved_source != root and root not in resolved_source.parents)):
        raise ValueError("runner diagnostic directory escapes job root; lease retained")
    checkout = root / "runner/_work/derived-alg-geo-lean/derived-alg-geo-lean"
    actual_paths = {
        "checkout": checkout,
        "git_index": checkout / ".git/index",
        "lake_build": checkout / ".lake/build",
        "lake_packages": checkout / ".lake/packages",
        "elan": root / "home/.elan",
        "controller_temp": root / "tmp",
        "actions_temp": root / "runner/_work/_temp",
        "outputs": root / "runner/_work/_temp/_runner_file_commands",
        "artifacts": checkout / "attest",
    }
    inventory = {}
    escaped = []
    for key, path in actual_paths.items():
        observed = path.resolve(strict=False)
        entry: dict[str, Any] = {"path": str(path), "resolved_path": str(observed)}
        try:
            info = path.lstat()
        except FileNotFoundError:
            entry["exists"] = False
        else:
            entry.update({"exists": True, "device": info.st_dev, "inode": info.st_ino,
                          "symlink": stat.S_ISLNK(info.st_mode)})
        if observed != root and root not in observed.parents:
            escaped.append(key)
        inventory[key] = entry
    checkout_observed = bool(inventory["checkout"]["exists"])
    inventory_valid = not escaped
    metadata = json.dumps({
        "namespace": namespace, "runner_name": f"dag-{namespace}",
        "repository": REPOSITORY, "writable_path_inventory": inventory,
        "inventory_valid": inventory_valid,
        "checkout_observed": checkout_observed,
        "reservation": record["resources"],
        "host_capacity_at_admission": record.get("host_capacity_at_admission"),
    }, sort_keys=True, indent=2) + "\n"
    stage = Path(tempfile.mkdtemp(prefix=f".{namespace}.", dir=logs))
    try:
        if source.is_dir():
            shutil.copytree(source, stage / "diag", symlinks=True)
        descriptor = os.open(stage, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            metadata_fd = os.open("pickup.json", os.O_CREAT | os.O_EXCL | os.O_WRONLY | os.O_NOFOLLOW,
                                  0o600, dir_fd=descriptor)
            with os.fdopen(metadata_fd, "w", encoding="utf-8") as stream:
                stream.write(metadata)
                stream.flush()
                os.fsync(stream.fileno())
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        stage.rename(destination)
    except BaseException:
        if stage.exists():
            shutil.rmtree(stage)
        raise
    if escaped:
        raise ValueError(f"runner writable paths escaped job root: {', '.join(escaped)}")
    if require_checkout and not checkout_observed:
        raise ValueError("runner checkout was not observed; lease retained")


def runner_once(base: Path, archive: Path, digest: str, label: str) -> None:
    if not base.is_absolute() or not archive.is_absolute():
        raise ValueError("absolute host base and runner archive paths are required")
    if label not in ("owner-linux", "owner-linux-main"):
        raise ValueError("unrecognized runner scheduling label")
    _verify_runner_archive(archive, digest)
    if not all((base / name).is_dir() for name in ("jobs", "leases", "logs")):
        raise ValueError("host base requires jobs/, leases/ and logs/")
    namespace = secrets.token_hex(12)
    root = base / "jobs" / namespace
    record = _record(namespace, root, "build", kind="runner")
    capacity = _capacity(base)
    record["host_capacity_at_admission"] = capacity[_host_id()]
    runner_state.acquire_lease(record, base / "leases", capacity)
    root, identity = _prepare(base, namespace)
    _store_root_identity(base, record, identity)
    token = _registration_token()
    token_path = root / "registration-token"
    descriptor = os.open(token_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY | os.O_NOFOLLOW, 0o600)
    with os.fdopen(descriptor, "w", encoding="ascii") as stream:
        stream.write(token + "\n")
        stream.flush()
        os.fsync(stream.fileno())
    unit = f"dag-pickup-{namespace}.scope"
    try:
        result = _run_scope(unit, root, "build", [
            sys.executable, str(Path(__file__).resolve()), "_runner_worker", str(archive), digest,
            label, str(root), str(identity[0]), str(identity[1]),
        ])
    finally:
        if _scope_cleared(unit):
            _unlink_registration_token(root, identity)
    if not _scope_cleared(unit) or result != 0:
        raise ValueError("runner exited unsuccessfully or scope is active; lease and root retained")
    if _runner_registered(f"dag-{namespace}"):
        raise ValueError("ephemeral runner remains registered; lease and root retained")
    _archive_runner_logs(base, root, namespace, record)
    _cleanup(base, namespace, identity)
    _remove_root_identity(base, record)
    runner_state.release_lease(record, base / "leases")


def pickup(base: Path, repo: Path, revision: str, profile: str, command: list[str]) -> int:
    if not base.is_absolute() or not repo.is_absolute() or not command:
        raise ValueError("absolute base, absolute repository and command are required")
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("revision must be a full commit SHA")
    if not (base / "jobs").is_dir() or not (base / "leases").is_dir():
        raise ValueError("host base must have pre-created jobs/ and leases/ directories")
    namespace = secrets.token_hex(12)
    root = base / "jobs" / namespace
    record = _record(namespace, root, profile)
    capacity = _capacity(base)
    record["host_capacity_at_admission"] = capacity[_host_id()]
    runner_state.acquire_lease(record, base / "leases", capacity)
    # The lease precedes even the first writable workspace operation. If
    # preparation fails or the controller crashes, recovery sees the lease.
    root, identity = _prepare(base, namespace)
    _store_root_identity(base, record, identity)
    unit = f"dag-pickup-{namespace}.scope"
    result = _run_scope(unit, root, profile, [
        sys.executable, str(Path(__file__).resolve()), "_worker", str(repo), revision,
        str(root), str(identity[0]), str(identity[1]), *command,
    ])
    if not _scope_cleared(unit):
        raise ValueError(f"scope {unit} is still active; lease and root retained")
    if result != 0:
        raise ValueError(f"pickup command failed ({result}); lease and root retained for recovery")
    _cleanup(base, namespace, identity)
    _remove_root_identity(base, record)
    runner_state.release_lease(record, base / "leases")
    return result


def recover(base: Path, namespace: str) -> None:
    """Release an interrupted pickup only after verifying its stopped scope."""
    if not base.is_absolute():
        raise ValueError("host base must be absolute")
    name = runner_state._lease_name({"namespace": namespace})
    with runner_state._locked_lease_dir(base / "leases") as lease_fd:
        payload = runner_state._read_lease(lease_fd, name)
    if not isinstance(payload, dict) or not isinstance(payload.get("record"), dict):
        raise ValueError("invalid pickup lease")
    record = payload["record"]
    if (runner_state.validate_record(record) or
            payload.get("owner_digest") != runner_state._record_digest(record) or
            record["host_id"] != _host_id() or
            record.get("kind") not in ("agent", "runner") or
            record["runner_id"] != ("agent-pickup" if record["kind"] == "agent"
                                    else f"dag-{namespace}") or
            record["namespace"] != namespace):
        raise ValueError("lease is not a valid local pickup")
    root = base / "jobs" / namespace
    expected_checkout = root / ("workspace" if record["kind"] == "agent" else "runner")
    if Path(record["paths"]["checkout"]["path"]) != expected_checkout:
        raise ValueError("lease checkout does not match the host job root")
    unit = f"dag-pickup-{namespace}.scope"
    if not _scope_cleared(unit):
        raise ValueError(f"scope {unit} is still active; recovery denied")
    if record["kind"] == "runner" and _runner_registered(f"dag-{namespace}"):
        raise ValueError("runner is still registered; recovery denied")
    try:
        info = root.lstat()
    except FileNotFoundError:
        # Only admission before root creation can safely lack an identity.
        try:
            _read_root_identity(base, record)
        except FileNotFoundError:
            pass
        else:
            raise ValueError("recorded root is missing; lease retained for manual recovery")
    else:
        if not stat.S_ISDIR(info.st_mode):
            raise ValueError("recovery root is not an owned directory")
        identity = _read_root_identity(base, record)
        if (info.st_dev, info.st_ino) != identity:
            raise ValueError("recovery root differs from recorded inode; lease retained")
        if record["kind"] == "runner":
            _archive_runner_logs(base, root, namespace, record, require_checkout=False)
        _cleanup(base, namespace, identity)
        _remove_root_identity(base, record)
    runner_state.release_lease(record, base / "leases")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    run = sub.add_parser("agent")
    run.add_argument("--base", required=True, type=Path)
    run.add_argument("--repo", required=True, type=Path)
    run.add_argument("--revision", required=True)
    run.add_argument("--profile", choices=PROFILES, default="probe")
    run.add_argument("command", nargs=argparse.REMAINDER)
    runner = sub.add_parser("runner-once")
    runner.add_argument("--base", required=True, type=Path)
    runner.add_argument("--archive", required=True, type=Path)
    runner.add_argument("--sha256", required=True)
    runner.add_argument("--label", required=True, choices=("owner-linux", "owner-linux-main"))
    release = sub.add_parser("recover")
    release.add_argument("--base", required=True, type=Path)
    release.add_argument("namespace")
    worker = sub.add_parser("_worker", help=argparse.SUPPRESS)
    worker.add_argument("repo", type=Path)
    worker.add_argument("revision")
    worker.add_argument("root", type=Path)
    worker.add_argument("device", type=int)
    worker.add_argument("inode", type=int)
    worker.add_argument("command", nargs=argparse.REMAINDER)
    runner_worker = sub.add_parser("_runner_worker", help=argparse.SUPPRESS)
    runner_worker.add_argument("archive", type=Path)
    runner_worker.add_argument("digest")
    runner_worker.add_argument("label")
    runner_worker.add_argument("root", type=Path)
    runner_worker.add_argument("device", type=int)
    runner_worker.add_argument("inode", type=int)
    args = parser.parse_args(argv)
    try:
        if args.action == "_worker":
            return _worker(args.repo, args.revision, args.root,
                           (args.device, args.inode), args.command)
        if args.action == "_runner_worker":
            return _runner_worker(args.archive, args.digest, args.label, args.root,
                                  (args.device, args.inode))
        if args.action == "recover":
            recover(args.base, args.namespace)
            return 0
        if args.action == "runner-once":
            runner_once(args.base, args.archive, args.sha256, args.label)
            return 0
        command = args.command[1:] if args.command[:1] == ["--"] else args.command
        return pickup(args.base, args.repo, args.revision, args.profile, command)
    except (OSError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"host pickup failed: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
