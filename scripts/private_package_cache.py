#!/usr/bin/env python3
"""Seed a worktree from a checked, read-only package archive and a private build copy.

The archive is a download cache, never a Lake package root.  A seed verifies its
checksum, extracts to a private staging directory, and publishes a ready marker
only after both writable trees are private and complete.  Existing worktrees
are migrated one at a time with ``--force``; their old paths survive until the
new copies have passed every check.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import stat
import subprocess
import sys
import tarfile
import time
import uuid

try:
    import fcntl
except ImportError:  # The private mode deliberately fails closed off Ubuntu/Linux.
    fcntl = None


MIN_FREE_BYTES = 2 * 1024**3
QUIET_SECONDS = 90
READY = "private-cache-ready.json"


def fail(message: str) -> None:
    raise ValueError(message)


def digest_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(4 * 1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def pins(root: Path) -> tuple[str, dict[str, str]]:
    toolchain = (root / "lean-toolchain").read_bytes()
    manifest = (root / "lake-manifest.json").read_bytes()
    parsed = json.loads(manifest)
    revisions = {p["name"]: p["rev"] for p in parsed["packages"]}
    if len(revisions) != len(parsed["packages"]) or "mathlib" not in revisions:
        fail("manifest has no pinned Mathlib package")
    h = hashlib.sha256()
    for part in (toolchain, manifest):
        h.update(len(part).to_bytes(8, "big"))
        h.update(part)
    for part in (sys.platform.encode(), platform.machine().encode()):
        h.update(len(part).to_bytes(8, "big"))
        h.update(part)
    return h.hexdigest(), revisions


def validate_packages(root: Path, revisions: dict[str, str]) -> None:
    if root.is_symlink() or not root.is_dir():
        fail(f"package root is absent or linked: {root}")
    actual = {p.name for p in root.iterdir() if p.is_dir()}
    if actual != set(revisions):
        fail(f"package directories differ from manifest: {actual ^ set(revisions)}")
    for name, revision in revisions.items():
        package = root / name
        real_package = package.resolve()
        if package.is_symlink():
            fail(f"package is linked rather than privately owned: {package}")
        git_dir = package / ".git"
        if git_dir.is_symlink() or not git_dir.is_dir():
            fail(f"{name} has external Git metadata (linked worktree or symlink)")
        if (git_dir / "commondir").exists() or (git_dir / "objects/info/alternates").exists():
            fail(f"{name} has external Git common data or object alternates")
        actual_git_dir = subprocess.run(
            ["git", "-C", str(real_package), "rev-parse", "--absolute-git-dir"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
        if Path(actual_git_dir).resolve() != git_dir.resolve():
            fail(f"{name} resolves its Git index outside the package")
        toplevel = subprocess.run(
            ["git", "-C", str(real_package), "rev-parse", "--show-toplevel"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
        if Path(toplevel).resolve() != package.resolve():
            fail(f"{name} resolves its worktree outside the package")
        head = subprocess.run(
            ["git", "-C", str(real_package), "rev-parse", "HEAD"],
            capture_output=True, text=True, check=True,
        ).stdout.strip()
        if head != revision:
            fail(f"{name} is at {head}, manifest pins {revision}")
        dirty = subprocess.run(
            ["git", "--no-optional-locks", "-C", str(real_package),
             "status", "--porcelain", "--untracked-files=all"],
            capture_output=True, text=True, check=True,
        ).stdout
        if dirty:
            fail(f"{name} has uncommitted package source")
    if not next((root / "mathlib/.lake/build").rglob("*.olean"), None):
        fail("Mathlib cache has no .olean; seeding would start a cold build")


def tree_digest(root: Path) -> tuple[str, int]:
    """Hash content, names and kinds; reject links escaping this package tree."""
    h = hashlib.sha256()
    size = 0
    boundary = root.resolve()
    for parent, dirs, files in os.walk(root, topdown=True, followlinks=False):
        dirs.sort()
        files.sort()
        for name in dirs + files:
            path = Path(parent) / name
            rel = path.relative_to(root).as_posix().encode()
            info = path.lstat()
            if stat.S_ISLNK(info.st_mode):
                raw_link = os.readlink(path)
                if os.path.isabs(raw_link):
                    fail(f"absolute package symlink is not portable to a private copy: {path}")
                resolved = path.resolve()
                if not resolved.is_relative_to(boundary):
                    fail(f"package symlink escapes its tree: {path}")
                kind, value = b"L", raw_link.encode()
            elif stat.S_ISDIR(info.st_mode):
                kind, value = b"D", b""
            elif stat.S_ISREG(info.st_mode):
                kind, value = b"F", bytes.fromhex(digest_file(path))
                size += info.st_size
            else:
                fail(f"special file in package tree: {path}")
            h.update(len(rel).to_bytes(8, "big") + rel + kind)
            h.update(len(value).to_bytes(8, "big") + value)
            h.update((info.st_mode & 0o111).to_bytes(2, "big"))
            if kind == b"L" and name in dirs:
                dirs.remove(name)
    return h.hexdigest(), size


def recently_written(root: Path) -> bool:
    threshold = time.time() - QUIET_SECONDS
    for parent, _, files in os.walk(root, followlinks=False):
        for name in files:
            if (Path(parent) / name).lstat().st_mtime > threshold:
                return True
    return False


def snapshot_dir(key: str) -> Path:
    base = os.environ.get("DAG_PRIVATE_PACKAGE_SNAPSHOT_DIR")
    if not base:
        base = str(Path.home() / ".cache/derived-alg-geo-lean/package-snapshots")
    return Path(base).expanduser().resolve() / key


def disk_headroom(path: Path, required: int) -> None:
    free = shutil.disk_usage(path).free
    if free < required + MIN_FREE_BYTES:
        fail(f"insufficient disk at {path}: need {required + MIN_FREE_BYTES} bytes, have {free}")


@contextlib.contextmanager
def snapshot_lock(directory: Path):
    if fcntl is None:
        fail("private package seeding requires Linux file locking")
    directory.mkdir(parents=True, exist_ok=True)
    if directory.is_symlink():
        fail("package snapshot directory is linked")
    root_fd = os.open(directory, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        lock_fd = os.open(".lock", os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW,
                          0o600, dir_fd=root_fd)
        with os.fdopen(lock_fd, "a+b") as stream:
            if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                fail("package snapshot lock is not a regular file")
            fcntl.flock(stream, fcntl.LOCK_EX)
            actual = directory.lstat()
            opened = os.fstat(root_fd)
            if (directory.is_symlink() or
                    (actual.st_dev, actual.st_ino) != (opened.st_dev, opened.st_ino)):
                fail("package snapshot directory changed while waiting for its lock")
            yield Path(f"/proc/self/fd/{root_fd}")
    finally:
        os.close(root_fd)


def checked_snapshot(directory: Path, key: str, revisions: dict[str, str]) -> dict | None:
    current = directory / "current"
    if not current.exists() and not current.is_symlink():
        return None
    if current.is_symlink() or not current.is_dir():
        fail("package snapshot generation is linked or is not a directory")
    archive = current / "packages.tar"
    metadata = current / "snapshot.json"
    if not archive.is_file() or archive.is_symlink() or not metadata.is_file() or metadata.is_symlink():
        fail("incomplete or linked package snapshot; refusing to repair it implicitly")
    if archive.stat().st_mode & 0o222 or metadata.stat().st_mode & 0o222:
        fail("package snapshot is writable")
    record = json.loads(metadata.read_text())
    if record.get("format") != 1 or record.get("key") != key or record.get("revisions") != revisions:
        fail("package snapshot pins differ from target")
    if record.get("archive_sha256") != digest_file(archive):
        fail("package snapshot archive checksum failed")
    return record


def create_snapshot(directory: Path, source: Path, key: str,
                    revisions: dict[str, str]) -> dict:
    validate_packages(source, revisions)
    if recently_written(source):
        fail(f"package source changed in the last {QUIET_SECONDS} seconds: {source}")
    before, source_bytes = tree_digest(source)
    disk_headroom(directory, 2 * source_bytes)
    token = uuid.uuid4().hex
    stage = directory / f".stage-{token}"
    archive_stage = stage / "packages.tar"
    metadata_stage = stage / "snapshot.json"
    try:
        shutil.copytree(source, stage / "packages", symlinks=True)
        after, _ = tree_digest(source)
        copied, _ = tree_digest(stage / "packages")
        if before != after or before != copied or recently_written(source):
            fail("package source changed during snapshot copy")
        validate_packages(stage / "packages", revisions)
        with tarfile.open(archive_stage, "w") as tar:
            tar.add(stage / "packages", arcname="packages")
        record = {
            "format": 1, "key": key, "revisions": revisions,
            "tree_sha256": before, "source_bytes": source_bytes,
            "archive_sha256": digest_file(archive_stage),
        }
        metadata_stage.write_text(json.dumps(record, sort_keys=True) + "\n")
        archive_stage.chmod(0o444)
        metadata_stage.chmod(0o444)
        shutil.rmtree(stage / "packages")
        os.replace(stage, directory / "current")
        return record
    finally:
        shutil.rmtree(stage, ignore_errors=True)


def remove_abandoned_snapshots(directory: Path) -> None:
    """A killed creator leaves only a hidden staging generation under the lock."""
    for path in directory.glob(".stage-*"):
        remove_path(path)


def safe_extract(archive: Path, destination: Path) -> None:
    with tarfile.open(archive, "r") as tar:
        for member in tar:
            if not (member.isdir() or member.isfile() or member.issym()):
                fail(f"unexpected member in package snapshot: {member.name}")
            path = Path(member.name)
            if not path.parts or path.is_absolute() or ".." in path.parts or path.parts[0] != "packages":
                fail(f"unsafe package snapshot member: {member.name}")
        tar.extractall(destination, filter="data")


def remove_path(path: Path) -> None:
    if path.is_symlink() or path.is_file():
        path.unlink()
    elif path.exists():
        shutil.rmtree(path)


def path_identity(path: Path) -> tuple | None:
    """Capture the directory entry, including a link's target, without following it."""
    try:
        info = path.lstat()
    except FileNotFoundError:
        return None
    link = os.readlink(path) if stat.S_ISLNK(info.st_mode) else None
    return info.st_dev, info.st_ino, info.st_mode, link


@contextlib.contextmanager
def pinned_lake(path: Path):
    """Keep every stage, rollback and cleanup below the opened target inode."""
    if not Path("/proc/self/fd").is_dir():
        fail("private package seeding requires Linux /proc/self/fd")
    fd = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    info = os.fstat(fd)
    pinned = Path(f"/proc/self/fd/{fd}")

    def verify() -> None:
        current = path.stat()
        if (path.is_symlink() or path.resolve() != path or
                (current.st_dev, current.st_ino) != (info.st_dev, info.st_ino)):
            fail("target .lake changed identity or resolves outside the worktree")

    try:
        verify()
        yield pinned, verify
    finally:
        os.close(fd)


def seed(target: Path, donor: Path, force: bool, dry_run: bool) -> None:
    for name in ("GIT_DIR", "GIT_COMMON_DIR", "GIT_INDEX_FILE", "GIT_OBJECT_DIRECTORY",
                 "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_WORK_TREE"):
        if name in os.environ:
            fail(f"Git environment override {name} would hide package ownership")
    target = target.resolve()
    donor = donor.resolve()
    if target == donor:
        fail("donor and target are the same worktree")
    key, revisions = pins(target)
    donor_key, _ = pins(donor)
    if key != donor_key:
        fail("donor and target have different lean-toolchain or lake-manifest.json")
    source_hint = donor / ".lake/packages"
    build_source = donor / ".lake/build"
    if build_source.is_symlink() or not build_source.is_dir() or not next(build_source.rglob("*.olean"), None):
        fail("donor has no built project modules")
    lake_name = target / ".lake"
    if lake_name.is_symlink() or (lake_name.exists() and not lake_name.is_dir()):
        fail("target .lake is linked or is not a directory")
    lake_name.mkdir(exist_ok=True)
    with pinned_lake(lake_name) as (lake, verify_lake):
        return _seed_at_lake(target, source_hint, build_source, key, revisions,
                             force, dry_run, lake, verify_lake)


def _seed_at_lake(target: Path, source_hint: Path, build_source: Path, key: str,
                  revisions: dict[str, str], force: bool, dry_run: bool,
                  lake: Path, verify_lake) -> None:
    packages = lake / "packages"
    build = lake / "build"
    if not force and (packages.exists() or packages.is_symlink() or build.exists()):
        fail("target already has a cache; use --force for a quiescent migration")
    if recently_written(build_source) or (build.exists() and recently_written(build)):
        fail("donor or target build changed in the last 90 seconds")
    if force and (packages.exists() or packages.is_symlink()) and recently_written(packages):
        fail("target package tree changed in the last 90 seconds; migration is not quiescent")
    initial_state = tuple(path_identity(path) for path in (packages, build, lake / READY))
    directory = snapshot_dir(key)
    if directory.is_relative_to(source_hint.resolve()) or directory.is_relative_to(target):
        fail("snapshot store must be outside the package source and target")
    snapshot_name = directory
    with snapshot_lock(directory) as locked_directory:
        directory = locked_directory
        verify_lake()
        if tuple(path_identity(path) for path in (packages, build, lake / READY)) != initial_state:
            fail("target cache changed while waiting for the snapshot lock")
        if not force and (packages.exists() or packages.is_symlink() or build.exists() or
                          (lake / READY).exists()):
            fail("target already has a cache after acquiring the snapshot lock")
        if (build.exists() and recently_written(build)) or (force and
                (packages.exists() or packages.is_symlink()) and recently_written(packages)):
            fail("target cache changed during admission")
        if not dry_run:
            remove_abandoned_snapshots(directory)
        record = checked_snapshot(directory, key, revisions)
        if record is None:
            source = source_hint.resolve(strict=True)
            validate_packages(source, revisions)
            if dry_run:
                print(f"would create checked package snapshot from {source}")
                _, source_bytes = tree_digest(source)
                record = {"source_bytes": source_bytes}
            else:
                print(f"creating checked package snapshot from {source}", flush=True)
                record = create_snapshot(directory, source, key, revisions)
        else:
            print(f"verified package snapshot {snapshot_name}", flush=True)
        build_before, build_bytes = tree_digest(build_source)
        disk_headroom(lake, record["source_bytes"] + build_bytes)
        if dry_run:
            print(f"would privately seed {target} from snapshot {snapshot_name} and build {build_source}")
            return
        token = uuid.uuid4().hex
        pkg_stage = lake / f".packages-seeding-{token}"
        build_stage = lake / f".build-seeding-{token}"
        pkg_old = lake / f".packages-previous-{token}"
        build_old = lake / f".build-previous-{token}"
        marker = lake / READY
        marker_stage = lake / f".{READY}-{token}"
        published_pkg = False
        published_build = False
        marker.unlink(missing_ok=True)
        try:
            safe_extract(directory / "current/packages.tar", pkg_stage)
            extracted = pkg_stage / "packages"
            got, _ = tree_digest(extracted)
            if got != record["tree_sha256"]:
                fail("extracted package tree differs from checked snapshot")
            validate_packages(extracted, revisions)
            shutil.copytree(build_source, build_stage, symlinks=True)
            build_after, _ = tree_digest(build_source)
            build_copied, _ = tree_digest(build_stage)
            if build_before != build_after or build_before != build_copied or recently_written(build_source):
                fail("donor build changed during cache copy")
            verify_lake()
            if force and (packages.exists() or packages.is_symlink()) and recently_written(packages):
                fail("target package tree changed during migration")
            if build.exists() and recently_written(build):
                fail("target build changed during migration")
            if packages.exists() or packages.is_symlink():
                packages.rename(pkg_old)
            if build.exists() or build.is_symlink():
                build.rename(build_old)
            extracted.rename(packages)
            published_pkg = True
            pkg_stage.rmdir()
            build_stage.rename(build)
            published_build = True
            marker_stage.write_text(json.dumps({
                "format": 1, "key": key,
                "snapshot_sha256": record["archive_sha256"],
            }, sort_keys=True) + "\n")
            os.replace(marker_stage, marker)
            verify_lake()
        except BaseException:
            marker.unlink(missing_ok=True)
            if pkg_old.exists() or pkg_old.is_symlink():
                remove_path(packages)
                pkg_old.rename(packages)
            elif published_pkg:
                remove_path(packages)
            if build_old.exists() or build_old.is_symlink():
                remove_path(build)
                build_old.rename(build)
            elif published_build:
                remove_path(build)
            raise
        finally:
            remove_path(pkg_stage)
            remove_path(build_stage)
            marker_stage.unlink(missing_ok=True)
        for old in (pkg_old, build_old):
            try:
                remove_path(old)
            except OSError as error:
                print(f"warning: private seed is ready but old cache cleanup needs attention: {error}",
                      file=sys.stderr)
        print(f"private package and build caches ready in {target}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", type=Path, required=True)
    parser.add_argument("--donor", type=Path, required=True)
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    try:
        seed(args.target, args.donor, args.force, args.dry_run)
    except (ValueError, OSError, subprocess.CalledProcessError, tarfile.TarError) as error:
        print(f"private cache seed refused: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
