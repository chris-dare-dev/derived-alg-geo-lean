#!/usr/bin/env python3
"""Bootstrap a fresh worktree with private, pinned Lake caches.

A checked snapshot contains Git-object checkouts of every manifest package and
all eleven required build trees.  A fresh target receives the whole `.lake`
generation with one no-replace rename.  Existing `.lake` trees are never
changed; migration needs a separate quiescent protocol.
"""

from __future__ import annotations

import argparse
import contextlib
import ctypes
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
except ImportError:
    fcntl = None

from private_archive_io import DIR_FLAGS, extract_checked_archive, remove_owned_tree

MIN_FREE_BYTES = 2 * 1024**3
QUIET_SECONDS = 90
READY = "private-cache-ready.json"
STAGE_OWNER = ".private-stage-owner.json"
FORMAT = 4
RENAME_NOREPLACE = 1


def fail(message: str) -> None:
    raise ValueError(message)


def digest_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(4 * 1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def pins(root: Path) -> tuple[str, dict[str, str]]:
    toolchain = (root / "lean-toolchain").read_bytes()
    manifest = (root / "lake-manifest.json").read_bytes()
    parsed = json.loads(manifest)
    revisions = {p["name"]: p["rev"] for p in parsed["packages"]}
    if len(revisions) != len(parsed["packages"]) or "mathlib" not in revisions:
        fail("manifest has no pinned Mathlib package")
    h = hashlib.sha256(b"private-package-cache-v4\0")
    for part in (toolchain, manifest, sys.platform.encode(), platform.machine().encode()):
        h.update(len(part).to_bytes(8, "big"))
        h.update(part)
    return h.hexdigest(), revisions


def package_urls(root: Path, revisions: dict[str, str]) -> dict[str, str]:
    packages = json.loads((root / "lake-manifest.json").read_text())["packages"]
    urls = {p["name"]: p.get("url") for p in packages}
    if set(urls) != set(revisions) or any(not isinstance(url, str) or not url for url in urls.values()):
        fail("manifest package URLs are incomplete")
    return urls


def git(*args: str) -> str:
    environment = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    environment.update(GIT_CONFIG_NOSYSTEM="1", GIT_CONFIG_GLOBAL=os.devnull)
    result = subprocess.run(["git", *args], check=True, capture_output=True,
                            text=True, env=environment)
    return result.stdout.strip()


def validate_packages(root: Path, revisions: dict[str, str]) -> None:
    if root.is_symlink() or not root.is_dir():
        fail(f"package root absent or linked: {root}")
    names = {path.name for path in root.iterdir() if path.is_dir()}
    if names != set(revisions):
        fail(f"package directories differ from manifest: {names ^ set(revisions)}")
    for name, revision in revisions.items():
        package = root / name
        if package.is_symlink() or not package.is_dir():
            fail(f"package is linked or absent: {package}")
        git_dir = package / ".git"
        if git_dir.is_symlink() or not git_dir.is_dir():
            fail(f"{name} has external Git metadata")
        if (git_dir / "commondir").exists() or (git_dir / "objects/info/alternates").exists():
            fail(f"{name} has external Git common data or object alternates")
        if Path(git("-C", str(package), "rev-parse", "--absolute-git-dir")).resolve() != git_dir.resolve():
            fail(f"{name} Git directory resolves outside package")
        if Path(git("-C", str(package), "rev-parse", "--show-toplevel")).resolve() != package.resolve():
            fail(f"{name} worktree resolves outside package")
        if git("-C", str(package), "rev-parse", "HEAD") != revision:
            fail(f"{name} differs from manifest revision")


def tree_digest(root: Path) -> tuple[str, int]:
    """Hash names, types, permissions and bytes; refuse escaping links."""
    h = hashlib.sha256()
    size = 0
    root_info = root.lstat()
    if not stat.S_ISDIR(root_info.st_mode):
        fail(f"cache root is not a directory: {root}")
    h.update(b"ROOT" + (root_info.st_mode & 0o777).to_bytes(2, "big"))
    boundary = root.resolve()
    for parent, dirs, files in os.walk(root, topdown=True, followlinks=False):
        dirs.sort()
        files.sort()
        for name in dirs + files:
            path = Path(parent) / name
            rel = path.relative_to(root).as_posix().encode()
            info = path.lstat()
            if stat.S_ISLNK(info.st_mode):
                raw = os.readlink(path)
                if os.path.isabs(raw) or not path.resolve().is_relative_to(boundary):
                    fail(f"package/cache link escapes tree: {path}")
                kind, value = b"L", raw.encode()
            elif stat.S_ISDIR(info.st_mode):
                kind, value = b"D", b""
            elif stat.S_ISREG(info.st_mode):
                kind, value = b"F", bytes.fromhex(digest_file(path))
                size += info.st_size
            else:
                fail(f"special file in cache tree: {path}")
            h.update(len(rel).to_bytes(8, "big") + rel + kind)
            h.update(len(value).to_bytes(8, "big") + value)
            h.update((info.st_mode & 0o777).to_bytes(2, "big"))
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


def require_owner_writable(root: Path) -> None:
    """Lake must be able to replace artifacts and create output below every dir."""
    for parent, dirs, files in os.walk(root, followlinks=False):
        for path in (Path(parent), *(Path(parent) / name for name in dirs + files)):
            info = path.lstat()
            if not stat.S_ISLNK(info.st_mode) and not info.st_mode & stat.S_IWUSR:
                fail(f"private build cache entry is not owner-writable: {path}")


def disk_headroom(path: Path, required: int) -> None:
    free = shutil.disk_usage(path).free
    if free < required + MIN_FREE_BYTES:
        fail(f"insufficient disk at {path}: need {required + MIN_FREE_BYTES} bytes, have {free}")


def snapshot_dir(key: str) -> Path:
    base = os.environ.get("DAG_PRIVATE_PACKAGE_SNAPSHOT_DIR")
    if not base:
        base = str(Path.home() / ".cache/derived-alg-geo-lean/package-snapshots")
    # Keep the spelling until each component has been opened with NOFOLLOW.
    return Path(base).expanduser().absolute() / key


def open_created_directory(path: Path) -> int:
    """Create/open an absolute path component by component below pinned fds."""
    if not path.is_absolute() or ".." in path.parts:
        fail("snapshot store path must be absolute and normalized")
    fd = os.open("/", DIR_FLAGS)
    try:
        for part in path.parts[1:]:
            try:
                os.mkdir(part, 0o700, dir_fd=fd)
            except FileExistsError:
                pass
            child = os.open(part, DIR_FLAGS, dir_fd=fd)
            os.close(fd)
            fd = child
        return fd
    except BaseException:
        os.close(fd)
        raise


@contextlib.contextmanager
def locked_directory(directory: Path, lock_name: str, *, create: bool):
    if fcntl is None or not Path("/proc/self/fd").is_dir():
        fail("private seeding requires Linux flock and /proc/self/fd")
    root_fd = open_created_directory(directory) if create else os.open(directory, DIR_FLAGS)
    try:
        lock_fd = os.open(lock_name, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW,
                          0o600, dir_fd=root_fd)
        with os.fdopen(lock_fd, "a+b") as stream:
            if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                fail("cache lock is not regular")
            fcntl.flock(stream, fcntl.LOCK_EX)
            named = directory.lstat()
            opened = os.fstat(root_fd)
            if directory.is_symlink() or (named.st_dev, named.st_ino) != (opened.st_dev, opened.st_ino):
                fail("locked directory changed identity")
            yield root_fd, Path(f"/proc/self/fd/{root_fd}")
    finally:
        os.close(root_fd)


def no_replace_rename(src_fd: int, src: str, dst_fd: int, dst: str,
                      expected: tuple[int, int]) -> None:
    named = os.stat(src, dir_fd=src_fd, follow_symlinks=False)
    if (not stat.S_ISDIR(named.st_mode) or
            (named.st_dev, named.st_ino) != expected):
        fail("staged generation changed identity before publication")
    _rename_noreplace(src_fd, src, dst_fd, dst)
    published = os.stat(dst, dir_fd=dst_fd, follow_symlinks=False)
    if ((published.st_dev, published.st_ino) != expected or
            not stat.S_ISDIR(published.st_mode)):
        # A concurrent same-UID writer may have replaced the random stage
        # between the identity check and renameat2. Restore its old name if
        # possible; never leave that substitution at the public destination.
        try:
            _rename_noreplace(dst_fd, dst, src_fd, src)
        except OSError:
            pass
        fail("published generation differs from opened stage")


def _rename_noreplace(src_fd: int, src: str, dst_fd: int, dst: str) -> None:
    libc = ctypes.CDLL(None, use_errno=True)
    renameat2 = getattr(libc, "renameat2", None)
    if renameat2 is None:
        fail("Linux renameat2 is unavailable")
    renameat2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p,
                          ctypes.c_uint]
    renameat2.restype = ctypes.c_int
    if renameat2(src_fd, os.fsencode(src), dst_fd, os.fsencode(dst), RENAME_NOREPLACE) != 0:
        code = ctypes.get_errno()
        raise OSError(code, os.strerror(code), dst)


def checked_snapshot(directory: Path, key: str, revisions: dict[str, str],
                     urls: dict[str, str]) -> dict | None:
    current = directory / "current"
    if not current.exists() and not current.is_symlink():
        return None
    if current.is_symlink() or not current.is_dir():
        fail("snapshot generation is linked or incomplete")
    archive, metadata = current / "cache.tar", current / "snapshot.json"
    if (archive.is_symlink() or metadata.is_symlink() or not archive.is_file() or
            not metadata.is_file()):
        fail("snapshot files are linked or incomplete")
    if archive.stat().st_mode & 0o222 or metadata.stat().st_mode & 0o222:
        fail("snapshot files are writable")
    record = json.loads(metadata.read_text())
    if (record.get("format") != FORMAT or record.get("key") != key or
            record.get("revisions") != revisions or record.get("urls") != urls):
        fail("snapshot pins differ from target")
    expected_caches = set(revisions) | {"project"}
    digests = record.get("cache_digests")
    if (not isinstance(digests, dict) or set(digests) != expected_caches or
            not isinstance(record.get("source_bytes"), int) or
            record["source_bytes"] <= 0):
        fail("snapshot cache inventory is incomplete")
    for value in (record.get("archive_sha256"), record.get("packages_sha256"),
                  record.get("build_sha256"), *digests.values()):
        if (not isinstance(value, str) or len(value) != 64 or
                any(ch not in "0123456789abcdef" for ch in value)):
            fail("snapshot has an invalid content digest")
    if record.get("archive_sha256") != digest_file(archive):
        fail("snapshot archive checksum failed")
    return record


def _build_roots(source: Path, build_source: Path, revisions: dict[str, str]) -> dict[str, Path]:
    roots = {name: source / name / ".lake/build" for name in revisions}
    roots["project"] = build_source
    for name, path in roots.items():
        if path.is_symlink() or path.parent.is_symlink() or not path.is_dir() or not next(path.rglob("*.olean"), None):
            fail(f"required warm build cache missing or linked: {name}: {path}")
        require_owner_writable(path)
        if recently_written(path):
            fail(f"required warm build cache is active: {name}: {path}")
    return roots


def write_stage_owner(stage_fd: int, kind: str, token: str) -> None:
    fd = os.open(STAGE_OWNER, os.O_CREAT | os.O_EXCL | os.O_WRONLY | os.O_NOFOLLOW,
                 0o600, dir_fd=stage_fd)
    try:
        os.write(fd, json.dumps({"format": FORMAT, "kind": kind, "token": token},
                                sort_keys=True).encode() + b"\n")
        os.fsync(fd)
    finally:
        os.close(fd)


def sweep_owned_stages(parent_fd: int, parent: Path, kind: str, prefix: str) -> None:
    """Reap quiet abandoned generations under the same parent lock."""
    for entry in list(os.scandir(parent_fd)):
        if not (entry.name.startswith(prefix) or entry.name.startswith(".removing-")):
            continue
        try:
            stage_fd = os.open(entry.name, DIR_FLAGS, dir_fd=parent_fd)
        except OSError:
            continue
        try:
            info = os.fstat(stage_fd)
            marker_fd = os.open(STAGE_OWNER, os.O_RDONLY | os.O_NOFOLLOW,
                                dir_fd=stage_fd)
            try:
                marker = json.loads(os.read(marker_fd, 4096))
            finally:
                os.close(marker_fd)
            if (marker.get("format") != FORMAT or marker.get("kind") != kind or
                    not isinstance(marker.get("token"), str) or
                    (entry.name.startswith(prefix) and
                     entry.name != prefix + marker["token"])):
                continue
            if time.time() - info.st_mtime < QUIET_SECONDS:
                continue
            if recently_written(parent / entry.name):
                continue
            identity = (info.st_dev, info.st_ino)
        except (OSError, ValueError, json.JSONDecodeError):
            continue
        finally:
            os.close(stage_fd)
        remove_owned_tree(parent_fd, entry.name, identity)


def install_cloned_build(package: Path, source: Path) -> None:
    """Add a donor build to a pinned checkout without following tracked links."""
    package_fd = os.open(package, DIR_FLAGS)
    try:
        try:
            os.mkdir(".lake", 0o700, dir_fd=package_fd)
        except FileExistsError:
            pass
        # A Git revision may track .lake as a symlink even when the donor's
        # working tree replaced it with an ignored, ordinary build directory.
        lake_fd = os.open(".lake", DIR_FLAGS, dir_fd=package_fd)
        try:
            try:
                os.stat("build", dir_fd=lake_fd, follow_symlinks=False)
            except FileNotFoundError:
                pass
            else:
                fail(f"pinned package already contains .lake/build: {package}")
            # /proc/self/fd pins the opened .lake even if an ancestor is renamed.
            shutil.copytree(source, Path(f"/proc/self/fd/{lake_fd}/build"),
                            symlinks=True)
        finally:
            os.close(lake_fd)
    finally:
        os.close(package_fd)


def create_snapshot(directory_fd: int, directory: Path, source: Path,
                    build_source: Path, key: str, revisions: dict[str, str],
                    urls: dict[str, str]) -> dict:
    validate_packages(source, revisions)
    roots = _build_roots(source, build_source, revisions)
    before = {name: tree_digest(path) for name, path in roots.items()}
    source_bytes = sum(size for _, size in before.values())
    disk_headroom(directory, 3 * source_bytes)
    token = uuid.uuid4().hex
    stage_name = f".stage-{token}"
    os.mkdir(stage_name, 0o700, dir_fd=directory_fd)
    stage_fd = os.open(stage_name, DIR_FLAGS, dir_fd=directory_fd)
    stage_identity = (os.fstat(stage_fd).st_dev, os.fstat(stage_fd).st_ino)
    published = False
    try:
        write_stage_owner(stage_fd, "snapshot", token)
        # Git is a child process: its /proc/self would not own our descriptor.
        stage = Path(f"/proc/{os.getpid()}/fd/{stage_fd}")
        content = stage / "content"
        packages = content / "packages"
        packages.mkdir(parents=True)
        for name, revision in revisions.items():
            git("clone", "--no-local", "--no-checkout", "--", str(source / name),
                str(packages / name))
            git("-C", str(packages / name), "checkout", "--detach", "--force", revision)
            git("-C", str(packages / name), "remote", "set-url", "origin", urls[name])
            if git("-C", str(packages / name), "rev-parse", "HEAD") != revision:
                fail(f"clone did not check out pinned {name}")
            install_cloned_build(packages / name, roots[name])
        shutil.copytree(roots["project"], content / "build", symlinks=True)
        after = {name: tree_digest(path) for name, path in roots.items()}
        copied = {name: tree_digest((packages / name / ".lake/build") if name != "project"
                                    else content / "build") for name in roots}
        if before != after or before != copied or any(recently_written(p) for p in roots.values()):
            fail("donor build cache changed during snapshot construction")
        validate_packages(packages, revisions)
        package_digest, _ = tree_digest(packages)
        project_digest, _ = tree_digest(content / "build")
        archive = stage / "cache.tar"
        with tarfile.open(archive, "w") as tar:
            tar.add(packages, arcname="packages")
            tar.add(content / "build", arcname="build")
        record = {"format": FORMAT, "key": key, "revisions": revisions,
                  "urls": urls,
                  "cache_digests": {name: value[0] for name, value in before.items()},
                  "packages_sha256": package_digest, "build_sha256": project_digest,
                  "source_bytes": source_bytes, "archive_sha256": digest_file(archive)}
        metadata = stage / "snapshot.json"
        metadata.write_text(json.dumps(record, sort_keys=True) + "\n")
        archive.chmod(0o444)
        metadata.chmod(0o444)
        content_info = (content.stat().st_dev, content.stat().st_ino)
        remove_owned_tree(stage_fd, "content", content_info)
        no_replace_rename(directory_fd, stage_name, directory_fd, "current",
                          stage_identity)
        published = True
        return record
    finally:
        os.close(stage_fd)
        if not published:
            try:
                remove_owned_tree(directory_fd, stage_name, stage_identity)
            except (OSError, ValueError):
                pass  # Leave an uncertain stage for manual recovery, never chase it.


def _read_receipt(lake: Path) -> dict:
    if lake.is_symlink() or not lake.is_dir():
        fail("target .lake is absent or linked")
    receipt = lake / READY
    if receipt.is_symlink() or not receipt.is_file():
        fail("target has no private-cache receipt")
    return json.loads(receipt.read_text())


def verify_ready(target: Path) -> None:
    key, revisions = pins(target)
    urls = package_urls(target, revisions)
    lake = target / ".lake"
    record = _read_receipt(lake)
    if (record.get("format") != FORMAT or record.get("key") != key or
            record.get("revisions") != revisions or record.get("urls") != urls):
        fail("private-cache receipt pins differ from target")
    validate_packages(lake / "packages", revisions)
    for name, url in urls.items():
        if git("-C", str(lake / "packages" / name), "remote", "get-url", "origin") != url:
            fail(f"private package remote differs from manifest: {name}")
    caches = {name: lake / "packages" / name / ".lake/build" for name in revisions}
    caches["project"] = lake / "build"
    for name, path in caches.items():
        if not path.is_dir() or path.is_symlink():
            fail(f"private build cache missing or linked: {name}")
        require_owner_writable(path)
    packages_digest, _ = tree_digest(lake / "packages")
    project_digest, _ = tree_digest(lake / "build")
    if (packages_digest != record.get("packages_sha256") or
            project_digest != record.get("build_sha256")):
        fail("private-cache receipt content differs from target")
    for name, path in caches.items():
        if tree_digest(path)[0] != record.get("cache_digests", {}).get(name):
            fail(f"private build cache differs from receipt: {name}")


def default_donor(target: Path) -> Path:
    common = Path(git("-C", str(target), "rev-parse", "--path-format=absolute",
                      "--git-common-dir"))
    donor = common.parent
    if donor == target or not donor.is_dir():
        fail("no donor available to create pinned cache snapshot")
    return donor


def verify_target_inode(target: Path, target_fd: int) -> None:
    """Require the user-facing worktree path to still name the opened root."""
    named = target.lstat()
    opened = os.fstat(target_fd)
    if (stat.S_ISLNK(named.st_mode) or
            (named.st_dev, named.st_ino) != (opened.st_dev, opened.st_ino)):
        fail("target worktree changed identity during private seeding")


def seed(target: Path, donor: Path | None, *, verify: bool, dry_run: bool,
         force: bool) -> None:
    if force:
        fail("forced migration is not implemented; existing .lake is preserved")
    if target.is_symlink():
        fail("target worktree is linked")
    target = target.resolve(strict=True)
    if verify:
        verify_ready(target)
        print(f"private package and build caches verified in {target}")
        return
    lake_name = target / ".lake"
    if lake_name.exists() or lake_name.is_symlink():
        fail("target already has .lake; fresh-worktree bootstrap only")
    key, revisions = pins(target)
    urls = package_urls(target, revisions)
    directory = snapshot_dir(key)
    if directory.is_relative_to(target):
        fail("snapshot store must be outside the target")
    with locked_directory(target, ".private-cache-seed.lock", create=False) as (target_fd, _pinned_target):
        verify_target_inode(target, target_fd)
        if lake_name.exists() or lake_name.is_symlink():
            fail("target .lake appeared while waiting for the lock")
        sweep_owned_stages(target_fd, _pinned_target, "target", ".lake-stage-")
        with locked_directory(directory, ".lock", create=True) as (snapshot_fd, snapshot):
            sweep_owned_stages(snapshot_fd, snapshot, "snapshot", ".stage-")
            record = checked_snapshot(snapshot, key, revisions, urls)
            if record is None:
                donor = default_donor(target) if donor is None else donor.resolve(strict=True)
                donor_key, _ = pins(donor)
                if donor == target or donor_key != key:
                    fail("donor and target pins differ")
                source = (donor / ".lake/packages").resolve(strict=True)
                build_source = donor / ".lake/build"
                if dry_run:
                    validate_packages(source, revisions)
                    _build_roots(source, build_source, revisions)
                    print(f"would create Git-object snapshot from {donor}")
                    return
                print(f"creating Git-object snapshot from {donor}", flush=True)
                record = create_snapshot(snapshot_fd, snapshot, source, build_source,
                                         key, revisions, urls)
            else:
                print(f"verified package snapshot {directory}", flush=True)
            disk_headroom(target, record["source_bytes"])
            if dry_run:
                print(f"would privately seed fresh {target} from {directory}")
                return
            token = uuid.uuid4().hex
            stage_name = f".lake-stage-{token}"
            os.mkdir(stage_name, 0o700, dir_fd=target_fd)
            stage_fd = os.open(stage_name, DIR_FLAGS, dir_fd=target_fd)
            identity = (os.fstat(stage_fd).st_dev, os.fstat(stage_fd).st_ino)
            published = False
            try:
                write_stage_owner(stage_fd, "target", token)
                extract_checked_archive(snapshot / "current/cache.tar", stage_fd,
                                        record["archive_sha256"], set(revisions))
                stage = Path(f"/proc/{os.getpid()}/fd/{stage_fd}")
                validate_packages(stage / "packages", revisions)
                if tree_digest(stage / "packages")[0] != record["packages_sha256"]:
                    fail("extracted packages differ from snapshot")
                if tree_digest(stage / "build")[0] != record["build_sha256"]:
                    fail("extracted project build differs from snapshot")
                caches = {name: stage / "packages" / name / ".lake/build" for name in revisions}
                caches["project"] = stage / "build"
                for name, path in caches.items():
                    if tree_digest(path)[0] != record["cache_digests"][name]:
                        fail(f"extracted build cache differs from snapshot: {name}")
                receipt_fd = os.open(READY, os.O_CREAT | os.O_EXCL | os.O_WRONLY |
                                     os.O_NOFOLLOW, 0o600, dir_fd=stage_fd)
                try:
                    receipt = json.dumps(record, sort_keys=True).encode() + b"\n"
                    os.write(receipt_fd, receipt)
                    os.fsync(receipt_fd)
                finally:
                    os.close(receipt_fd)
                os.fsync(stage_fd)
                verify_target_inode(target, target_fd)
                no_replace_rename(target_fd, stage_name, target_fd, ".lake", identity)
                published = True
            finally:
                os.close(stage_fd)
                if not published:
                    try:
                        remove_owned_tree(target_fd, stage_name, identity)
                    except (OSError, ValueError):
                        pass  # An uncertain stage is never treated as ready.
    verify_ready(target)
    print(f"private package and build caches ready in {target}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", type=Path, required=True)
    parser.add_argument("--donor", type=Path)
    parser.add_argument("--force", action="store_true")
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()
    try:
        seed(args.target, args.donor, verify=args.verify, dry_run=args.dry_run,
             force=args.force)
    except (ValueError, OSError, subprocess.CalledProcessError, tarfile.TarError,
            KeyError) as error:
        print(f"private cache seed refused: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
