"""Authenticate pinned Git source independently of the index and worktree status.

Provision ``reader_git_dir`` once with ``git init --bare --object-format=sha1``
outside the packages. Verification never creates or changes that reader. The
caller must separately check ownership of mutable .git/.lake descendants and
coordinate a quiescent pickup; this is a source-byte contract, not a snapshot.
"""

from __future__ import annotations

import ctypes
import hashlib
import os
from pathlib import Path
import re
import shutil
import stat
import struct
import subprocess


_HEX = re.compile(rb"[0-9a-f]{40}\Z")
_NAME = re.compile(r"[A-Za-z0-9][A-Za-z0-9_.-]*\Z")
_DIR = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC
_FILE = os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC
_MAX_OBJECT = 256 * 1024 * 1024
_MAX_ENTRIES = 2_000_000
_MODES = {b"100644", b"100755", b"120000", b"40000", b"160000"}


def _refuse(message: str) -> None:
    raise ValueError(f"private source contract: {message}")


def _read_file(fd: int, name: bytes, limit: int) -> bytes:
    handle = os.open(name, _FILE, dir_fd=fd)
    try:
        info = os.fstat(handle)
        if not stat.S_ISREG(info.st_mode) or info.st_size > limit or info.st_nlink != 1:
            _refuse(f"unsafe regular file {os.fsdecode(name)}")
        data = bytearray()
        while len(data) <= limit:
            block = os.read(handle, min(1024 * 1024, limit + 1 - len(data)))
            if not block:
                break
            data.extend(block)
        if len(data) > limit or os.fstat(handle).st_size != info.st_size:
            _refuse(f"changing or oversized file {os.fsdecode(name)}")
        return bytes(data)
    finally:
        os.close(handle)


def _open_dir(fd: int, name: bytes) -> int:
    return os.open(name, _DIR, dir_fd=fd)


def _statx_mount_id(fd: int) -> int:
    statx = getattr(ctypes.CDLL(None, use_errno=True), "statx", None)
    if statx is None:
        _refuse("Linux statx mount IDs are unavailable")
    result = ctypes.create_string_buffer(256)
    statx.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int,
                      ctypes.c_uint, ctypes.c_void_p]
    statx.restype = ctypes.c_int
    if statx(fd, b"", 0x1000, 0x1000, result) != 0:  # AT_EMPTY_PATH, STATX_MNT_ID
        _refuse("Linux statx mount IDs are unavailable")
    mask = struct.unpack_from("I", result, 0)[0]
    if not mask & 0x1000:
        _refuse("Linux statx omitted mount ID")
    return struct.unpack_from("Q", result, 144)[0]


def _check_reader(reader_git_dir: Path) -> None:
    if reader_git_dir.is_symlink():
        _refuse("reader repository is linked")
    fd = os.open(reader_git_dir, _DIR)
    try:
        config = _read_file(fd, b"config", 16 * 1024).decode("ascii")
        section = None
        keys: dict[str, str] = {}
        for raw in config.splitlines():
            line = raw.strip()
            if not line or line.startswith(("#", ";")):
                continue
            if line.lower() == "[core]":
                section = "core"
            elif section == "core" and "=" in line:
                key, value = [piece.strip().lower() for piece in line.split("=", 1)]
                if key not in {"repositoryformatversion", "filemode", "bare", "logallrefupdates"} or key in keys:
                    _refuse("reader has nonminimal configuration")
                keys[key] = value
            else:
                _refuse("reader has nonminimal configuration")
        if keys.get("repositoryformatversion") != "0" or keys.get("bare") != "true":
            _refuse("reader is not a bare SHA-1 repository")
        if keys.get("filemode") not in {"true", "false"}:
            _refuse("reader configuration is incomplete")
        for name in (b"objects", b"refs"):
            child = _open_dir(fd, name)
            os.close(child)
    finally:
        os.close(fd)


def _check_object_store(git_fd: int) -> None:
    for marker in (b"commondir",):
        if marker in {os.fsencode(x) for x in os.listdir(git_fd)}:
            _refuse("external Git common directory")
    refs_fd = _open_dir(git_fd, b"refs")
    try:
        if b"replace" in {os.fsencode(x) for x in os.listdir(refs_fd)}:
            _refuse("replacement refs")
    finally:
        os.close(refs_fd)
    if b"packed-refs" in {os.fsencode(x) for x in os.listdir(git_fd)}:
        if b"refs/replace/" in _read_file(git_fd, b"packed-refs", 16 * 1024 * 1024):
            _refuse("packed replacement refs")
    config = _read_file(git_fd, b"config", 64 * 1024).lower()
    if any(token in config for token in (b"promisor", b"partialclone", b"[include", b"objectformat")):
        _refuse("package Git config uses unsupported features")
    objects_fd = _open_dir(git_fd, b"objects")
    try:
        stack = [os.dup(objects_fd)]
        seen = 0
        while stack:
            fd = stack.pop()
            try:
                for item in os.listdir(fd):
                    name = os.fsencode(item)
                    seen += 1
                    if seen > _MAX_ENTRIES:
                        _refuse("object store has too many entries")
                    info = os.stat(name, dir_fd=fd, follow_symlinks=False)
                    if stat.S_ISDIR(info.st_mode):
                        stack.append(_open_dir(fd, name))
                    elif not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                        _refuse("linked or special Git object")
                    if name in (b"alternates", b"http-alternates") or name.endswith(b".promisor"):
                        _refuse("alternates or promisor object store")
            finally:
                os.close(fd)
    finally:
        os.close(objects_fd)


class _Objects:
    def __init__(self, reader: Path, objects: Path):
        env = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
        env.update(GIT_DIR=str(reader), GIT_OBJECT_DIRECTORY=str(objects),
                   GIT_ALTERNATE_OBJECT_DIRECTORIES="", GIT_NO_REPLACE_OBJECTS="1",
                   GIT_NO_LAZY_FETCH="1", GIT_CONFIG_NOSYSTEM="1",
                   GIT_CONFIG_GLOBAL=os.devnull, GIT_OPTIONAL_LOCKS="0",
                   GIT_TERMINAL_PROMPT="0")
        self.proc = subprocess.Popen([shutil.which("git") or "git", "cat-file", "--batch"],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     stderr=subprocess.DEVNULL, env=env)

    def close(self) -> None:
        if self.proc.stdin:
            self.proc.stdin.close()
        if self.proc.stdout:
            self.proc.stdout.close()
        self.proc.wait(timeout=10)

    def get(self, oid: bytes, kind: bytes) -> bytes:
        if not _HEX.fullmatch(oid):
            _refuse("invalid SHA-1 object ID")
        assert self.proc.stdin and self.proc.stdout
        self.proc.stdin.write(oid + b"\n")
        self.proc.stdin.flush()
        header = self.proc.stdout.readline(128)
        parts = header.rstrip(b"\n").split(b" ")
        if len(parts) != 3 or parts[0] != oid or parts[1] != kind or not parts[2].isdigit():
            _refuse("Git returned a missing or mistyped object")
        size = int(parts[2])
        if size > _MAX_OBJECT:
            _refuse("oversized Git object")
        payload = self.proc.stdout.read(size)
        if len(payload) != size or self.proc.stdout.read(1) != b"\n":
            _refuse("truncated Git batch object")
        actual = hashlib.sha1(kind + b" " + str(size).encode() + b"\0" + payload).hexdigest().encode()
        if actual != oid:
            _refuse("Git object payload fails typed SHA-1 authentication")
        return payload


def _commit_tree(data: bytes) -> bytes:
    first = data.split(b"\n", 1)[0]
    if not first.startswith(b"tree ") or not _HEX.fullmatch(first[5:]):
        _refuse("malformed pinned commit tree")
    return first[5:]


def _tree(data: bytes) -> dict[bytes, tuple[bytes, bytes]]:
    entries = {}
    cursor = 0
    while cursor < len(data):
        space = data.find(b" ", cursor)
        nul = data.find(b"\0", space + 1)
        if space < 0 or nul < 0 or nul + 21 > len(data):
            _refuse("malformed Git tree entry")
        mode, name = data[cursor:space], data[space + 1:nul]
        oid = data[nul + 1:nul + 21].hex().encode()
        if mode not in _MODES or not name or name in (b".", b"..") or b"/" in name or name in entries:
            _refuse("unsupported or duplicate Git tree entry")
        entries[name] = mode, oid
        cursor = nul + 21
    return entries


def _tracked(objects: _Objects, tree_oid: bytes, package: str) -> dict[tuple[bytes, ...], tuple[bytes, bytes]]:
    result = {}
    stack = [((), tree_oid)]
    while stack:
        prefix, oid = stack.pop()
        for name, entry in _tree(objects.get(oid, b"tree")).items():
            path = (*prefix, name)
            mode, child_oid = entry
            if len(result) >= _MAX_ENTRIES or len(path) > 128:
                _refuse("pinned tree exceeds bounds")
            if mode == b"160000" and not (package == "aesop" and path == (b"lean_packages", b"std")):
                _refuse("unsupported Git gitlink")
            result[path] = entry
            if mode == b"40000":
                stack.append((path, child_oid))
    return result


def _resolve_link(path: tuple[bytes, ...], raw: bytes,
                  tracked: dict[tuple[bytes, ...], tuple[bytes, bytes]],
                  objects: _Objects) -> None:
    if raw.startswith(b"/") or b"\0" in raw:
        _refuse("absolute or malformed tracked symlink")
    pending = list(raw.split(b"/"))
    current = list(path[:-1])
    visited = set()
    for _ in range(128):
        if not pending:
            if not current or tuple(current) not in tracked:
                _refuse("tracked symlink points outside tracked source")
            return
        part = pending.pop(0)
        if part in (b"", b"."):
            continue
        if part == b"..":
            if not current:
                _refuse("tracked symlink escapes package")
            current.pop()
            continue
        if part in (b".git", b".lake"):
            _refuse("tracked symlink enters mutable runtime area")
        current.append(part)
        at = tuple(current)
        entry = tracked.get(at)
        if entry is None or entry[0] == b"160000":
            _refuse("tracked symlink points outside tracked source")
        if entry[0] == b"120000":
            if at in visited:
                _refuse("tracked symlink cycle")
            visited.add(at)
            link = objects.get(entry[1], b"blob")
            current.pop()
            pending = list(link.split(b"/")) + pending
        elif pending and entry[0] != b"40000":
            _refuse("tracked symlink crosses nondirectory")
    _refuse("tracked symlink depth exceeds bound")


def _check_worktree(package_fd: int, tracked: dict[tuple[bytes, ...], tuple[bytes, bytes]],
                    objects: _Objects) -> None:
    children: dict[tuple[bytes, ...], set[bytes]] = {}
    for path in tracked:
        children.setdefault(path[:-1], set()).add(path[-1])
    stack = [(os.dup(package_fd), ())]
    while stack:
        fd, prefix = stack.pop()
        try:
            actual = {os.fsencode(x) for x in os.listdir(fd)}
            expected = children.get(prefix, set())
            for name in actual | expected:
                at = (*prefix, name)
                entry = tracked.get(at)
                if entry is None:
                    if prefix == () and name in (b".git", b".lake"):
                        child = _open_dir(fd, name)
                        os.close(child)
                        continue
                    _refuse(f"unexpected source entry {b'/'.join(at)!r}")
                mode, oid = entry
                if mode == b"160000":
                    if name not in actual:
                        continue
                    child = _open_dir(fd, name)
                    try:
                        if _statx_mount_id(child) != _statx_mount_id(fd) or os.listdir(child):
                            _refuse("aesop gitlink is mounted or populated")
                    finally:
                        os.close(child)
                    continue
                if name not in actual:
                    _refuse(f"missing tracked source {b'/'.join(at)!r}")
                info = os.stat(name, dir_fd=fd, follow_symlinks=False)
                if mode == b"40000":
                    if not stat.S_ISDIR(info.st_mode):
                        _refuse("tracked directory changed type")
                    stack.append((_open_dir(fd, name), at))
                elif mode == b"120000":
                    if not stat.S_ISLNK(info.st_mode):
                        _refuse("tracked symlink changed type")
                    raw = os.fsencode(os.readlink(name, dir_fd=fd))
                    if raw != objects.get(oid, b"blob"):
                        _refuse("tracked symlink text differs from pin")
                    _resolve_link(at, raw, tracked, objects)
                else:
                    if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
                        _refuse("tracked source is linked or special")
                    payload = objects.get(oid, b"blob")
                    if bool(info.st_mode & 0o111) != (mode == b"100755"):
                        _refuse("tracked executable bit differs from pin")
                    if _read_file(fd, name, len(payload)) != payload:
                        _refuse("tracked source bytes differ from pin")
        finally:
            os.close(fd)


def verify_source_packages(packages_root: Path, revisions: dict[str, str], *,
                           reader_git_dir: Path) -> None:
    """Raise ValueError/OSError if any package differs from its SHA-1 commit.

    ``reader_git_dir`` is a preprovisioned minimal bare reader outside package
    roots. The function is read-only. It exempts only untracked root .git/.lake
    directories, and the current aesop empty gitlink.
    """
    if not revisions or any(not isinstance(name, str) or not _NAME.fullmatch(name) or
                            not isinstance(rev, str) or
                            not _HEX.fullmatch(rev.encode("ascii"))
                            for name, rev in revisions.items()):
        _refuse("invalid package names or SHA-1 revisions")
    _check_reader(reader_git_dir)
    root_fd = os.open(packages_root, _DIR)
    try:
        if {os.fsencode(x) for x in os.listdir(root_fd)} != {name.encode() for name in revisions}:
            _refuse("package inventory differs from manifest")
        for name, revision in revisions.items():
            package_fd = _open_dir(root_fd, name.encode())
            try:
                git_fd = _open_dir(package_fd, b".git")
                try:
                    head = _read_file(git_fd, b"HEAD", 128)
                    if head != revision.encode() + b"\n":
                        _refuse(f"{name} HEAD differs from manifest")
                    _check_object_store(git_fd)
                    objects = _Objects(reader_git_dir, packages_root / name / ".git/objects")
                    try:
                        commit = objects.get(revision.encode(), b"commit")
                        tracked = _tracked(objects, _commit_tree(commit), name)
                        _check_worktree(package_fd, tracked, objects)
                    finally:
                        objects.close()
                finally:
                    os.close(git_fd)
            finally:
                os.close(package_fd)
    finally:
        os.close(root_fd)
