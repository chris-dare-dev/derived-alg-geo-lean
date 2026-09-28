#!/usr/bin/env python3
"""Descriptor-relative I/O for private cache archives and disposable stages.

The caller must own and lock the stage's parent.  Every descendant lookup is
relative to an opened directory and refuses symlink traversal.  Archive links
are created only after regular contents, and are never followed by this module.
"""

from __future__ import annotations

import hashlib
import ctypes
import os
from pathlib import Path
import posixpath
import shutil
import stat
import tarfile
import uuid


DIR_FLAGS = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
FILE_FLAGS = os.O_RDONLY | os.O_NOFOLLOW


def _parts(name: str) -> tuple[str, ...]:
    if not name or name.startswith("/") or "//" in name:
        raise ValueError(f"unsafe archive member: {name}")
    parts = tuple(name.rstrip("/").split("/"))
    if any(part in ("", ".", "..") for part in parts):
        raise ValueError(f"unsafe archive member: {name}")
    return parts


def _parent_fd(root_fd: int, parts: tuple[str, ...]) -> int:
    fd = os.dup(root_fd)
    try:
        for part in parts:
            next_fd = os.open(part, DIR_FLAGS, dir_fd=fd)
            os.close(fd)
            fd = next_fd
        return fd
    except BaseException:
        os.close(fd)
        raise


def _sha256_fd(fd: int) -> str:
    os.lseek(fd, 0, os.SEEK_SET)
    digest = hashlib.sha256()
    while block := os.read(fd, 4 * 1024 * 1024):
        digest.update(block)
    os.lseek(fd, 0, os.SEEK_SET)
    return digest.hexdigest()


def extract_checked_archive(archive: Path, root_fd: int, expected_sha256: str,
                            package_names: set[str]) -> None:
    """Extract a checked tar into an empty owned directory, never following links."""
    archive_fd = os.open(archive, FILE_FLAGS)
    try:
        if not stat.S_ISREG(os.fstat(archive_fd).st_mode):
            raise ValueError("snapshot archive is not a regular file")
        if _sha256_fd(archive_fd) != expected_sha256:
            raise ValueError("snapshot archive checksum failed")
        with os.fdopen(os.dup(archive_fd), "rb") as source:
            with tarfile.open(fileobj=source, mode="r:") as tar:
                entries: list[tuple[tarfile.TarInfo, tuple[str, ...]]] = []
                seen: set[tuple[str, ...]] = set()
                for member in tar:
                    parts = _parts(member.name)
                    if parts in seen:
                        raise ValueError(f"duplicate archive member: {member.name}")
                    seen.add(parts)
                    if parts[0] == "packages":
                        if len(parts) > 1 and parts[1] not in package_names:
                            raise ValueError(f"unlisted package in archive: {member.name}")
                    elif parts[0] != "build":
                        raise ValueError(f"unexpected archive root: {member.name}")
                    if not (member.isdir() or member.isfile() or member.issym()):
                        raise ValueError(f"unsupported archive member: {member.name}")
                    if member.issym():
                        link = member.linkname
                        if not link or link.startswith("/"):
                            raise ValueError(f"unsafe archive link: {member.name}")
                        combined = posixpath.normpath(posixpath.join(*parts[:-1], link))
                        boundary = "/".join(parts[:2]) if parts[0] == "packages" else "build"
                        if not (combined == boundary or combined.startswith(boundary + "/")):
                            raise ValueError(f"archive link escapes its tree: {member.name}")
                    entries.append((member, parts))
                directories = [(m, p) for m, p in entries if m.isdir()]
                regular = [(m, p) for m, p in entries if m.isfile()]
                links = [(m, p) for m, p in entries if m.issym()]
                for member, parts in sorted(directories, key=lambda x: len(x[1])):
                    parent_fd = _parent_fd(root_fd, parts[:-1])
                    try:
                        os.mkdir(parts[-1], 0o700, dir_fd=parent_fd)
                    finally:
                        os.close(parent_fd)
                for member, parts in regular:
                    parent_fd = _parent_fd(root_fd, parts[:-1])
                    try:
                        output_fd = os.open(parts[-1], os.O_WRONLY | os.O_CREAT | os.O_EXCL |
                                            os.O_NOFOLLOW, 0o600, dir_fd=parent_fd)
                        try:
                            input_file = tar.extractfile(member)
                            if input_file is None:
                                raise ValueError(f"archive file has no bytes: {member.name}")
                            with input_file, os.fdopen(os.dup(output_fd), "wb") as output:
                                shutil.copyfileobj(input_file, output, 4 * 1024 * 1024)
                            os.fchmod(output_fd, member.mode & 0o777)
                        finally:
                            os.close(output_fd)
                    finally:
                        os.close(parent_fd)
                for member, parts in links:
                    parent_fd = _parent_fd(root_fd, parts[:-1])
                    try:
                        os.symlink(member.linkname, parts[-1], dir_fd=parent_fd)
                    finally:
                        os.close(parent_fd)
                for member, parts in sorted(directories, key=lambda x: len(x[1]), reverse=True):
                    dir_fd = _parent_fd(root_fd, parts)
                    try:
                        os.fchmod(dir_fd, member.mode & 0o777)
                    finally:
                        os.close(dir_fd)
        if _sha256_fd(archive_fd) != expected_sha256:
            raise ValueError("snapshot archive changed during extraction")
    finally:
        os.close(archive_fd)


def remove_owned_tree(parent_fd: int, name: str, expected: tuple[int, int]) -> None:
    """Remove one stage only when its name still denotes the opened inode."""
    stage_fd = os.open(name, DIR_FLAGS, dir_fd=parent_fd)
    try:
        info = os.fstat(stage_fd)
        if (info.st_dev, info.st_ino) != expected:
            raise ValueError("stage changed identity before cleanup")
        quarantine = _quarantine(parent_fd, name, expected)
        _remove_children(stage_fd)
        named = os.stat(quarantine, dir_fd=parent_fd, follow_symlinks=False)
        if (named.st_dev, named.st_ino) != expected:
            raise ValueError("stage changed identity during cleanup")
        os.rmdir(quarantine, dir_fd=parent_fd)
    finally:
        os.close(stage_fd)


def _quarantine(parent_fd: int, name: str, expected: tuple[int, int]) -> str:
    """Atomically take a child name aside, then confirm the moved inode."""
    alias = f".removing-{uuid.uuid4().hex}"
    named = os.stat(name, dir_fd=parent_fd, follow_symlinks=False)
    if (named.st_dev, named.st_ino) != expected:
        raise ValueError("stage child changed identity before quarantine")
    libc = ctypes.CDLL(None, use_errno=True)
    renameat2 = getattr(libc, "renameat2", None)
    if renameat2 is None:
        raise ValueError("Linux renameat2 is unavailable for cleanup")
    renameat2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int,
                          ctypes.c_char_p, ctypes.c_uint]
    renameat2.restype = ctypes.c_int
    if renameat2(parent_fd, os.fsencode(name), parent_fd, os.fsencode(alias), 1) != 0:
        code = ctypes.get_errno()
        raise OSError(code, os.strerror(code), name)
    moved = os.stat(alias, dir_fd=parent_fd, follow_symlinks=False)
    if (moved.st_dev, moved.st_ino) != expected:
        raise ValueError("stage child changed identity during quarantine")
    return alias


def _remove_children(parent_fd: int) -> None:
    for entry in list(os.scandir(parent_fd)):
        info = os.stat(entry.name, dir_fd=parent_fd, follow_symlinks=False)
        if stat.S_ISDIR(info.st_mode):
            child_fd = os.open(entry.name, DIR_FLAGS, dir_fd=parent_fd)
            try:
                opened = os.fstat(child_fd)
                if (opened.st_dev, opened.st_ino) != (info.st_dev, info.st_ino):
                    raise ValueError("stage child changed identity during cleanup")
                alias = _quarantine(parent_fd, entry.name,
                                    (opened.st_dev, opened.st_ino))
                _remove_children(child_fd)
                named = os.stat(alias, dir_fd=parent_fd, follow_symlinks=False)
                if (named.st_dev, named.st_ino) != (opened.st_dev, opened.st_ino):
                    raise ValueError("stage child changed identity during cleanup")
                os.rmdir(alias, dir_fd=parent_fd)
            finally:
                os.close(child_fd)
        elif stat.S_ISREG(info.st_mode) or stat.S_ISLNK(info.st_mode):
            alias = _quarantine(parent_fd, entry.name, (info.st_dev, info.st_ino))
            named = os.stat(alias, dir_fd=parent_fd, follow_symlinks=False)
            if (named.st_dev, named.st_ino) != (info.st_dev, info.st_ino):
                raise ValueError("stage child changed identity during cleanup")
            os.unlink(alias, dir_fd=parent_fd)
        else:
            raise ValueError("special stage entry during cleanup")
