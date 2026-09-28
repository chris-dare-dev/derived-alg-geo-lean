#!/usr/bin/env python3
"""Read-only, descriptor-relative ownership scan for a private Lake tree.

This detects aliases visible at a quiescent pickup boundary. It does not guard
against a same-UID process mutating the tree after the scan.
"""

from __future__ import annotations

import os
from pathlib import Path
import posixpath
import re
import stat


DIR = os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW
ENTRY = os.O_PATH | os.O_NOFOLLOW


def _mount_id(fd: int) -> int:
    """Read Linux's mount ID for an already opened inode, not a path lookup."""
    with open(f"/proc/self/fdinfo/{fd}", encoding="ascii") as info:
        for line in info:
            if line.startswith("mnt_id:\t"):
                return int(line.split()[1])
    raise ValueError("Linux fd mount IDs are unavailable")


def _identity(info: os.stat_result) -> tuple[int, int, int]:
    return info.st_dev, info.st_ino, stat.S_IFMT(info.st_mode)


_ESCAPE = re.compile(r"\\([0-7]{3})")


def _mount_path(raw: str) -> str:
    return _ESCAPE.sub(lambda match: chr(int(match.group(1), 8)), raw)


def _overlaps(left: str, right: str) -> bool:
    left, right = left.rstrip("/") or "/", right.rstrip("/") or "/"
    return (left == right or left == "/" or right == "/" or
            left.startswith(right + "/") or right.startswith(left + "/"))


def _check_parent_mount_alias(fd: int, target: Path, child_name: str) -> None:
    """Reject both incoming and outgoing bind aliases of this Lake generation."""
    mount = _mount_id(fd)
    entries = []
    with open("/proc/self/mountinfo", encoding="utf-8", errors="surrogateescape") as inventory:
        for line in inventory:
            fields = line.split(" - ", 1)[0].split()
            if len(fields) < 5:
                raise ValueError("malformed Linux mount inventory")
            entries.append((int(fields[0]), fields[2],
                            _mount_path(fields[3]), _mount_path(fields[4])))
    current = [entry for entry in entries if entry[0] == mount]
    if len(current) != 1:
        raise ValueError("worktree parent mount has no unique inventory entry")
    _, device, root, mountpoint = current[0]
    if root != "/" or sum(entry[1:3] == (device, root) for entry in entries) != 1:
        raise ValueError("worktree parent is beneath a mount alias")
    try:
        relative = target.relative_to(Path(mountpoint))
    except ValueError as error:
        raise ValueError("worktree path differs from its mount inventory") from error
    backing = posixpath.normpath(posixpath.join(root, relative.as_posix(), child_name))
    for other_id, other_device, other_root, _ in entries:
        if other_id != mount and other_device == device and _overlaps(other_root, backing):
            raise ValueError("private cache is exposed by another mount")


def _walk(fd: int, mount: int, name: str,
          allowed_links: dict[str, str]) -> None:
    if _mount_id(fd) != mount:
        raise ValueError(f"private cache crosses a mount: {name}")
    with os.scandir(fd) as entries:
        for entry in entries:
            child_name = entry.name
            shown = f"{name}/{child_name}"
            before = os.stat(child_name, dir_fd=fd, follow_symlinks=False)
            child_fd = os.open(child_name, ENTRY, dir_fd=fd)
            try:
                opened = os.fstat(child_fd)
                if _identity(before) != _identity(opened):
                    raise ValueError(f"private cache entry changed while opening: {shown}")
                if _mount_id(child_fd) != mount:
                    raise ValueError(f"private cache crosses a mount: {shown}")
                mode = opened.st_mode
                if stat.S_ISREG(mode):
                    if opened.st_nlink != 1:
                        raise ValueError(f"private cache has a hardlinked file: {shown}")
                elif stat.S_ISDIR(mode):
                    read_fd = os.open(child_name, DIR, dir_fd=fd)
                    try:
                        if _identity(os.fstat(read_fd)) != _identity(opened):
                            raise ValueError(f"private cache directory changed: {shown}")
                        _walk(read_fd, mount, shown, allowed_links)
                    finally:
                        os.close(read_fd)
                elif stat.S_ISLNK(mode):
                    raw = os.readlink(child_name, dir_fd=fd)
                    relative = shown.split("/", 1)[1]
                    if relative not in allowed_links or allowed_links[relative] != raw:
                        raise ValueError(f"private cache link escapes tree or is not pinned: {shown}")
                else:
                    raise ValueError(f"private cache has a special file: {shown}")
                after = os.stat(child_name, dir_fd=fd, follow_symlinks=False)
                if _identity(after) != _identity(opened):
                    raise ValueError(f"private cache entry changed during scan: {shown}")
            finally:
                os.close(child_fd)


def scan_owned_child(target: Path, child_name: str,
                     allowed_links: dict[str, str] | None = None) -> None:
    """Scan a named Lake generation under a worktree, including its mount."""
    if not child_name or child_name in (".", "..") or "/" in child_name:
        raise ValueError("owned child must be one simple name")
    target = target.absolute()
    parent_fd = os.open(target.parent, DIR)
    try:
        _check_parent_mount_alias(parent_fd, target, child_name)
        target_fd = os.open(target.name, DIR, dir_fd=parent_fd)
        try:
            mount = _mount_id(parent_fd)
            if _mount_id(target_fd) != mount:
                raise ValueError("worktree root is a mount alias")
            lake_fd = os.open(child_name, DIR, dir_fd=target_fd)
            try:
                if _mount_id(lake_fd) != mount:
                    raise ValueError(f"{child_name} is a mount alias")
                _walk(lake_fd, mount, child_name, allowed_links or {})
                named = os.stat(child_name, dir_fd=target_fd, follow_symlinks=False)
                if _identity(named) != _identity(os.fstat(lake_fd)):
                    raise ValueError(f"{child_name} changed during scan")
            finally:
                os.close(lake_fd)
        finally:
            os.close(target_fd)
    finally:
        os.close(parent_fd)


def scan_private_lake(target: Path,
                      allowed_links: dict[str, str] | None = None) -> None:
    """Refuse hardlinks, special files and mount aliases in a target's `.lake`."""
    scan_owned_child(target, ".lake", allowed_links)
