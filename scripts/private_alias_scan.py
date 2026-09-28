#!/usr/bin/env python3
"""Read-only, descriptor-relative ownership scan for a private Lake tree.

This detects aliases visible at a quiescent pickup boundary. It does not guard
against a same-UID process mutating the tree after the scan.
"""

from __future__ import annotations

import os
from pathlib import Path
import posixpath
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


def _check_parent_mount_alias(fd: int) -> None:
    """Reject a bind-mounted ancestor while allowing a unique filesystem root."""
    mount = _mount_id(fd)
    entries = []
    with open("/proc/self/mountinfo", encoding="utf-8") as inventory:
        for line in inventory:
            fields = line.split(" - ", 1)[0].split()
            if len(fields) < 5:
                raise ValueError("malformed Linux mount inventory")
            entries.append((int(fields[0]), fields[2], fields[3]))
    current = [entry for entry in entries if entry[0] == mount]
    if len(current) != 1:
        raise ValueError("worktree parent mount has no unique inventory entry")
    _, device, root = current[0]
    if root != "/" or sum(entry[1:] == (device, root) for entry in entries) != 1:
        raise ValueError("worktree parent is beneath a mount alias")


def _walk(fd: int, mount: int, name: str) -> None:
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
                        _walk(read_fd, mount, shown)
                    finally:
                        os.close(read_fd)
                elif stat.S_ISLNK(mode):
                    raw = os.readlink(child_name, dir_fd=fd)
                    destination = posixpath.normpath(posixpath.join(name, raw))
                    root = name.split("/", 1)[0]
                    if (not raw or raw.startswith("/") or
                            not (destination == root or
                                 destination.startswith(root + "/"))):
                        raise ValueError(f"private cache link escapes tree: {shown}")
                else:
                    raise ValueError(f"private cache has a special file: {shown}")
                after = os.stat(child_name, dir_fd=fd, follow_symlinks=False)
                if _identity(after) != _identity(opened):
                    raise ValueError(f"private cache entry changed during scan: {shown}")
            finally:
                os.close(child_fd)


def scan_owned_child(target: Path, child_name: str) -> None:
    """Scan a named Lake generation under a worktree, including its mount."""
    if not child_name or child_name in (".", "..") or "/" in child_name:
        raise ValueError("owned child must be one simple name")
    target = target.absolute()
    parent_fd = os.open(target.parent, DIR)
    try:
        _check_parent_mount_alias(parent_fd)
        target_fd = os.open(target.name, DIR, dir_fd=parent_fd)
        try:
            mount = _mount_id(parent_fd)
            if _mount_id(target_fd) != mount:
                raise ValueError("worktree root is a mount alias")
            lake_fd = os.open(child_name, DIR, dir_fd=target_fd)
            try:
                if _mount_id(lake_fd) != mount:
                    raise ValueError(f"{child_name} is a mount alias")
                _walk(lake_fd, mount, child_name)
                named = os.stat(child_name, dir_fd=target_fd, follow_symlinks=False)
                if _identity(named) != _identity(os.fstat(lake_fd)):
                    raise ValueError(f"{child_name} changed during scan")
            finally:
                os.close(lake_fd)
        finally:
            os.close(target_fd)
    finally:
        os.close(parent_fd)


def scan_private_lake(target: Path) -> None:
    """Refuse hardlinks, special files and mount aliases in a target's `.lake`."""
    scan_owned_child(target, ".lake")
