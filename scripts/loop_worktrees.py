#!/usr/bin/env python3
"""Keep loop worktrees in one place, inside a disk budget, and retire them.

WHY THIS EXISTS. On 2026-09-28 the owner's 549 GB root filesystem filled to
99%. About 250 worktrees of this repository had accumulated in a week, under
two Codex homes and `/tmp`, each holding a ~10 GB private `.lake` from
`scripts/private_package_cache.py`: 358 of the 364 GB were Lake build output.
The run-loop skill created a worktree for every issue and every attempt,
told runs to preserve older checkouts, and said "remove the worktree" only in
prose after a merge, so nothing ever did.

Codex does not clean these up. Its worktree cleanup (`[desktop]
worktree-keep-count`, default 15) manages only worktrees the Codex app itself
created; one made with `git worktree add` is either invisible to it or, at the
managed depth under its root, looks ownerless and is deleted first, in use or
not. `/tmp` is tmpfs here and wiped at reboot, which orphaned 34 worktree
entries and left four detached commits reachable from nothing.

Three commands, used by the run-loop skill:

  root     print the directory new loop worktrees go in, creating it
  check    exit 1, saying why, when a new seeded worktree would break the budget
  retire   remove one finished worktree without losing work

The root is `$DAG_WORKTREE_ROOT`, else `git config dag.worktreeRoot`, else
`~/wt/<checkout name>`. It may not be on tmpfs, inside a Codex home, or inside
the shared checkout.

The budget is a disk floor and a count. A new worktree needs its seed
(`dag.worktreeSeedGiB`, default 12) on top of `dag.worktreeMinFreeGiB`
(default 60) free at the root, and the root may hold at most `dag.worktreeMax`
(default 20) worktrees. Each setting also reads `$DAG_WORKTREE_SEED_GIB`,
`$DAG_WORKTREE_MIN_FREE_GIB` and `$DAG_WORKTREE_MAX`, which win.

`retire` removes a linked worktree of this repository only when it is clean,
no other process has its working directory inside it, no other worktree's
`.lake/packages` symlink resolves into it, and its commits are safe elsewhere:
its branch's pull request merged, or its HEAD is on a remote-tracking ref.
Removal is `git worktree remove` without `--force`, so Git re-checks
cleanliness itself. A merged branch is then deleted locally too; squash merges
leave it unreachable from `main`, so that deletion needs the merged PR.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

GIB = 1024**3
DEFAULTS = {"worktreeMinFreeGiB": 60.0, "worktreeSeedGiB": 12.0, "worktreeMax": 20}
ENV = {"worktreeRoot": "DAG_WORKTREE_ROOT", "worktreeMinFreeGiB": "DAG_WORKTREE_MIN_FREE_GIB",
       "worktreeSeedGiB": "DAG_WORKTREE_SEED_GIB", "worktreeMax": "DAG_WORKTREE_MAX"}
VOLATILE_FS = {"tmpfs", "ramfs"}
CODEX_MARKER = ".codex-worktree-name"


class Refused(Exception):
    """A command declined to act; the message says why and what to do."""


def git(*args: str, cwd: Path) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "--no-optional-locks", *args], cwd=cwd,
                          capture_output=True, text=True)


def repository(start: Path) -> Path:
    """The shared checkout that owns the worktree containing `start`."""
    result = git("rev-parse", "--path-format=absolute", "--git-common-dir", cwd=start)
    if result.returncode:
        raise Refused(f"not inside a Git worktree: {start}")
    return Path(result.stdout.strip()).parent


def setting(repo: Path, key: str) -> str | None:
    value = os.environ.get(ENV[key])
    if value:
        return value
    result = git("config", "--get", f"dag.{key}", cwd=repo)
    if result.returncode or not result.stdout.strip():
        return None
    return result.stdout.strip()


def number(repo: Path, key: str) -> float:
    raw = setting(repo, key)
    if raw is None:
        return float(DEFAULTS[key])
    try:
        return float(raw)
    except ValueError:
        raise Refused(f"dag.{key} is not a number: {raw!r}") from None


def _unescape(field: str) -> str:
    return re.sub(r"\\([0-7]{3})", lambda m: chr(int(m.group(1), 8)), field)


def fs_type(path: Path) -> str:
    """Type of the filesystem that holds `path`, or would hold it once created."""
    probe = path
    while not probe.exists():
        probe = probe.parent
    probe = probe.resolve()
    best, kind = "", ""
    for line in Path("/proc/self/mountinfo").read_text().splitlines():
        left, _, right = line.partition(" - ")
        mount = _unescape(left.split()[4])
        if (probe == Path(mount) or probe.is_relative_to(mount)) and len(mount) >= len(best):
            best, kind = mount, right.split()[0]
    return kind


def worktree_root(repo: Path) -> Path:
    raw = setting(repo, "worktreeRoot")
    root = Path(raw).expanduser() if raw else Path.home() / "wt" / repo.name
    if not root.is_absolute():
        raise Refused(f"worktree root must be absolute: {root}")
    root = Path(os.path.normpath(root))
    if any(part.startswith(".codex") for part in root.parts):
        raise Refused(f"worktree root is inside a Codex home, whose cleanup deletes "
                      f"worktrees it did not create: {root}")
    if root == repo or root.is_relative_to(repo):
        raise Refused(f"worktree root is inside the shared checkout: {root}")
    kind = fs_type(root)
    if kind in VOLATILE_FS:
        raise Refused(f"worktree root is on {kind}, which a reboot wipes: {root}")
    return root


def worktrees(repo: Path) -> list[dict]:
    """`git worktree list --porcelain` records; the first is the shared checkout."""
    records, current = [], {}
    for line in git("worktree", "list", "--porcelain", cwd=repo).stdout.splitlines():
        if not line:
            if current:
                records.append(current)
            current = {}
            continue
        key, _, value = line.partition(" ")
        current[key] = value or True
    if current:
        records.append(current)
    return records


def human(size: float) -> str:
    return f"{size / GIB:.1f} GiB"


def check(repo: Path) -> str:
    root = worktree_root(repo)
    root.mkdir(parents=True, exist_ok=True)
    free = shutil.disk_usage(root).free
    floor = number(repo, "worktreeMinFreeGiB") * GIB
    seed = number(repo, "worktreeSeedGiB") * GIB
    cap = int(number(repo, "worktreeMax"))
    live = [w for w in worktrees(repo)[1:]
            if Path(w["worktree"]).is_relative_to(root) and Path(w["worktree"]).is_dir()]
    problems = []
    if free < floor + seed:
        problems.append(f"{human(free)} free at {root}; a seeded worktree needs about "
                        f"{human(seed)} and {human(floor)} must stay free")
    if len(live) >= cap:
        problems.append(f"{len(live)} worktrees under {root}; the cap is {cap}")
    if problems:
        raise Refused("worktree budget refused a new worktree:\n  " + "\n  ".join(problems) +
                      "\nRetire finished worktrees (`loop_worktrees.py retire <path>`) and run "
                      "check again. If it still refuses, freeing disk is the owner's call.")
    return f"worktree budget ok: {human(free)} free, {len(live)} of {cap} worktrees under {root}"


def _ancestors() -> set[int]:
    pids, pid = set(), os.getpid()
    while pid > 1 and pid not in pids:
        pids.add(pid)
        try:
            stat = Path(f"/proc/{pid}/stat").read_text()
        except OSError:
            break
        pid = int(stat.rsplit(")", 1)[1].split()[1])
    return pids


def processes_inside(path: Path) -> list[int]:
    """Other processes whose working directory is `path` or below it."""
    mine, found = _ancestors(), []
    for link in Path("/proc").glob("[0-9]*/cwd"):
        pid = int(link.parent.name)
        if pid in mine:
            continue
        try:
            cwd = Path(os.readlink(link))
        except OSError:
            continue
        if cwd == path or cwd.is_relative_to(path):
            found.append(pid)
    return found


def package_links_into(checkouts: list[Path], target: Path) -> list[Path]:
    """Checkouts whose `.lake/packages` symlink chain passes through `target`."""
    users = []
    for checkout in checkouts:
        link, seen = checkout / ".lake" / "packages", set()
        while link.is_symlink() and link not in seen:
            seen.add(link)
            link = Path(os.path.normpath(link.parent / os.readlink(link)))
            if link == target or link.is_relative_to(target):
                users.append(checkout)
                break
    return users


def pr_merged(repo: Path, branch: str) -> bool:
    """True only when GitHub reports a merged pull request from `branch`."""
    try:
        result = subprocess.run(["gh", "pr", "list", "--head", branch, "--state", "merged",
                                 "--json", "number", "--limit", "1"],
                                cwd=repo, capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return False
    if result.returncode:
        return False
    try:
        return bool(json.loads(result.stdout or "[]"))
    except ValueError:
        return False


def _real(path: str | Path) -> Path:
    return Path(os.path.realpath(path))


def retire(repo: Path, path: Path, *, dry_run: bool) -> str:
    target = _real(path)
    records = worktrees(repo)
    if target == _real(records[0]["worktree"]):
        raise Refused("the shared checkout is never retired")
    record = next((r for r in records[1:] if _real(r["worktree"]) == target), None)
    if record is None:
        raise Refused(f"not a linked worktree of {repo}: {target}")
    if "locked" in record:
        raise Refused(f"worktree is locked: {target}")
    if not target.is_dir():
        raise Refused(f"worktree directory is missing; `git worktree prune` drops the entry: {target}")
    busy = processes_inside(target)
    if busy:
        raise Refused(f"processes are working inside it (pids {', '.join(map(str, busy))}): {target}")
    status = git("status", "--porcelain", cwd=target)
    if status.returncode:
        raise Refused(f"git status failed in {target}: {status.stderr.strip()}")
    if status.stdout.strip():
        raise Refused(f"uncommitted changes; commit and push them first: {target}")
    others = [_real(r["worktree"]) for r in records if _real(r["worktree"]) != target]
    users = package_links_into(others, target)
    if users:
        raise Refused(f"other worktrees use its .lake/packages ({', '.join(map(str, users))}); "
                      f"retire those first: {target}")
    head = record["HEAD"]
    branch = record["branch"].removeprefix("refs/heads/") if isinstance(record.get("branch"), str) else None
    merged = branch is not None and pr_merged(repo, branch)
    pushed = bool(git("for-each-ref", "--contains", head, "--count=1", "refs/remotes",
                      cwd=repo).stdout.strip())
    if not (merged or pushed):
        raise Refused(f"its HEAD {head[:12]} is on no remote-tracking ref and no merged pull "
                      f"request; push {'branch ' + branch if branch else 'it to a branch'} first: {target}")
    plan = [f"git worktree remove {target}"]
    wrapper = target.parent
    wrapped = (wrapper / CODEX_MARKER).is_file() and set(os.listdir(wrapper)) == {CODEX_MARKER, target.name}
    if wrapped:
        plan.append(f"remove the empty Codex wrapper {wrapper}")
    if merged:
        plan.append(f"git branch -D {branch} (its pull request merged)")
    if dry_run:
        return "would " + "; ".join(plan)
    removed = git("worktree", "remove", str(target), cwd=repo)
    if removed.returncode:
        raise Refused(f"git worktree remove refused: {removed.stderr.strip()}")
    if wrapped:
        try:
            if (wrapper / CODEX_MARKER).stat().st_size == 0:
                (wrapper / CODEX_MARKER).unlink()
                wrapper.rmdir()
        except OSError as error:
            plan.append(f"(left Codex wrapper {wrapper}: {error})")
    if merged:
        deleted = git("branch", "-D", branch, cwd=repo)
        if deleted.returncode:
            return f"retired {target}; kept branch {branch}: {deleted.stderr.strip()}"
    return "retired: " + "; ".join(plan)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("root", help="print (and create) the loop worktree root")
    commands.add_parser("check", help="refuse when a new worktree would break the budget")
    retiring = commands.add_parser("retire", help="remove a finished worktree without losing work")
    retiring.add_argument("path", type=Path)
    retiring.add_argument("--dry-run", action="store_true")
    parser.add_argument("--repo", type=Path, help="checkout to act for (default: this script's)")
    args = parser.parse_args(argv)
    try:
        if args.command == "retire":
            start = args.path if args.path.is_dir() else args.path.parent
        else:
            start = args.repo or Path(__file__).resolve().parent
        repo = repository(start if start.is_dir() else Path.cwd())
        if args.repo and repository(args.repo) != repo:
            raise Refused(f"{args.path} is not a worktree of {args.repo}")
        if args.command == "root":
            root = worktree_root(repo)
            root.mkdir(parents=True, exist_ok=True)
            print(root)
        elif args.command == "check":
            print(check(repo))
        else:
            print(retire(repo, args.path, dry_run=args.dry_run))
    except Refused as refusal:
        print(refusal, file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
