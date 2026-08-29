#!/usr/bin/env python3
"""Report which worktrees of this clone are running without the local-build gate.

## Why this cannot be a hook

`scripts/check_local_build.py` is wired in the TRACKED `.claude/settings.json`,
so it reaches every worktree whose checkout contains the commit that added it --
and no others. A worktree parked on an older commit has no `PreToolUse` entry,
nothing is refused, and the agent working there gets no signal that a rule
exists. That is #837 hole 1, and it is not self-correcting: the stale checkout
has no copy of the fix either, so no in-repo enforcement can reach backwards
into it.

This script does the one thing an in-repo file still CAN do about that: make the
gap visible. Run it from a current checkout to find the stale ones.

    python3 scripts/check_worktree_hooks.py            # report, always exit 0
    python3 scripts/check_worktree_hooks.py --strict    # exit 1 if any gap

It is deliberately NOT a gate in `scripts/gates.sh`. The answer is a property of
this machine's checkouts, not of the branch, and CI has exactly one worktree
which is current by construction -- so there it would pass without ever having
looked at anything.

## What counts as covered

Both halves have to be present in the worktree, because either alone is inert:

  * a `PreToolUse` hook in `.claude/settings.json` naming `check_local_build.py`;
  * the script itself at `scripts/check_local_build.py`.

The umbrella refusal (#837 hole 2) is reported separately, because a worktree
can predate it while still having the hook -- which is exactly the state
`dag-serre` was in on 2026-08-27 when `lake build DerivedAlgGeo` ran there for
over an hour.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


def git(*args: str) -> str:
    return subprocess.run(
        ["git", *args], capture_output=True, text=True, check=False
    ).stdout.strip()


def worktrees() -> list[dict[str, str]]:
    """Every worktree of this clone, as {path, head, branch}."""
    out: list[dict[str, str]] = []
    current: dict[str, str] = {}
    for line in git("worktree", "list", "--porcelain").splitlines():
        if not line:
            if current:
                out.append(current)
                current = {}
            continue
        key, _, value = line.partition(" ")
        if key == "worktree":
            current = {"path": value, "head": "", "branch": "(detached)"}
        elif key == "HEAD":
            current["head"] = value
        elif key == "branch":
            current["branch"] = value.rsplit("/", 1)[-1]
    if current:
        out.append(current)
    return out


def hook_present(root: Path) -> bool:
    """Is check_local_build.py wired as a PreToolUse hook in this worktree?"""
    settings = root / ".claude" / "settings.json"
    try:
        payload = json.loads(settings.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    entries = (payload.get("hooks") or {}).get("PreToolUse") or []
    for entry in entries:
        for hook in entry.get("hooks") or []:
            if "check_local_build.py" in (hook.get("command") or ""):
                return True
    return False


def refuses_umbrella(root: Path) -> bool:
    """Does this worktree's copy of the script carry the #837 hole-2 fix?

    Read rather than executed: a stale worktree's script is not something to
    run, and the marker is unambiguous.
    """
    script = root / "scripts" / "check_local_build.py"
    try:
        return "UMBRELLAS" in script.read_text(encoding="utf-8")
    except OSError:
        return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--strict",
        action="store_true",
        help="exit 1 if any worktree is missing the hook or the umbrella fix",
    )
    args = parser.parse_args()

    trees = worktrees()
    if not trees:
        print("no worktrees found -- is this a git repository?", file=sys.stderr)
        return 0

    git("fetch", "--quiet", "origin")
    rows = []
    for tree in trees:
        root = Path(tree["path"])
        behind = git("rev-list", "--count", f"{tree['head']}..origin/main")
        rows.append(
            {
                "name": root.name,
                "branch": tree["branch"],
                "behind": behind or "?",
                "hook": hook_present(root),
                "umbrella": refuses_umbrella(root),
            }
        )

    width = max(len(r["name"]) for r in rows)
    print(f"{'worktree'.ljust(width)}  behind  hook     umbrella")
    print(f"{'-' * width}  ------  -------  --------")
    for row in sorted(rows, key=lambda r: (r["hook"], r["umbrella"], r["name"])):
        print(
            f"{row['name'].ljust(width)}  "
            f"{row['behind']:>6}  "
            f"{'present' if row['hook'] else 'ABSENT ':<7}  "
            f"{'refused' if row['umbrella'] else 'ALLOWED'}"
        )

    no_hook = [r for r in rows if not r["hook"]]
    allows = [r for r in rows if r["hook"] and not r["umbrella"]]
    print()
    print(f"{len(rows)} worktrees: {len(no_hook)} with no local-build hook at all, "
          f"{len(allows)} hooked but still allowing the umbrella build.")
    if no_hook:
        print(
            "\nA worktree with no hook cannot be fixed from inside the repository:\n"
            "its checkout predates the hook, so it has no copy of any in-repo\n"
            "enforcement either. Rebase it onto origin/main, or retire it."
        )
    return 1 if args.strict and (no_hook or allows) else 0


if __name__ == "__main__":
    sys.exit(main())
