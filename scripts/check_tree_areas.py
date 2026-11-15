#!/usr/bin/env python3
"""Invariant: every tracked file lies in an area that CREDO.md lists.

AREAS is the "In this repository" table of CREDO.md written as path patterns:
product, authored records, prose and tooling. A file in none of them is a
plan, a review, a run log, a generated listing or some other thing the tree
refuses. LEGACY names the files outside every area that the tree still holds.
They may be deleted or shortened, never added to, and LEGACY only shrinks.

Usage: python3 scripts/check_tree_areas.py [BASE]

With BASE, a change from BASE to HEAD is also judged: no LEGACY file grows and
no LEGACY entry is new. Without one, only HEAD's tree is judged. Uncommitted
work is not judged. Standard library only.
"""

from __future__ import annotations

import ast
import re
import subprocess
import sys

from _output import force_utf8_output

THIS_FILE = "scripts/check_tree_areas.py"

AREAS = {
    "product": (
        r"DerivedAlgGeo/.+\.lean",
        r"DerivedAlgGeo\.lean",
        r"exe/[^/]+\.lean",
        r"lakefile\.toml",
        r"lean-toolchain",
        r"lake-manifest\.json",
    ),
    "authored record": (
        r"registry/[^/]+\.json",
        r"formalization\.yaml",
        r"attest/review\.yaml",
        r"pins\.json",
    ),
    "prose": (
        r"(README|CONTRIBUTING|CREDO|AGENTS|CLAUDE|LICENSE)\.md",
        r"\.claude/skills/[^/]+/SKILL\.md",
        r"\.claude/agents/[^/]+\.md",
        r"\.github/pull_request_template\.md",
        r"\.github/ISSUE_TEMPLATE/[^/]+\.md",
    ),
    # Checks and their runners, one level deep. A script's own tests and
    # fixtures have no area (CREDO.md §3).
    "tooling": (
        r"scripts/(?!test_)[^/]+\.(py|sh|lean)",
        r"scripts/requirements-[^/]+\.txt",
        r"\.github/workflows/[^/]+\.yml",
        r"\.github/actionlint\.yaml",
        r"\.claude/settings\.json",
        r"\.claude/loop-authority\.yaml",
        r"\.agents/skills/[^/]+",
        r"docbuild/(lakefile\.toml|lean-toolchain|lake-manifest\.json|\.gitignore)",
        r"DerivedAlgGeoSweep\.lean",
        r"\.gitignore",
    ),
    # Each has its own ratchet. A new list needs a line here and in CREDO.md.
    "exceptions list": (
        r"scripts/nolints\.json",
        r"scripts/style-baseline\.json",
        r"scripts/warning-baseline\.json",
        r"scripts/single_instantiation_baseline\.txt",
        r"scripts/single_instantiation_records/[^/]+\.txt",
    ),
}

# An entry ending in / names a directory; any other names one file.
LEGACY = (
    ".claude/README.md",
    ".claude/decisions/",
    ".claude/references/",
    ".claude/roadmap/",
    "docs/",
    "registry/README.md",
    "scripts/fixtures/",
    "scripts/private-reader.git/",
)

PATTERNS = [(area, re.compile(p)) for area, ps in AREAS.items() for p in ps]


def git(*args: str) -> str:
    return subprocess.run(
        ["git", "-c", "core.quotePath=false", *args],
        check=True, capture_output=True, text=True,
    ).stdout


def area_of(path: str) -> str | None:
    return next((a for a, rx in PATTERNS if rx.fullmatch(path)), None)


def in_legacy(path: str, legacy: tuple[str, ...] | set[str]) -> bool:
    return any(
        path.startswith(e) if e.endswith("/") else path == e for e in legacy
    )


def legacy_at(rev: str) -> set[str] | None:
    """LEGACY as REV defined it, or None if REV predates this file."""
    try:
        source = git("show", f"{rev}:{THIS_FILE}")
    except subprocess.CalledProcessError:
        return None
    for node in ast.parse(source).body:
        if isinstance(node, ast.Assign) and any(
            isinstance(t, ast.Name) and t.id == "LEGACY" for t in node.targets
        ):
            return set(ast.literal_eval(node.value))
    return set()


def usable(base: str | None) -> bool:
    if not base or set(base) == {"0"}:
        return False
    try:
        git("cat-file", "-e", f"{base}^{{commit}}")
    except subprocess.CalledProcessError:
        return False
    return True


def main(argv: list[str]) -> int:
    base = argv[0] if argv else None
    errors: list[str] = []

    tree = git("ls-tree", "-r", "--name-only", "HEAD").splitlines()
    outside = [p for p in tree if area_of(p) is None]
    for path in outside:
        if not in_legacy(path, LEGACY):
            errors.append(
                f"{path}: in no area CREDO.md lists. A record of how a change "
                "was made goes in the issue, the pull request or the wiki; "
                "anything a command regenerates stays out of git"
            )
    for entry in LEGACY:
        if not any(in_legacy(p, (entry,)) for p in outside):
            errors.append(f"LEGACY entry {entry!r} names no file outside the areas; delete it")

    if usable(base):
        before = legacy_at(base)
        for entry in sorted(set(LEGACY) - (before if before is not None else set(LEGACY))):
            errors.append(f"LEGACY entry {entry!r} is new; LEGACY only shrinks")
        present = set(tree)
        new = set(git("diff", "--name-only", "--no-renames", "--diff-filter=A",
                      f"{base}...HEAD").splitlines())
        for line in git("diff", "--numstat", "--no-renames", f"{base}...HEAD").splitlines():
            added, deleted, path = line.split("\t", 2)
            if path not in present or not in_legacy(path, LEGACY):
                continue
            if path in new:
                errors.append(f"{path}: new file under a LEGACY entry; LEGACY only shrinks")
            elif added == "-" or int(added) > int(deleted):
                errors.append(
                    f"{path}: LEGACY file grows (+{added}/-{deleted}); "
                    "it may shrink or go, and new text belongs in the wiki"
                )
    else:
        print(f"no usable base ({base or 'none given'}): judging HEAD's tree only")

    for error in errors:
        print(error)
    print(f"{len(tree)} files, {len(outside)} outside the areas, "
          f"{len(errors)} finding(s)")
    return 1 if errors else 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main(sys.argv[1:]))
