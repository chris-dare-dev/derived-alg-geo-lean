#!/usr/bin/env python3
"""Reject every source-level dependency on the retired stability-code source.

This is intentionally a repository-wide zero-import gate.  It has no
allowlist: the retired module root and the two former bridge roots may not be
imported by any tracked Lean source.  It also rejects restoration of the
deleted source/bridge paths or the two exact copied helper files that were
replaced by owner-native proofs.

"Repository-wide" means *this* checkout.  The walk stops at any nested
checkout, because those files are another working tree's, not this one's.
"""

from __future__ import annotations

import os
import pathlib
import re
import sys
from typing import Iterator

from _output import force_utf8_output


ROOT = pathlib.Path(__file__).resolve().parent.parent
# Lean's module system prefixes imports with `public`, `private`, or `meta`,
# and `import all` re-exports; a plain `^import` regex missed every one of
# those forms (2026-08-18 adversarial review, finding P2-2).
IMPORT = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)"
)
SKIP_DIRS = (".lake", ".git", ".claude")
FORBIDDEN_MODULE_ROOTS = (
    "BridgelandStability",
    "BridgelandStabLean",
    "CohLean",
    "DGLean",
)
FORBIDDEN_PATHS = (
    ROOT / "vendor" / "BridgelandStability",
    ROOT / "BridgelandStabLean",
    ROOT / "BridgelandStabLean.lean",
    ROOT / "CohLean",
    ROOT / "CohLean.lean",
    ROOT / "DGLean",
    ROOT / "DGLean.lean",
    ROOT
    / "DerivedAlgGeo"
    / "CategoryTheory"
    / "ObjectProperty"
    / "FullSubcategory.lean",
    ROOT
    / "DerivedAlgGeo"
    / "CategoryTheory"
    / "Triangulated"
    / "TStructure"
    / "HeartAbelian.lean",
)


def is_forbidden_module(module: str) -> bool:
    return any(
        module == root or module.startswith(root + ".")
        for root in FORBIDDEN_MODULE_ROOTS
    )


def lean_sources(
    root: pathlib.Path, unexpected_checkouts: list[pathlib.Path]
) -> Iterator[pathlib.Path]:
    """Yield this checkout's Lean sources, skipping build output.

    Local working trees live under `.claude/worktrees/`, and a worktree of any
    pre-#372 branch still holds the retired `CohLean/` and `DGLean/` layouts.
    Those are a different checkout's tracked files, so counting them makes this
    gate -- and therefore `scripts/gates.sh` -- permanently red in any clone
    that has one, while CI stays green because CI checks out clean. A gate that
    only ever fails locally teaches people to ignore it; `.claude` is therefore
    in SKIP_DIRS wholesale.

    A nested `.git` entry anywhere ELSE is no longer silently pruned: silent
    pruning meant a directory with a stub `.git` file hid a live copy from the
    import scan entirely (2026-08-18 adversarial review, finding P2-2). Such a
    directory is now recorded and the caller fails the gate naming it.
    """
    for dirpath, dirnames, filenames in os.walk(root):
        here = pathlib.Path(dirpath)
        kept: list[str] = []
        for name in sorted(dirnames):
            if name in SKIP_DIRS:
                continue
            if (here / name / ".git").exists():
                unexpected_checkouts.append(here / name)
                continue
            kept.append(name)
        dirnames[:] = kept
        for name in sorted(filenames):
            if name.endswith(".lean"):
                yield here / name


def main() -> int:
    failures: list[str] = []

    for path in FORBIDDEN_PATHS:
        if path.exists():
            failures.append(f"retired path exists: {path.relative_to(ROOT)}")

    unexpected_checkouts: list[pathlib.Path] = []
    lean_files = list(lean_sources(ROOT, unexpected_checkouts))
    for checkout in unexpected_checkouts:
        failures.append(
            f"unexpected nested checkout: {checkout.relative_to(ROOT)} "
            "(a `.git` entry outside .lake/.claude hides its files from this "
            "gate; remove it or move it under .claude/worktrees/)"
        )
    if not lean_files:
        failures.append("no Lean sources found; run the gate from a repository checkout")

    for path in lean_files:
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            match = IMPORT.match(line)
            if match and is_forbidden_module(match.group(1)):
                failures.append(
                    f"{path.relative_to(ROOT)}:{line_number}: forbidden import "
                    f"{match.group(1)}"
                )

    lakefile = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    if re.search(r"(?m)^\s*\[\[lean_lib\]\]\s*$[\s\S]*?^\s*name\s*=\s*"
                 r"[\"']BridgelandStability[\"']", lakefile):
        failures.append("lakefile.toml declares the retired external library root")
    # A `[[require]]` fetching the retired upstream is a live Lake dependency
    # even with no library root named after it; and configuration in a
    # `lakefile.lean` would escape this textual audit entirely.
    if re.search(r"(?i)mattrobball", lakefile):
        failures.append("lakefile.toml references the retired upstream repository")
    for req in re.finditer(
        r"(?m)^\s*\[\[require\]\]\s*$[\s\S]*?^\s*name\s*=\s*[\"']([^\"']+)[\"']",
        lakefile,
    ):
        if req.group(1) in FORBIDDEN_MODULE_ROOTS:
            failures.append(
                f"lakefile.toml requires the retired dependency {req.group(1)}"
            )
    if (ROOT / "lakefile.lean").exists():
        failures.append(
            "lakefile.lean exists; this gate audits lakefile.toml only, so a "
            "Lean-format lakefile is an unaudited dependency channel"
        )

    if failures:
        print("source-independence gate failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    print(
        f"ok: {len(lean_files)} Lean sources have zero imports from retired "
        "source and bridge roots"
    )
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
