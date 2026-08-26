#!/usr/bin/env python3
"""Fail when a subsystem audit falls behind the source in the *other* direction.

`check_audit.py` compares the records a run printed against the commands in the
audit file. So a listed name that disappears breaks the build loudly, and a new
public declaration that nobody listed is invisible. `StabilityConditionAudit.lean`
documents that asymmetry about itself; this script is the missing half.

PR #354 is what it would have caught: 32 new public declarations, none
registered, including `DGFunctor.IsQuasiEquivalence` — the milestone's headline
result. A reviewer had to notice an absence.

Usage:
    lake env lean scripts/EnumDecls.lean > /tmp/enum-decls.txt
    python3 scripts/check_audit_complete.py /tmp/enum-decls.txt
    python3 scripts/check_audit_complete.py /tmp/enum-decls.txt --relax

## Why this is a ratchet and not a hard gate

Measured 2026-08-14, the algebraic-geometry audit listed 1024 of its 2118
public declarations and the stability-condition audit 2253 of 2634. Those gaps
predate this script by a long way
and cannot be closed in the change that introduces it, so the ceilings below
record where things stand and the gate fails only when a library gets *worse*.
The dg-category audit sits at zero because it was gated from its first commit, and its
ceiling of 0 is the one that matters: it keeps a complete audit complete.

## Why the counts are close rather than exact

Audit files `open` their own namespace, so a record may be written unqualified
(`Lattice.NumLattice` for a declaration in the integral-lattice namespace). Resolving
that properly means resolving names the way Lean would; this script instead
tries a small list of prefixes per library. A handful of records still fail to
resolve — they are reported, not silently dropped, and they are the reason a
count here is trustworthy for *direction* but not to the last unit.
"""

from __future__ import annotations

import sys
from pathlib import Path

# Prefixes an audit file's `open` lines make available, per library.
AUDITS = {
    "AlgebraicGeometry": (
        "scripts/AlgebraicGeometryAudit.lean",
        ["AlgebraicGeometry.", "AlgebraicGeometry.Numerical."],
    ),
    "StabilityCondition": (
        "scripts/StabilityConditionAudit.lean",
        ["CategoryTheory.Triangulated.",
         "CategoryTheory.Triangulated.StabilityCondition."],
    ),
    # `DGCategory.` until 2026-08-15. #374 moved every declaration into
    # `CategoryTheory`, which left that prefix naming a namespace that no longer
    # exists. It never failed a build, because the resolver tries the bare name
    # first and every record in this audit is fully qualified -- so the prefixes
    # are dead weight until someone writes an unqualified record, which is normal
    # practice in the other two audits and would then silently fail to resolve.
    "DGCategory": (
        "scripts/DGCategoryAudit.lean",
        ["CategoryTheory.", "CategoryTheory.DGCategory."],
    ),
}

# Public declarations absent from each audit, as measured 2026-08-14. Lower these
# whenever the real figure drops -- `--relax` prints the new values. Never raise
# one: a change that leaves more declarations unaudited than it found is the
# thing this gate exists to stop.
CEILINGS = {
    "AlgebraicGeometry": 1059,
    "StabilityCondition": 305,
    "DGCategory": 0,
}

# The identity half of the ratchet. Ceilings alone admit a swap: a new
# unaudited declaration passes when the same change audits one old backlog
# entry, count unchanged (2026-08-18 adversarial review, finding P2-8). This
# file enumerates the known backlog by name; a missing declaration that is not
# in it is NEW and must be added to its audit, never to the baseline by hand.
# `--relax` rewrites it (and prints the ceilings) after a deliberate change.
BASELINE = Path("scripts/audit_missing_baseline.txt")


def load_env(path: Path) -> dict[str, set[str]]:
    env: dict[str, set[str]] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if "\t" not in line:
            continue
        lib, name = line.split("\t", 1)
        env.setdefault(lib, set()).add(name)
    return env


def listed_names(path: Path) -> set[str]:
    # Since #480 an audit may be split into `<stem>/*.lean` area files behind
    # an imports-only umbrella; read the umbrella plus every area file. For an
    # unsplit audit the glob is empty and this reads the one file, as before.
    files = [path] + sorted((path.parent / path.stem).glob("*.lean"))
    return {
        line.split()[-1]
        for f in files
        for line in f.read_text(encoding="utf-8").splitlines()
        if line.startswith("#print axioms")
    }


def main(argv: list[str]) -> int:
    args = [a for a in argv if not a.startswith("-")]
    if not args:
        print(__doc__, file=sys.stderr)
        return 1
    enum = Path(args[0])
    if not enum.exists():
        print(f"::error::{enum} not found; run `lake env lean scripts/EnumDecls.lean` first")
        return 1

    env = load_env(enum)
    if not env:
        # A sweep that found nothing would pass every check below. That is the
        # vacuous pass the audits exist to make impossible.
        print("::error::the declaration sweep is empty -- EnumDecls.lean produced no rows")
        return 1

    relax = "--relax" in argv
    failed = False
    new_ceilings: dict[str, int] = {}
    baseline: set[tuple[str, str]] = set()
    baseline_rows: list[str] = []
    if BASELINE.exists():
        baseline = {
            tuple(line.split("\t", 1))
            for line in BASELINE.read_text(encoding="utf-8").splitlines()
            if "\t" in line
        }
    elif not relax:
        # Fail closed: without the baseline the identity check below is
        # vacuous, which is the exact pass this gate exists to prevent.
        print(f"::error::{BASELINE} is missing; regenerate it with --relax")
        failed = True

    # Modules under the source root that `EnumDecls.libraryOf` classifies into
    # no audit bucket. Before #508 these were silently invisible to the sweep,
    # which made this gate pass vacuously for any new source directory; now
    # the sweep emits them under a sentinel and any occurrence is a failure,
    # named per module so the fix (a new branch in `libraryOf`) is actionable.
    unclassified = env.pop("Unclassified", set())
    if unclassified:
        failed = True
        print(f"::error::{len(unclassified)} module(s) under DerivedAlgGeo are "
              "not classified by EnumDecls.libraryOf, so their declarations "
              "are invisible to every audit. Add their directory to "
              "libraryOf in scripts/EnumDecls.lean (see #508):")
        for m in sorted(unclassified):
            print(f"    {m}")

    for lib, (audit_path, prefixes) in AUDITS.items():
        declared = env.get(lib, set())
        if not declared:
            # The same vacuous pass the global check above rejects, one level
            # down: with no declarations for this library, `missing` is empty and
            # the ceiling is met no matter what the audit says. It means the sweep
            # did not reach the library, or `EnumDecls.libraryOf` stopped
            # classifying its modules -- a new source root under an existing one
            # is the way that happens. Either way this gate is not measuring it.
            print(f"::error::{lib} contributed no declarations to the sweep; the "
                  "ceiling below would be met vacuously. Check that "
                  "EnumDecls.lean imports it and that libraryOf classifies its "
                  "modules.")
            failed = True
            continue
        raw = listed_names(Path(audit_path))

        resolved: set[str] = set()
        unresolved: set[str] = set()
        for n in raw:
            hit = next((c for c in [n] + [p + n for p in prefixes] if c in declared), None)
            if hit:
                resolved.add(hit)
            else:
                unresolved.add(n)

        missing = declared - resolved
        ceiling = CEILINGS[lib]
        new_ceilings[lib] = len(missing)
        baseline_rows.extend(f"{lib}\t{n}" for n in sorted(missing))

        note = f" ({len(unresolved)} records unresolved)" if unresolved else ""
        print(f"{lib:<20} {len(declared):>5} public, {len(resolved):>5} audited, "
              f"{len(missing):>5} missing (ceiling {ceiling}){note}")

        if len(missing) > ceiling:
            failed = True
            print(f"::error::{lib} left {len(missing) - ceiling} more declaration(s) "
                  "unaudited than the recorded ceiling. Add them to "
                  f"{audit_path} -- see CONTRIBUTING.md.")
            for n in sorted(missing)[:15]:
                print(f"    {n}")
        elif len(missing) < ceiling:
            print(f"  note: {lib} improved by {ceiling - len(missing)}; "
                  "run with --relax and lower the ceiling.")

        if not relax and baseline:
            new_names = sorted(n for n in missing if (lib, n) not in baseline)
            if new_names:
                failed = True
                print(f"::error::{lib} has {len(new_names)} NEW unaudited public "
                      f"declaration(s) absent from {BASELINE}. Add them to "
                      f"{audit_path}; do not extend the baseline by hand.")
                for n in new_names[:15]:
                    print(f"    {n}")

    if relax:
        BASELINE.write_text(
            "\n".join(sorted(baseline_rows)) + "\n", encoding="utf-8")
        print(f"\nwrote {BASELINE} ({len(baseline_rows)} entries)")
        print("CEILINGS = {")
        for lib, n in new_ceilings.items():
            print(f'    "{lib}": {n},')
        print("}")
        return 0

    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
