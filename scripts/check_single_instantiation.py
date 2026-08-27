#!/usr/bin/env python3
"""Fail when a NEW generic abstraction ships with at most one inhabitant.

The disease this catches, in the shape it actually occurs: someone correctly
identifies that N things share a structure and writes the general definition;
instantiates it once, at the case in front of them; and never migrates the other
N-1. The abstraction then sits at zero adoption while the duplicates it was
meant to absorb keep accruing, and nothing anywhere notices.

Three instances of it are on the record. `GrothendieckPresentation` was generic
in its generator and relation types and instantiated once, at distinguished
triangles, until #760. `ClassDatum` was introduced by #764 to serve two
theories, said so in its own docstring, and shipped with one instantiation until
#784. `Enhancement` still has one, which is correct -- see below.

## Why a baseline rather than a rule

Because "one inhabitant" is not by itself wrong. Of 117 structures and classes
in the generic subjects, 53 have at most one: statement layers with no intended
inhabitant, data structures a consumer supplies from outside the repository,
and abstractions whose second instantiation is genuinely future work. A gate
failing on all of them fires on 45% of the tree and stops being read.

So this follows `audit_missing_baseline.txt`: the known ones are named, and only
a NEW name fails. That converts the failure mode from invisible drift into a
deliberate, reviewable act -- the author either instantiates it twice in the same
change, or adds the name and says why in the pull request.

## What counts as an inhabitant

`scripts/EnumInhabitants.lean` decides, from the elaborated environment: a
declaration whose type, after stripping every leading binder, has the structure
as the head of its conclusion. That distinguishes a producer from a consumer,
which no amount of grepping over source can do -- the first attempt at this
counted `def IsPositive (D : ClassDatum O G) : Prop` as an instantiation of
`ClassDatum`.
"""

from __future__ import annotations

import collections
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
BASELINE = ROOT / "scripts" / "single_instantiation_baseline.txt"

# Subjects that exist in order to be instantiated. `AlgebraicGeometry` is not
# one: a structure there describes a particular geometric situation, and having
# one witness of it is the normal case rather than a smell.
GENERIC_SUBJECTS = {"CategoryTheory", "LinearAlgebra", "Algebra", "Topology"}
THRESHOLD = 1


def subject_of(module: str) -> str:
    parts = module.split(".")
    return parts[1] if len(parts) > 1 else ""


def main() -> int:
    relax = "--relax" in sys.argv
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not args:
        print("usage: check_single_instantiation.py <enum-inhabitants.txt> [--relax]")
        return 2
    sweep = pathlib.Path(args[0])
    if not sweep.exists():
        print(f"::error::{sweep} is missing; run `lake env lean scripts/EnumInhabitants.lean`")
        return 1

    modules: dict[str, str] = {}
    counts: collections.Counter[str] = collections.Counter()
    for line in sweep.read_text(encoding="utf-8").splitlines():
        parts = line.split("\t")
        if parts[0] == "structure" and len(parts) == 3:
            modules[parts[2]] = parts[1]
        elif parts[0] == "inhabitant" and len(parts) == 3:
            counts[parts[1]] += 1

    thin = sorted(
        name
        for name, module in modules.items()
        if subject_of(module) in GENERIC_SUBJECTS and counts[name] <= THRESHOLD
    )

    if relax:
        BASELINE.write_text(
            "".join(f"{subject_of(modules[n])}\t{n}\n" for n in thin), encoding="utf-8"
        )
        print(f"wrote {BASELINE.relative_to(ROOT)} ({len(thin)} entries)")
        return 0

    if not BASELINE.exists():
        print(f"::error::{BASELINE.relative_to(ROOT)} is missing; regenerate it with --relax")
        return 1

    baseline = {
        line.split("\t")[1]
        for line in BASELINE.read_text(encoding="utf-8").splitlines()
        if "\t" in line
    }
    new = [n for n in thin if n not in baseline]

    if new:
        print("single-instantiation gate failed:")
        for name in new:
            print(
                f"  - {name} ({modules[name]}) has {counts[name]} inhabitant(s)"
            )
        print()
        print(
            "A generic abstraction with at most one inhabitant is the shape that "
            "produced `GrothendieckPresentation` and `ClassDatum`: written for N "
            "cases, instantiated once, never adopted. Either instantiate it a "
            "second time in this change, or add it to "
            f"{BASELINE.relative_to(ROOT)} with --relax and say in the pull "
            "request why one is right."
        )
        return 1

    stale = sorted(baseline - set(thin))
    print(
        f"ok: {len(thin)} generic abstraction(s) at or below {THRESHOLD} "
        f"inhabitant(s), all known"
    )
    if stale:
        print(
            f"note: {len(stale)} baseline entry/entries now have more than "
            f"{THRESHOLD}; `--relax` to drop them and lower the figure."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
