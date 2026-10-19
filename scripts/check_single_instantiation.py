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
change, or adds the name and says why in the third column of its owner record.
The historical records stay in `single_instantiation_baseline.txt`; new ones
go to `single_instantiation_records/<source-module-subject>.txt`. A strict
reader checks the union for duplicate names and conflicting owners.

The reason used to live in the pull request instead, and that did not hold. A
pull request is not readable from the tree, and `--relax` used to rewrite the
file from scratch, so a regenerated baseline was indistinguishable from a reviewed one.
Between 2026-09-08 and 2026-09-14, 29 names drifted in that way -- against 80
recorded -- while this gate ran only in `scripts/gates.sh` and never in CI. The
reason now lives in each record, `--relax` preserves the reasons already there and
returns nonzero for any name it had to write a `TODO` for, and a `TODO` for a
current thin abstraction fails the gate. `--relax` can record a name; it cannot
bless one. The 80 entries that predate the column carry a visible legacy marker
rather than a silent pass, so the back-fill stays countable.
`--relax` adds records without pruning stale ones; stale-record triage is a
separate review decision.

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
from typing import NamedTuple

from _output import force_utf8_output

ROOT = pathlib.Path(__file__).resolve().parent.parent
BASELINE = ROOT / "scripts" / "single_instantiation_baseline.txt"
RECORDS = ROOT / "scripts" / "single_instantiation_records"

# Subjects that exist in order to be instantiated. `AlgebraicGeometry` is not
# one: a structure there describes a particular geometric situation, and having
# one witness of it is the normal case rather than a smell. A geometric
# realization of a categorical interface lives with the geometric object, under
# `AlgebraicGeometry/`, so no path below a generic subject is geometric.
GENERIC_SUBJECTS = {
    "CategoryTheory", "LinearAlgebra", "Algebra", "Topology", "RingTheory",
    "AlgebraicTopology",
}
THRESHOLD = 1


def subject_of(module: str) -> str:
    parts = module.split(".")
    return parts[1] if len(parts) > 1 else ""


# A third, optional tab-separated column carrying the reason one inhabitant
# is right. Optional only in the parsing: `--relax` writes `TODO` for a name
# that has none and returns nonzero, and the gate rejects a `TODO` that
# reaches a commit. Before this column the reason lived only in the pull
# request, so the next `--relax` erased every one of them and a regenerated
# file could not be told from a reviewed one -- which is how 29 names drifted
# in unnoticed while the gate itself ran only locally.
TODO = "TODO: say why one inhabitant is right"


class BaselineError(ValueError):
    """A record cannot be assigned to one unambiguous subject owner."""


class BaselineRecord(NamedTuple):
    subject: str
    name: str
    reason: str
    path: pathlib.Path
    line: int


def read_baseline(
    legacy: pathlib.Path = BASELINE, shards: pathlib.Path = RECORDS
) -> dict[str, BaselineRecord]:
    """Read the historical records and owner shards without lossy set union."""
    if not legacy.is_file():
        raise BaselineError(f"{legacy} is missing; the exception gate cannot pass")
    paths = [legacy]
    if shards.exists():
        if not shards.is_dir():
            raise BaselineError(f"{shards} is not a directory")
        for path in sorted(shards.iterdir()):
            if path.is_symlink() or not path.is_file() or path.suffix != ".txt":
                raise BaselineError(f"{path}: expected an ordinary .txt owner shard")
            if path.stem not in GENERIC_SUBJECTS:
                raise BaselineError(f"{path}: unknown subject owner {path.stem}")
            paths.append(path)

    records: dict[str, BaselineRecord] = {}
    for path in paths:
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            parts = line.split("\t")
            if len(parts) != 3 or any(not part.strip() for part in parts):
                raise BaselineError(f"{path}:{line_number}: expected subject, name and reason")
            if any(part != part.strip() for part in parts):
                raise BaselineError(f"{path}:{line_number}: surrounding whitespace in a record field")
            subject, name, reason = parts
            if subject not in GENERIC_SUBJECTS:
                raise BaselineError(f"{path}:{line_number}: unknown subject owner {subject}")
            if path != legacy and subject != path.stem:
                raise BaselineError(
                    f"{path}:{line_number}: record owner {subject} conflicts with shard {path.stem}"
                )
            if name in records:
                earlier = records[name]
                raise BaselineError(
                    f"{path}:{line_number}: duplicate {name}; first at "
                    f"{earlier.path}:{earlier.line} (owner {earlier.subject})"
                )
            records[name] = BaselineRecord(subject, name, reason, path, line_number)
    return records


def write_baseline(
    thin: list[str], modules: dict[str, str], records: dict[str, BaselineRecord],
    shards: pathlib.Path = RECORDS,
) -> list[pathlib.Path]:
    """Add new exceptions to owner shards without pruning any existing record."""
    additions: dict[pathlib.Path, list[tuple[str, str]]] = {}
    for name in thin:
        subject = subject_of(modules[name])
        previous = records.get(name)
        if previous and previous.subject != subject:
            raise BaselineError(
                f"{previous.path}:{previous.line}: {name} belongs to module subject "
                f"{subject}, not recorded owner {previous.subject}"
            )
        if previous:
            continue
        path = shards / f"{subject}.txt"
        additions.setdefault(path, []).append((name, f"{subject}\t{name}\t{TODO}\n"))

    touched: list[pathlib.Path] = []
    for path in sorted(additions):
        rows = [
            (record.name, f"{record.subject}\t{record.name}\t{record.reason}\n")
            for record in records.values() if record.path == path
        ]
        rows.extend(additions[path])
        content = "".join(row for _, row in sorted(rows))
        if not path.exists() or path.read_text(encoding="utf-8") != content:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")
            touched.append(path)
    return touched


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

    try:
        records = read_baseline(BASELINE, RECORDS)
        for name, previous in records.items():
            module = modules.get(name)
            if module and previous.subject != subject_of(module):
                raise BaselineError(
                    f"{previous.path}:{previous.line}: {name} belongs to module subject "
                    f"{subject_of(module)}, not recorded owner {previous.subject}"
                )
    except (BaselineError, OSError, UnicodeError) as error:
        print(f"::error::single-instantiation records: {error}")
        return 1

    if relax:
        missing = [n for n in thin if n not in records or records[n].reason == TODO]
        touched = write_baseline(thin, modules, records, RECORDS)
        for path in touched:
            action = "wrote" if path.exists() else "removed"
            shown = path.relative_to(ROOT) if path.is_relative_to(ROOT) else path
            print(f"{action} {shown}")
        if not touched:
            print("single-instantiation records unchanged")
        if missing:
            print()
            print(f"{len(missing)} of them have no reason, written as `{TODO}`:")
            for name in missing:
                print(
                    f"  - {name} ({modules[name]}) has "
                    f"{counts[name]} inhabitant(s)"
                )
            print()
            print(
                "Replace each placeholder with the reason one inhabitant is "
                "right, in the third tab-separated column. Until then this "
                "gate stays red: `--relax` can record a name but it cannot "
                "bless one, which is the whole point of the file."
            )
            return 1
        return 0

    baseline = set(records)
    new = [n for n in thin if n not in records]

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
            "an owner shard with --relax and say in the pull request why one "
            "is right."
        )
        return 1

    unexplained = sorted(
        n for n in thin if n in records and records[n].reason == TODO
    )
    if unexplained:
        print("single-instantiation gate failed:")
        for name in unexplained:
            print(f"  - {name} ({modules[name]}) is recorded with no reason")
        print()
        print(
            "A baseline entry still reading the placeholder is a name "
            "recorded without anyone saying why one inhabitant is right. "
            "That is the drift this file exists to make visible, so it "
            "fails here rather than passing quietly."
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
            f"{THRESHOLD}; review and remove them separately. "
            "`--relax` does not prune records."
        )
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
