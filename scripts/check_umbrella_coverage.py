#!/usr/bin/env python3
"""Assert every umbrella re-exports its whole directory.

An umbrella that omits a leaf drops that module from the build graph, and
nothing else notices: the leaf still compiles when something imports it
directly, the audits never see declarations they were never handed, and the
emission sweep measures the modules that were built rather than the ones that
exist. The failure is silent in every direction.

It is not hypothetical. Two changes in one day nearly caused it. One replaced a
flat leaf-import block in `Foundation.lean` with two sub-umbrellas while another
added a new leaf to the block being deleted; resolving that conflict by taking
the umbrella side alone would have dropped `StabilityFunction.SlopeThreshold`
with no error anywhere. The other generated an umbrella from a directory
listing, after which a leaf added upstream was simply absent.

## Umbrella, or module that shares a name with a directory?

`Foundation/Slicing.lean` sits beside `Foundation/Slicing/` and imports none of
its seventeen files. That is correct: it *declares* `Slicing` and `HNFiltration`,
and the directory holds theorems about them. Requiring it to re-export its
children would invert the dependency and create a cycle.

So the rule keys on content, not on position: a file that declares nothing and
has a directory of its own name is an umbrella, and must cover it. A file that
declares something is a module, and is left alone.

Explicit abstraction boundaries keep a generic umbrella from re-exporting a
stronger child or an opt-in geometric instance umbrella. The subject-layering
gate checks the import direction at those boundaries. Keeping every exception
as an exact umbrella/child pair prevents it from weakening coverage anywhere
else.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE_ROOT = ROOT / "DerivedAlgGeo"
IMPORT = re.compile(r"^\s*import\s+(\S+)")
# Anything that introduces a name. `example` deliberately does not.
DECLARES = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|scoped\s+)*"
    r"(def|theorem|lemma|abbrev|structure|class|inductive|instance|axiom|opaque)\b"
)
EXPLICIT_CHILD_BOUNDARIES = {
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition": {
        "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
        "StabilityCondition",
    },
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families": {
        "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
        "Families.Instances",
    },
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Families": {
        "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
        "StabilityCondition.Families.Instances",
    },
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Symmetry.Autoequivalence": {
        "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
        "StabilityCondition.Symmetry.Autoequivalence.Instances",
    },
}


def module_name(path: pathlib.Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def declares_something(path: pathlib.Path) -> bool:
    for line in path.read_text(encoding="utf-8").splitlines():
        if DECLARES.match(line):
            return True
    return False


def imports_of(path: pathlib.Path) -> set[str]:
    found: set[str] = set()
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT.match(line)
        if match is not None:
            found.add(match.group(1))
    return found


def main() -> int:
    failures: list[str] = []
    checked = 0

    for directory in sorted(p for p in SOURCE_ROOT.rglob("*") if p.is_dir()):
        umbrella = directory.with_suffix(".lean")
        if not umbrella.exists():
            continue
        if declares_something(umbrella):
            # A module that shares a name with a directory of its consequences.
            continue

        checked += 1
        declared = imports_of(umbrella)
        omitted_children = EXPLICIT_CHILD_BOUNDARIES.get(
            module_name(umbrella), set()
        )
        # Direct children only: a nested directory is covered by its own
        # umbrella, which this check reaches on its own pass.
        # A child `X.lean` beside a directory `X/` is reached by both loops
        # below; report it once.
        seen: set[str] = set()
        for child in sorted(directory.glob("*.lean")):
            name = module_name(child)
            if name in omitted_children:
                continue
            if name not in declared and name not in seen:
                seen.add(name)
                failures.append(
                    f"{umbrella.relative_to(ROOT)}: does not re-export "
                    f"{child.relative_to(ROOT)}"
                )
        for sub in sorted(p for p in directory.iterdir() if p.is_dir()):
            sub_umbrella = sub.with_suffix(".lean")
            sub_name = module_name(sub_umbrella) if sub_umbrella.exists() else None
            if sub_name in omitted_children:
                continue
            if sub_name is not None and sub_name not in declared and sub_name not in seen:
                seen.add(sub_name)
                failures.append(
                    f"{umbrella.relative_to(ROOT)}: does not re-export "
                    f"{sub_umbrella.relative_to(ROOT)}"
                )

    if failures:
        print("umbrella coverage gate failed:")
        for failure in failures:
            print(f"  - {failure}")
        print()
        print(
            "An umbrella that omits a leaf drops it from the build graph "
            "silently. Add the import, or -- if the file is a module that "
            "shares a name with a directory rather than an umbrella of it -- "
            "nothing is wrong and this check already skips it."
        )
        return 1

    print(f"ok: {checked} umbrella(s) re-export their whole directory")
    return 0


if __name__ == "__main__":
    sys.exit(main())
