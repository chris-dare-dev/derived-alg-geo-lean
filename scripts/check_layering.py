#!/usr/bin/env python3
"""Invariant: the library's import graph has none of the edges this file forbids.

Mathlib's subjects interleave, so there is no rank order to check and Lean
already rejects cycles. What is left is a short table of directory edges the
layout promises, checked over the transitive import graph that Lean's own
header parser reports.

A rule names paths below `DerivedAlgGeo/`: `X/Y/` is that directory together
with its same-named umbrella `X/Y.lean`, and `X/Y.lean` is one file.
`Mathlib/...` names Mathlib modules, seen where a library module imports one;
the graph does not follow Mathlib's own imports. A path a rule names must
exist, so a move that renames it updates the rule instead of emptying it.
"""

from __future__ import annotations

import graphlib
import json
import pathlib
import subprocess
import sys

from _output import force_utf8_output

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIBRARY = "DerivedAlgGeo"

#: The directories directly below `DerivedAlgGeo/`. A new one is a decision,
#: made by adding it here.
SUBJECTS = {
    "Algebra", "AlgebraicGeometry", "AlgebraicTopology", "Analysis",
    "CategoryTheory", "Development", "LinearAlgebra", "RingTheory", "Topology",
}

STABILITY = "CategoryTheory/Triangulated/StabilityCondition/"

#: Each protected tree is reached only from itself, from the listed sources,
#: and from the umbrellas above either.
REACHED_ONLY_FROM = {
    # Everything outside geometry is usable without schemes.
    ("AlgebraicGeometry/", "Mathlib/AlgebraicGeometry/"): ("Development/",),
    # No stable module imports a probe.
    ("Development/",): (),
    # Stability conditions have a closed list of consumers, so `Dᵇ(Coh X)`,
    # sheaves, stacks, cohomology and the neutral algebra beneath them import
    # without Bridgeland stability.
    (STABILITY,): (
        "AlgebraicGeometry/DerivedCategory/Stability/",
        "AlgebraicGeometry/Moduli/HarderNarasimhan/",
        "AlgebraicGeometry/Moduli/Semistability/",
        "AlgebraicGeometry/Numerical/Examples/Fourfold/",
        "AlgebraicGeometry/Numerical/Examples/Surface/",
        "AlgebraicGeometry/Numerical/Examples/Threefold/",
        "AlgebraicGeometry/Numerical/GrothendieckGroup/CategoricalChargeK3.lean",
        "AlgebraicGeometry/Numerical/GrothendieckGroup/CentralChargeK3.lean",
        "AlgebraicGeometry/Numerical/Stability/",
        "CategoryTheory/Triangulated/SphericalTwist/Autoequivalence.lean",
        "CategoryTheory/Triangulated/SphericalTwist/StabilityAction.lean",
        "Development/",
    ),
    # A demonstration is a leaf: models, transport and charges never import one.
    ("AlgebraicGeometry/Numerical/Examples/",): (),
}

#: Nothing below a source reaches a target outside that source.
NEVER_REACHES = (
    # Weak stability is the parent of Bridgeland stability, not its consumer.
    (f"{STABILITY}Weak/", STABILITY),
    # Charges are constructed before walls are drawn with them.
    (f"{STABILITY}CentralCharge/", f"{STABILITY}Walls/"),
    # The arbitrary-divisor-rank charge is a sibling of the H-degree compression.
    (f"{STABILITY}CentralCharge/Exponential/Divisorial.lean",
     f"{STABILITY}CentralCharge/Exponential/Comparison.lean"),
    (f"{STABILITY}CentralCharge/Exponential/Divisorial.lean",
     f"{STABILITY}CentralCharge/Numerical/"),
    # Abelian stability and linear Serre duality need no shift.
    ("CategoryTheory/Abelian/", "CategoryTheory/Triangulated/"),
    ("CategoryTheory/Linear/", "CategoryTheory/Triangulated/"),
    # Planar convex geometry needs no category.
    ("Analysis/", "CategoryTheory/"),
    # Intrinsic dg H0 theory is stated before a category is chosen to compare.
    ("Algebra/Homology/DGCategory/", "CategoryTheory/Triangulated/DGEnhancement/"),
    ("Algebra/Homology/DGCategory/",
     "Algebra/Homology/HomotopyCategory/DGEnhancement/"),
    # The neutral derived-category umbrella omits its stability child.
    ("AlgebraicGeometry/DerivedCategory.lean", STABILITY),
    # Derived tensor and pushforward are not about transforms.
    *(
        (source, target)
        for source in (
            "AlgebraicGeometry/DerivedCategory/Tensor/",
            "AlgebraicGeometry/DerivedCategory/Families/DerivedPushforward.lean",
            "AlgebraicGeometry/DerivedCategory/TwistedPushforward.lean",
        )
        for target in (
            "AlgebraicGeometry/DerivedCategory/FourierMukai/",
            "CategoryTheory/Triangulated/FourierMukai/",
        )
    ),
    # Flatness and perfection are properties of one complex, not of a moduli problem.
    ("AlgebraicGeometry/DerivedCategory/Perfect/", "AlgebraicGeometry/Moduli/"),
    ("AlgebraicGeometry/Modules/Flat.lean", "AlgebraicGeometry/Moduli/"),
    # Slope and Gieseker stability are siblings; `Comparison.lean` sees both.
    ("AlgebraicGeometry/Stability/Slope/", "AlgebraicGeometry/Stability/Gieseker/"),
    ("AlgebraicGeometry/Stability/Gieseker/", "AlgebraicGeometry/Stability/Slope/"),
    # Moduli problems instantiate stacks, not the reverse.
    ("AlgebraicGeometry/Sites/", "AlgebraicGeometry/Moduli/"),
    ("AlgebraicGeometry/Stacks/", "AlgebraicGeometry/Moduli/"),
)


def module(path: str) -> str:
    """`X/Y/` and `X/Y.lean` both name the module `DerivedAlgGeo.X.Y`."""
    name = path.removesuffix("/").removesuffix(".lean").replace("/", ".")
    return name if name.startswith("Mathlib.") else f"{LIBRARY}.{name}"


def covers(path: str, name: str) -> bool:
    root = module(path)
    return name == root or (path.endswith("/") and name.startswith(root + "."))


def import_graph() -> dict[str, list[str]]:
    files = subprocess.run(
        ["git", "ls-files", "--", f"{LIBRARY}/*.lean", f"{LIBRARY}.lean",
         f"{LIBRARY}Sweep.lean"],
        cwd=ROOT, capture_output=True, text=True, check=True,
    ).stdout.split()
    parsed = subprocess.run(
        ["lean", "--deps-json", "--stdin"], cwd=ROOT, input="\n".join(files),
        capture_output=True, text=True, check=True,
    )
    graph = {}
    for file, entry in zip(files, json.loads(parsed.stdout)["imports"], strict=True):
        if entry["errors"]:
            sys.exit(f"{file}: {entry['errors']}")
        name = file.removesuffix(".lean").replace("/", ".")
        graph[name] = [i["module"] for i in entry["result"]["imports"]]
    return graph


def rules():
    """Both tables as `(checked, banned, why)`: a checked module reaches nothing banned."""
    roots = (LIBRARY, f"{LIBRARY}Sweep")
    for targets, allowed in REACHED_ONLY_FROM.items():
        exempt = (*targets, *allowed)
        yield (
            lambda m, exempt=exempt: m not in roots and not any(
                covers(p, m) or module(p).startswith(m + ".") for p in exempt
            ),
            lambda d, targets=targets: any(covers(t, d) for t in targets),
            f"{targets[0]} is reached only from what REACHED_ONLY_FROM lists",
        )
    for source, target in NEVER_REACHES:
        yield (
            lambda m, source=source: covers(source, m),
            lambda d, source=source, target=target: covers(target, d)
            and not covers(source, d),
            f"{source} never reaches {target}",
        )


def main() -> int:
    graph = import_graph()
    reach: dict[str, set[str]] = {}
    try:
        order = list(graphlib.TopologicalSorter(graph).static_order())
    except graphlib.CycleError as cycle:
        print("import cycle:", " -> ".join(cycle.args[1]))
        return 1
    for name in order:
        reach[name] = set(graph.get(name, ()))
        for dep in graph.get(name, ()):
            reach[name] |= reach.get(dep, set())

    failures = [
        f"DerivedAlgGeo/{entry.name}/ is not in SUBJECTS"
        for entry in (ROOT / LIBRARY).iterdir()
        if entry.is_dir() and entry.name not in SUBJECTS
    ]
    named = {*REACHED_ONLY_FROM, *REACHED_ONLY_FROM.values(), *NEVER_REACHES}
    failures += [
        f"{path} is named by a rule and does not exist"
        for path in sorted({p for group in named for p in group})
        if not path.startswith("Mathlib/") and not any(covers(path, m) for m in graph)
    ]
    for checked, banned, why in rules():
        bad = {m for m in graph if checked(m) and any(map(banned, reach[m]))}
        for name in sorted(graph):
            if not checked(name):
                continue
            # Report the module that introduces the edge, not every importer of it.
            for dep in graph[name]:
                if banned(dep):
                    failures.append(f"{name} imports {dep}: {why}")
                elif dep not in bad and any(map(banned, reach.get(dep, ()))):
                    failures.append(
                        f"{name} imports {dep}, which reaches "
                        f"{min(filter(banned, reach[dep]))}: {why}"
                    )

    if failures:
        print("layering failed:", *failures, sep="\n  ")
        return 1
    print(f"ok: {len(graph)} modules, {len(REACHED_ONLY_FROM) + len(NEVER_REACHES)} rules")
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
