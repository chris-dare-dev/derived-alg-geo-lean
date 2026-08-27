#!/usr/bin/env python3
"""Check the repository's subject-level dependency direction.

An acyclic Lean module graph can still hide a cycle after modules are grouped
by their declared owners. This gate collapses imports to the top-level subject
directories, rejects cycles in that graph, and enforces the CategoryTheory /
AlgebraicGeometry ownership boundary introduced by issue #601.
"""

from __future__ import annotations

from collections import defaultdict
import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE_ROOT = ROOT / "DerivedAlgGeo"
IMPORT = re.compile(r"^\s*import\s+(\S+)")
GENERIC_OWNER = "CategoryTheory"
GEOMETRY_OWNER = "AlgebraicGeometry"

# Higher layers may import lower layers. Equal-rank support subjects may import
# one another provided the observed graph remains acyclic.
LAYER = {
    "Algebra": 0,
    "LinearAlgebra": 0,
    "Topology": 0,
    GENERIC_OWNER: 1,
    GEOMETRY_OWNER: 2,
    "Compatibility": 3,
    "Development": 4,
}

GEOMETRY_FAMILY_MODULES = {
    "BoundedGeometry",
    "DerivedPullbackCoherence",
    "DerivedPullbackLaws",
    "DerivedPullbackShift",
    "DerivedTensorCoherence",
    "Dqc",
    "ExactPullback",
    "ExactPullbackCoherence",
    "FiniteTypeGeometry",
    "FlatPullback",
    "FlatPullbackResolution",
    "GeometricBaseChange",
    "InducingPullback",
    "KernelAssociativity",
    "KernelConvolution",
    "KernelCorrespondence",
    "KernelUnit",
    "KernelUnitConvolution",
    "LeftDerivedPullback",
    "OpenImmersionPullback",
    "PullbackAcyclicResolution",
    "RelativeHN",
    "ResidueFiber",
    "Scheme",
    "SchemeDerived",
    "SchemeSemistableLocus",
}


def owner(path: pathlib.Path) -> str:
    relative = path.relative_to(SOURCE_ROOT)
    return relative.parts[0] if len(relative.parts) > 1 else relative.stem


def find_cycle(graph: dict[str, set[str]]) -> list[str] | None:
    visited: set[str] = set()
    active: set[str] = set()
    stack: list[str] = []

    def visit(node: str) -> list[str] | None:
        visited.add(node)
        active.add(node)
        stack.append(node)
        for dependency in sorted(graph.get(node, set())):
            if dependency not in visited:
                cycle = visit(dependency)
                if cycle is not None:
                    return cycle
            elif dependency in active:
                start = stack.index(dependency)
                return stack[start:] + [dependency]
        stack.pop()
        active.remove(node)
        return None

    for node in sorted(graph):
        if node not in visited:
            cycle = visit(node)
            if cycle is not None:
                return cycle
    return None


def main() -> int:
    subjects = {
        path.name for path in SOURCE_ROOT.iterdir() if path.is_dir()
    }
    graph: dict[str, set[str]] = defaultdict(set)
    evidence: dict[tuple[str, str], list[str]] = defaultdict(list)
    failures: list[str] = []

    for subject in sorted(subjects - LAYER.keys()):
        failures.append(f"subject has no declared layer: {subject}")

    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        source_owner = owner(path)
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = IMPORT.match(line)
            if match is None:
                continue
            module = match.group(1)
            # Any subject ranked BELOW the geometry owner must stay clear of
            # Mathlib's geometry. This used to test `source_owner ==
            # GENERIC_OWNER`, which checked `CategoryTheory` and nothing else --
            # so `Algebra`, `LinearAlgebra` and `Topology`, the three subjects
            # that should be *most* restricted, were unchecked. A `Topology`
            # module importing `Mathlib.AlgebraicGeometry.Scheme` passed this
            # gate for as long as it existed.
            if LAYER.get(source_owner, LAYER[GEOMETRY_OWNER]) < LAYER[
                GEOMETRY_OWNER
            ] and module.startswith("Mathlib.AlgebraicGeometry"):
                failures.append(
                    f"{path.relative_to(ROOT)}:{line_number}: {source_owner} "
                    f"ranks below {GEOMETRY_OWNER} and imports geometry module "
                    f"{module}"
                )
            if not module.startswith("DerivedAlgGeo."):
                continue
            dependency = module.split(".", 2)[1]
            if dependency not in subjects or dependency == source_owner:
                continue
            graph[source_owner].add(dependency)
            evidence[(source_owner, dependency)].append(
                f"{path.relative_to(ROOT)}:{line_number}"
            )

    for edge, locations_found in sorted(evidence.items()):
        if LAYER.get(edge[0], -1) < LAYER.get(edge[1], -1):
            locations = ", ".join(locations_found[:3])
            failures.append(
                f"reverse subject edge {edge[0]} -> {edge[1]} at {locations}"
            )

    cycle = find_cycle(graph)
    if cycle is not None:
        failures.append("subject dependency cycle: " + " -> ".join(cycle))

    legacy_root = (
        SOURCE_ROOT
        / "CategoryTheory"
        / "Triangulated"
        / "StabilityCondition"
        / "Families"
    )
    geometry_root = (
        SOURCE_ROOT / "AlgebraicGeometry" / "StabilityCondition" / "Families"
    )
    for module in sorted(GEOMETRY_FAMILY_MODULES):
        legacy = legacy_root / f"{module}.lean"
        relocated = geometry_root / f"{module}.lean"
        if legacy.exists():
            failures.append(
                f"geometry-owned module restored below CategoryTheory: "
                f"{legacy.relative_to(ROOT)}"
            )
        if not relocated.exists():
            failures.append(
                f"geometry-owned module missing from AlgebraicGeometry: "
                f"{relocated.relative_to(ROOT)}"
            )

    legacy_dqc = legacy_root / "Dqc"
    relocated_dqc = geometry_root / "Dqc"
    if legacy_dqc.exists():
        failures.append(
            f"geometry-owned subtree restored below CategoryTheory: "
            f"{legacy_dqc.relative_to(ROOT)}"
        )
    if not relocated_dqc.is_dir():
        failures.append(
            f"geometry-owned subtree missing from AlgebraicGeometry: "
            f"{relocated_dqc.relative_to(ROOT)}"
        )

    if failures:
        print("subject-layering gate failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    edge_text = ", ".join(
        f"{source}->{dependency}"
        for source in sorted(graph)
        for dependency in sorted(graph[source])
    )
    print(f"ok: acyclic subject graph ({edge_text})")
    print("ok: CategoryTheory has zero AlgebraicGeometry imports")
    print(
        f"ok: {len(GEOMETRY_FAMILY_MODULES)} geometric family roots have "
        "AlgebraicGeometry owners"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
