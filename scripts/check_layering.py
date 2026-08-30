#!/usr/bin/env python3
"""Check the repository's subject and AlgebraicGeometry dependency direction.

An acyclic Lean module graph can still hide a cycle after modules are grouped
by their declared owners. This gate collapses imports to the top-level subject
directories, rejects cycles in that graph, and enforces the CategoryTheory /
AlgebraicGeometry ownership boundary introduced by issue #601.

The top-level collapse cannot see a reusable moduli or stack root importing a
Bridgeland-family leaf because both live below ``AlgebraicGeometry``. Issue
#850 adds that finer boundary here. The former exact-pair migration allowlist
has been burned to zero; stale entries still fail so exceptions cannot return
silently. The gate also keeps neutral, weak, Bridgeland, and geometric family
declarations in the namespaces matching their owners.
"""

from __future__ import annotations

from collections import defaultdict
import pathlib
import re
import sys


ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE_ROOT = ROOT / "DerivedAlgGeo"
IMPORT = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)"
)
GENERIC_OWNER = "CategoryTheory"
GEOMETRY_OWNER = "AlgebraicGeometry"
GEOMETRY_INSTANCES_OWNER = "GeometryInstances"
GEOMETRY_INSTANCE_UMBRELLAS = {
    "DerivedAlgGeo.CategoryTheory.Monoidal.Triangulated.Instances",
}
STABILITY_FAMILIES_ROOT = (
    "DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families"
)
GENERIC_FAMILIES_NAMESPACE = "CategoryTheory.Triangulated.Families"
GENERIC_STACKS_NAMESPACE = "CategoryTheory"
DERIVED_CATEGORY_NAMESPACE = "AlgebraicGeometry.DerivedCategory"
DERIVED_FAMILIES_NAMESPACE = "AlgebraicGeometry.DerivedCategory.Families"
DQC_NAMESPACE = "AlgebraicGeometry.DerivedCategory.Dqc"
GEOMETRIC_FOURIER_MUKAI_NAMESPACE = (
    "AlgebraicGeometry.DerivedCategory.FourierMukai"
)
STABILITY_GEOMETRY_FAMILIES_NAMESPACE = (
    "AlgebraicGeometry.StabilityCondition.Families"
)
STABILITY_GEOMETRY_FOURIER_MUKAI_NAMESPACE = (
    "AlgebraicGeometry.StabilityCondition.FourierMukai"
)
RETIRED_FLATTENED_FAMILIES_NAMESPACE = (
    "CategoryTheory.Triangulated.StabilityCondition.Families"
)
WEAK_FAMILIES_NAMESPACE = (
    "CategoryTheory.Triangulated.WeakStabilityCondition.Families"
)
WEAK_SUPPORT_NAMESPACE = (
    "CategoryTheory.Triangulated.WeakStabilityCondition.Support"
)
RETIRED_SUPPORT_NAMESPACE = (
    "CategoryTheory.Triangulated.StabilityCondition.Support"
)
WEAK_FINITE_LENGTH_NAMESPACE = (
    "CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength"
)
RETIRED_FINITE_LENGTH_NAMESPACE = (
    "CategoryTheory.Triangulated.StabilityCondition.FiniteLength"
)
STRONG_FAMILIES_NAMESPACE = (
    "CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Families"
)
STRONG_WALL_NAMESPACE = (
    "CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Wall"
)
RETIRED_STRONG_WALL_NAMESPACE = (
    "CategoryTheory.Triangulated.StabilityCondition.Wall"
)
STRONG_SYMMETRY_NAMESPACE = (
    "CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Symmetry"
)
RETIRED_STRONG_SYMMETRY_NAMESPACE = (
    "CategoryTheory.Triangulated.StabilityCondition.Symmetry"
)
LEGACY_GENERIC_FAMILY_DECLARATION = re.compile(
    r"CategoryTheory\.Triangulated\.StabilityCondition\.Families\."
    r"(?:TriangulatedFiberFamily|BoundednessProblem|UniversalBoundedness)\b"
)
PROTECTED_GEOMETRY_SUBTREES = {
    ("AlgebraicGeometry", "Moduli"),
    ("AlgebraicGeometry", "Stacks"),
}
PROTECTED_GEOMETRY_UMBRELLAS = {
    "AlgebraicGeometry/Moduli.lean",
    "AlgebraicGeometry/Stacks.lean",
}
REVERSE_EDGE_ALLOWLIST = ROOT / "scripts" / "layering_reverse_edges.txt"
LAYERING_FIXTURES = ROOT / "scripts" / "fixtures" / "layering"

# Higher layers may import lower layers. Equal-rank support subjects may import
# one another provided the observed graph remains acyclic.
LAYER = {
    "Algebra": 0,
    "LinearAlgebra": 0,
    "Topology": 0,
    GENERIC_OWNER: 1,
    GEOMETRY_OWNER: 2,
    GEOMETRY_INSTANCES_OWNER: 3,
    "Compatibility": 4,
    "Development": 5,
}

NEUTRAL_DERIVED_FAMILY_MODULES = {
    "BoundedGeometry",
    "DerivedPullbackCoherence",
    "DerivedPullbackLaws",
    "DerivedPullbackShift",
    "ExactPullback",
    "ExactPullbackCoherence",
    "FiniteType",
    "FlatPullback",
    "FlatPullbackResolution",
    "LeftDerivedPullback",
    "OpenImmersionPullback",
    "PullbackAcyclicResolution",
    "ResidueFiber",
    "Scheme",
    "SchemeDerived",
}
RETIRED_STABILITY_FAMILY_MODULES = {
    "BoundedGeometry",
    "DerivedPullbackCoherence",
    "DerivedPullbackLaws",
    "DerivedPullbackShift",
    "ExactPullback",
    "ExactPullbackCoherence",
    "FlatPullback",
    "FlatPullbackResolution",
    "LeftDerivedPullback",
    "OpenImmersionPullback",
    "PullbackAcyclicResolution",
    "ResidueFiber",
    "SchemeDerived",
}
GEOMETRIC_FOURIER_MUKAI_MODULES = {
    "DerivedTensorCoherence",
    "KernelAdjunction",
    "KernelAssociativity",
    "KernelConvolution",
    "KernelCorrespondence",
    "KernelDualizingTwist",
}
STABILITY_FAMILY_MODULES = {
    "FiniteTypeGeometry",
    "GeometricBaseChange",
    "InducingPullback",
    "RelativeHN",
    "Scheme",
    "SchemeSemistableLocus",
}
STABILITY_FOURIER_MUKAI_MODULES = {
    "KernelComposition",
    "KernelSwap",
    "KernelUnit",
    "KernelUnitConvolution",
}


def owner(path: pathlib.Path) -> str:
    relative = path.relative_to(SOURCE_ROOT)
    parts = relative.parts
    if parts[0] == GENERIC_OWNER:
        module = "DerivedAlgGeo." + ".".join(parts).removesuffix(".lean")
        if (has_geometry_instances_segment(parts) or
                module in GEOMETRY_INSTANCE_UMBRELLAS):
            return GEOMETRY_INSTANCES_OWNER
    return relative.parts[0] if len(relative.parts) > 1 else relative.stem


def is_stability_families_import(module: str) -> bool:
    """Whether ``module`` is the family leaf forbidden to reusable AG roots."""

    return module == STABILITY_FAMILIES_ROOT or module.startswith(
        STABILITY_FAMILIES_ROOT + "."
    )


def is_protected_geometry_source(relative: pathlib.PurePath) -> bool:
    """Whether ``relative`` is a reusable Moduli/Stacks root module."""

    return relative.as_posix() in PROTECTED_GEOMETRY_UMBRELLAS or (
        len(relative.parts) >= 2
        and tuple(relative.parts[:2]) in PROTECTED_GEOMETRY_SUBTREES
    )


def collect_geometry_reverse_edges(
    source_root: pathlib.Path, pattern: str = "*.lean"
) -> list[tuple[str, int, str]]:
    """Collect protected-root imports of stability-family leaves.

    Source names are relative to ``source_root`` so the same scanner can run
    against both the repository and the known-answer fixture trees.
    """

    edges: list[tuple[str, int, str]] = []
    for path in sorted(source_root.rglob(pattern)):
        relative = path.relative_to(source_root)
        if not is_protected_geometry_source(relative):
            continue
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = IMPORT.match(line)
            if match is not None and is_stability_families_import(match.group(1)):
                edges.append((relative.as_posix(), line_number, match.group(1)))
    return edges


def load_reverse_edge_allowlist() -> tuple[set[tuple[str, str]], list[str]]:
    """Read the exact legacy-edge allowlist, rejecting malformed entries."""

    failures: list[str] = []
    allowed: set[tuple[str, str]] = set()
    if not REVERSE_EDGE_ALLOWLIST.exists():
        return allowed, [
            f"missing reverse-edge allowlist: "
            f"{REVERSE_EDGE_ALLOWLIST.relative_to(ROOT)}"
        ]
    for line_number, raw in enumerate(
        REVERSE_EDGE_ALLOWLIST.read_text(encoding="utf-8").splitlines(), 1
    ):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2:
            failures.append(
                f"{REVERSE_EDGE_ALLOWLIST.relative_to(ROOT)}:{line_number}: "
                "expected SOURCE<TAB>IMPORT"
            )
            continue
        source, module = fields
        source_path = pathlib.PurePosixPath(source)
        if (
            not is_protected_geometry_source(source_path)
            or not is_stability_families_import(module)
        ):
            failures.append(
                f"{REVERSE_EDGE_ALLOWLIST.relative_to(ROOT)}:{line_number}: "
                "entry is outside the guarded Moduli/Stacks-to-Families boundary"
            )
            continue
        edge = (source, module)
        if edge in allowed:
            failures.append(
                f"{REVERSE_EDGE_ALLOWLIST.relative_to(ROOT)}:{line_number}: "
                f"duplicate entry {source} -> {module}"
            )
        allowed.add(edge)
    return allowed, failures


def check_layering_fixtures() -> list[str]:
    """Run known-answer examples through the production reverse-edge parser."""

    failures: list[str] = []
    allowed_root = LAYERING_FIXTURES / "allowed"
    forbidden_root = LAYERING_FIXTURES / "forbidden"
    if not allowed_root.is_dir() or not forbidden_root.is_dir():
        return [
            f"missing layering fixture trees below {LAYERING_FIXTURES.relative_to(ROOT)}"
        ]

    allowed_edges = collect_geometry_reverse_edges(allowed_root, "*.imports")
    if allowed_edges:
        rendered = ", ".join(
            f"{source}:{line_number} -> {module}"
            for source, line_number, module in allowed_edges
        )
        failures.append(f"allowed layering fixture was rejected: {rendered}")

    forbidden_edges = collect_geometry_reverse_edges(forbidden_root, "*.imports")
    actual = {(source, module) for source, _, module in forbidden_edges}
    expected = {
        (
            "AlgebraicGeometry/Stacks/Forbidden.imports",
            STABILITY_FAMILIES_ROOT + ".Dqc",
        )
    }
    if actual != expected:
        failures.append(
            "forbidden layering fixture did not produce its known answer: "
            f"expected {sorted(expected)}, found {sorted(actual)}"
        )
    return failures


def has_geometry_instances_segment(parts: tuple[str, ...] | list[str]) -> bool:
    return any(
        parts[index] == "Instances" and
        pathlib.Path(parts[index + 1]).stem == GEOMETRY_OWNER
        for index in range(len(parts) - 1)
    )


def dependency_owner(module: str, subjects: set[str]) -> str | None:
    parts = module.split(".")
    if len(parts) < 2 or parts[0] != "DerivedAlgGeo":
        return None
    if parts[1] == GENERIC_OWNER and (
        has_geometry_instances_segment(parts[2:]) or
        module in GEOMETRY_INSTANCE_UMBRELLAS
    ):
        return GEOMETRY_INSTANCES_OWNER
    return parts[1] if parts[1] in subjects else None


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
    imports_by_path: dict[pathlib.Path, list[str]] = defaultdict(list)
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
            imports_by_path[path].append(module)
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
            dependency = dependency_owner(module, subjects)
            if dependency is None or dependency == source_owner:
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

    legacy_stability_root = (
        SOURCE_ROOT
        / "CategoryTheory"
        / "Triangulated"
        / "StabilityCondition"
    )
    legacy_stability_umbrella = legacy_stability_root.with_suffix(".lean")
    if legacy_stability_root.exists() or legacy_stability_umbrella.exists():
        failures.append(
            "legacy sibling CategoryTheory/Triangulated/StabilityCondition "
            "path restored; Bridgeland stability is the child of "
            "WeakStabilityCondition"
        )

    generic_stacks_source = (
        SOURCE_ROOT / "CategoryTheory" / "Sites" / "StackInGroupoids.lean"
    )
    generic_stacks_text = generic_stacks_source.read_text(encoding="utf-8")
    if not re.search(
        rf"^namespace {GENERIC_STACKS_NAMESPACE}$",
        generic_stacks_text,
        re.MULTILINE,
    ):
        failures.append(
            f"{generic_stacks_source.relative_to(ROOT)}: generic "
            f"stack-in-groupoids declarations must use namespace "
            f"{GENERIC_STACKS_NAMESPACE}"
        )
    if re.search(
        r"^namespace AlgebraicGeometry$", generic_stacks_text, re.MULTILINE
    ):
        failures.append(
            f"{generic_stacks_source.relative_to(ROOT)}: generic "
            "stack-in-groupoids declarations restored the retired geometric "
            "namespace"
        )

    generic_families_source_root = (
        SOURCE_ROOT / "CategoryTheory" / "Triangulated" / "Families"
    )
    for module in ("BaseChange", "Boundedness"):
        path = generic_families_source_root / f"{module}.lean"
        text = path.read_text(encoding="utf-8")
        if f"namespace {GENERIC_FAMILIES_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: generic family declarations must "
                f"use namespace {GENERIC_FAMILIES_NAMESPACE}"
            )

    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            if LEGACY_GENERIC_FAMILY_DECLARATION.search(line):
                failures.append(
                    f"{path.relative_to(ROOT)}:{line_number}: neutral family "
                    "declaration restored below the legacy stability namespace"
                )

    weak_stability_root = (
        SOURCE_ROOT
        / "CategoryTheory"
        / "Triangulated"
        / "WeakStabilityCondition"
    )
    weak_stability_umbrella = weak_stability_root.with_suffix(".lean")
    strong_stability_root = weak_stability_root / "StabilityCondition"
    strong_stability_umbrella = strong_stability_root.with_suffix(".lean")
    weak_stability_module = (
        "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition"
    )
    strong_stability_module = weak_stability_module + ".StabilityCondition"

    weak_families_source_root = weak_stability_root / "Families"
    for module in ("Basic", "Weak"):
        path = weak_families_source_root / f"{module}.lean"
        text = path.read_text(encoding="utf-8")
        if f"namespace {WEAK_FAMILIES_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: weak-family declarations must "
                f"use namespace {WEAK_FAMILIES_NAMESPACE}"
            )
        if f"namespace {RETIRED_FLATTENED_FAMILIES_NAMESPACE}" in text:
            failures.append(
                f"{path.relative_to(ROOT)}: weak-family declarations restored "
                "the legacy Bridgeland-family namespace"
            )

    weak_support_predicate_root = weak_stability_root / "Support" / "Predicate"
    for path in sorted(weak_support_predicate_root.glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if f"namespace {WEAK_SUPPORT_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: weak support-predicate declarations "
                f"must use namespace {WEAK_SUPPORT_NAMESPACE}"
            )

    weak_simple_charge = (
        weak_stability_root / "Foundation" / "StabilityFunction"
        / "SimpleCharge.lean"
    )
    weak_simple_charge_text = weak_simple_charge.read_text(encoding="utf-8")
    if f"namespace {WEAK_FINITE_LENGTH_NAMESPACE}" not in weak_simple_charge_text:
        failures.append(
            f"{weak_simple_charge.relative_to(ROOT)}: finite-length simple-charge "
            f"declarations must use namespace {WEAK_FINITE_LENGTH_NAMESPACE}"
        )
    retired_weak_foundations = weak_stability_root / "Foundations"
    if retired_weak_foundations.exists() or retired_weak_foundations.with_suffix(
        ".lean"
    ).exists():
        failures.append(
            "the duplicate WeakStabilityCondition/Foundations tree was restored"
        )

    strong_families_source_root = strong_stability_root / "Families"
    for module in (
        "CategoricalOrdinary",
        "FiberwiseOrdinary",
        "FiberwiseSupport",
        "Ordinary",
        "PreStabilityBaseChange",
    ):
        path = strong_families_source_root / f"{module}.lean"
        text = path.read_text(encoding="utf-8")
        if f"namespace {STRONG_FAMILIES_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: Bridgeland-family declarations "
                f"must use namespace {STRONG_FAMILIES_NAMESPACE}"
            )
        if f"namespace {RETIRED_FLATTENED_FAMILIES_NAMESPACE}" in text:
            failures.append(
                f"{path.relative_to(ROOT)}: Bridgeland-family declarations "
                "restored the legacy flattened namespace"
            )

    strong_walls_source_root = strong_stability_root / "Walls"
    for relative in (
        pathlib.Path("Numerical") / "Basic.lean",
        pathlib.Path("Spherical") / "Basic.lean",
        pathlib.Path("Spherical") / "Finiteness.lean",
    ):
        path = strong_walls_source_root / relative
        text = path.read_text(encoding="utf-8")
        if f"namespace {STRONG_WALL_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: Bridgeland wall declarations "
                f"must use namespace {STRONG_WALL_NAMESPACE}"
            )
    for path in sorted(strong_walls_source_root.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if f"namespace {RETIRED_STRONG_WALL_NAMESPACE}" in text:
            failures.append(
                f"{path.relative_to(ROOT)}: Bridgeland wall declarations "
                "restored the former sibling namespace"
            )

    strong_symmetry_bridge = (
        strong_stability_root
        / "Symmetry"
        / "Autoequivalence"
        / "FourierMukai.lean"
    )
    strong_symmetry_bridge_text = strong_symmetry_bridge.read_text(
        encoding="utf-8"
    )
    if (
        f"namespace {STRONG_SYMMETRY_NAMESPACE}"
        not in strong_symmetry_bridge_text
    ):
        failures.append(
            f"{strong_symmetry_bridge.relative_to(ROOT)}: Bridgeland "
            f"Fourier--Mukai symmetry declarations must use namespace "
            f"{STRONG_SYMMETRY_NAMESPACE}"
        )

    weak_parent_paths = [weak_stability_umbrella]
    weak_parent_paths.extend(
        path
        for path in sorted(weak_stability_root.rglob("*.lean"))
        if path != strong_stability_umbrella
        and strong_stability_root not in path.parents
    )
    for path in weak_parent_paths:
        for module in imports_by_path[path]:
            if module == strong_stability_module or module.startswith(
                strong_stability_module + "."
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}: weak-stability parent imports "
                    f"its Bridgeland child {module}"
                )

    if weak_stability_module not in imports_by_path[strong_stability_umbrella]:
        failures.append(
            "the Bridgeland StabilityCondition umbrella must import its "
            "WeakStabilityCondition parent"
        )

    generic_families_root = strong_stability_root / "Families"
    stability_families_root = (
        SOURCE_ROOT / "AlgebraicGeometry" / "StabilityCondition" / "Families"
    )
    neutral_derived_families_root = (
        SOURCE_ROOT / "AlgebraicGeometry" / "DerivedCategory" / "Families"
    )
    derived_category_basic = neutral_derived_families_root.parent / "Basic.lean"
    derived_category_basic_text = derived_category_basic.read_text(
        encoding="utf-8"
    )
    if (
        f"namespace {DERIVED_CATEGORY_NAMESPACE}"
        not in derived_category_basic_text
    ):
        failures.append(
            f"{derived_category_basic.relative_to(ROOT)}: scheme-derived "
            f"category declarations must use namespace {DERIVED_CATEGORY_NAMESPACE}"
        )
    legacy_geometric_namespace = (
        f"namespace {RETIRED_FLATTENED_FAMILIES_NAMESPACE}"
    )
    if legacy_geometric_namespace in derived_category_basic_text:
        failures.append(
            f"{derived_category_basic.relative_to(ROOT)}: scheme-derived "
            "category declarations restored the legacy stability namespace"
        )
    for path in sorted(neutral_derived_families_root.glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if f"namespace {DERIVED_FAMILIES_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: scheme-derived family declarations "
                f"must use namespace {DERIVED_FAMILIES_NAMESPACE}"
            )
        if legacy_geometric_namespace in text:
            failures.append(
                f"{path.relative_to(ROOT)}: scheme-derived family declarations "
                "restored the legacy stability namespace"
            )
    geometric_fourier_mukai_root = (
        SOURCE_ROOT / "AlgebraicGeometry" / "DerivedCategory" / "FourierMukai"
    )
    for path in sorted(geometric_fourier_mukai_root.glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if f"namespace {GEOMETRIC_FOURIER_MUKAI_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: geometric Fourier--Mukai "
                f"declarations must use namespace "
                f"{GEOMETRIC_FOURIER_MUKAI_NAMESPACE}"
            )
        if legacy_geometric_namespace in text:
            failures.append(
                f"{path.relative_to(ROOT)}: geometric Fourier--Mukai "
                "declarations restored the legacy stability namespace"
            )
    stability_fourier_mukai_root = (
        SOURCE_ROOT / "AlgebraicGeometry" / "StabilityCondition" / "FourierMukai"
    )
    for path in sorted(stability_families_root.glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if f"namespace {STABILITY_GEOMETRY_FAMILIES_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: stability-family geometry must "
                f"use namespace {STABILITY_GEOMETRY_FAMILIES_NAMESPACE}"
            )
    for path in sorted(stability_fourier_mukai_root.glob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if (
            f"namespace {STABILITY_GEOMETRY_FOURIER_MUKAI_NAMESPACE}"
            not in text
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: stability-specific "
                f"Fourier--Mukai declarations must use namespace "
                f"{STABILITY_GEOMETRY_FOURIER_MUKAI_NAMESPACE}"
            )

    perfect_complex_root = (
        SOURCE_ROOT / "AlgebraicGeometry" / "Moduli" / "PerfectComplex"
    )
    for module in (
        "AffineFamilyRelativePerfect",
        "AffineFamilyRelativePerfectPseudofunctor",
    ):
        path = perfect_complex_root / f"{module}.lean"
        text = path.read_text(encoding="utf-8")
        if not re.search(r"^namespace AlgebraicGeometry$", text, re.MULTILINE):
            failures.append(
                f"{path.relative_to(ROOT)}: neutral perfect-complex moduli "
                "declarations must use namespace AlgebraicGeometry"
            )

    geometric_tensor_instance = (
        SOURCE_ROOT
        / "CategoryTheory"
        / "Monoidal"
        / "Triangulated"
        / "Instances"
        / "AlgebraicGeometry"
        / "DerivedTensor.lean"
    )
    geometric_tensor_instance_text = geometric_tensor_instance.read_text(
        encoding="utf-8"
    )
    if (
        f"namespace {GEOMETRIC_FOURIER_MUKAI_NAMESPACE}"
        not in geometric_tensor_instance_text
    ):
        failures.append(
            f"{geometric_tensor_instance.relative_to(ROOT)}: geometric "
            f"derived-tensor registration must use namespace "
            f"{GEOMETRIC_FOURIER_MUKAI_NAMESPACE}"
        )

    development_scaffolding = (
        SOURCE_ROOT / "Development" / "StabilityCondition" / "Families"
        / "Scaffolding.lean"
    )
    development_namespace = f"{STRONG_FAMILIES_NAMESPACE}.Development"
    development_text = development_scaffolding.read_text(encoding="utf-8")
    if f"namespace {development_namespace}" not in development_text:
        failures.append(
            f"{development_scaffolding.relative_to(ROOT)}: strong-family "
            f"development scaffolding must use namespace {development_namespace}"
        )

    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if legacy_geometric_namespace in text:
            failures.append(
                f"{path.relative_to(ROOT)}: declaration restored the retired "
                f"flattened namespace {RETIRED_FLATTENED_FAMILIES_NAMESPACE}"
            )
        if RETIRED_SUPPORT_NAMESPACE in text:
            failures.append(
                f"{path.relative_to(ROOT)}: declaration restored the retired "
                f"strong-sibling namespace {RETIRED_SUPPORT_NAMESPACE}"
            )
        if RETIRED_FINITE_LENGTH_NAMESPACE in text:
            failures.append(
                f"{path.relative_to(ROOT)}: declaration restored the retired "
                f"strong-sibling namespace {RETIRED_FINITE_LENGTH_NAMESPACE}"
            )
        if RETIRED_STRONG_SYMMETRY_NAMESPACE in text:
            failures.append(
                f"{path.relative_to(ROOT)}: declaration restored the retired "
                f"strong-sibling namespace {RETIRED_STRONG_SYMMETRY_NAMESPACE}"
            )

    all_geometry_modules = (
        NEUTRAL_DERIVED_FAMILY_MODULES
        | GEOMETRIC_FOURIER_MUKAI_MODULES
        | STABILITY_FAMILY_MODULES
        | STABILITY_FOURIER_MUKAI_MODULES
    )
    for module in sorted(all_geometry_modules):
        legacy = generic_families_root / f"{module}.lean"
        if legacy.exists():
            failures.append(
                f"geometry-owned module restored below CategoryTheory: "
                f"{legacy.relative_to(ROOT)}"
            )

    for module in sorted(NEUTRAL_DERIVED_FAMILY_MODULES):
        relocated = neutral_derived_families_root / f"{module}.lean"
        if not relocated.exists():
            failures.append(
                f"neutral scheme-derived family module missing: "
                f"{relocated.relative_to(ROOT)}"
            )

    for module in sorted(RETIRED_STABILITY_FAMILY_MODULES):
        legacy = stability_families_root / f"{module}.lean"
        if legacy.exists():
            failures.append(
                f"neutral derived-category module restored below stability: "
                f"{legacy.relative_to(ROOT)}"
            )

    for module in sorted(GEOMETRIC_FOURIER_MUKAI_MODULES):
        relocated = geometric_fourier_mukai_root / f"{module}.lean"
        legacy = stability_families_root / f"{module}.lean"
        if not relocated.exists():
            failures.append(
                f"geometric Fourier--Mukai module missing: "
                f"{relocated.relative_to(ROOT)}"
            )
        if legacy.exists():
            failures.append(
                f"neutral Fourier--Mukai module restored below stability: "
                f"{legacy.relative_to(ROOT)}"
            )

    for module in sorted(STABILITY_FAMILY_MODULES):
        relocated = stability_families_root / f"{module}.lean"
        if not relocated.exists():
            failures.append(
                f"stability-specific family module missing: "
                f"{relocated.relative_to(ROOT)}"
            )

    for module in sorted(STABILITY_FOURIER_MUKAI_MODULES):
        relocated = stability_fourier_mukai_root / f"{module}.lean"
        legacy = stability_families_root / f"{module}.lean"
        if not relocated.exists():
            failures.append(
                f"stability-specific Fourier--Mukai module missing: "
                f"{relocated.relative_to(ROOT)}"
            )
        if legacy.exists():
            failures.append(
                f"stability Fourier--Mukai module restored below Families: "
                f"{legacy.relative_to(ROOT)}"
            )

    legacy_dqc = generic_families_root / "Dqc"
    retired_stability_dqc = stability_families_root / "Dqc"
    relocated_dqc = SOURCE_ROOT / "AlgebraicGeometry" / "DerivedCategory" / "Dqc"
    if legacy_dqc.exists():
        failures.append(
            f"geometry-owned subtree restored below CategoryTheory: "
            f"{legacy_dqc.relative_to(ROOT)}"
        )
    if retired_stability_dqc.exists():
        failures.append(
            f"neutral Dqc subtree restored below stability: "
            f"{retired_stability_dqc.relative_to(ROOT)}"
        )
    if not relocated_dqc.is_dir():
        failures.append(
            f"geometry-owned subtree missing from AlgebraicGeometry: "
            f"{relocated_dqc.relative_to(ROOT)}"
        )
    dqc_sources = [relocated_dqc.with_suffix(".lean")]
    if relocated_dqc.is_dir():
        dqc_sources.extend(sorted(relocated_dqc.glob("*.lean")))
    for path in dqc_sources:
        if not path.is_file():
            failures.append(
                f"geometry-owned Dqc module missing: {path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        if f"namespace {DQC_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: Dqc declarations must use "
                f"namespace {DQC_NAMESPACE}"
            )
        if legacy_geometric_namespace in text:
            failures.append(
                f"{path.relative_to(ROOT)}: Dqc declarations restored the "
                "legacy stability namespace"
            )

    failures.extend(check_layering_fixtures())
    allowed_reverse_edges, allowlist_failures = load_reverse_edge_allowlist()
    failures.extend(allowlist_failures)
    reverse_edges = collect_geometry_reverse_edges(SOURCE_ROOT)
    observed_reverse_edges = {
        (source, module) for source, _, module in reverse_edges
    }
    for source, line_number, module in reverse_edges:
        if (source, module) not in allowed_reverse_edges:
            failures.append(
                f"DerivedAlgGeo/{source}:{line_number}: reusable geometry root "
                f"imports stability-family leaf {module}"
            )
    for source, module in sorted(
        allowed_reverse_edges - observed_reverse_edges
    ):
        failures.append(
            f"stale reverse-edge allowlist entry {source} -> {module}; "
            f"remove it from {REVERSE_EDGE_ALLOWLIST.relative_to(ROOT)}"
        )

    legacy_dg_root = SOURCE_ROOT / "CategoryTheory" / "DGCategory"
    legacy_dg_umbrella = legacy_dg_root.with_suffix(".lean")
    if legacy_dg_root.exists() or legacy_dg_umbrella.exists():
        failures.append(
            "legacy monolithic CategoryTheory/DGCategory path restored"
        )

    raw_dg_root = SOURCE_ROOT / "CategoryTheory" / "Enriched" / "DGCategory"
    enhancement_module = (
        "DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement"
    )
    for path in sorted(raw_dg_root.rglob("*.lean")):
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = IMPORT.match(line)
            if match is not None and match.group(1).startswith(enhancement_module):
                failures.append(
                    f"{path.relative_to(ROOT)}:{line_number}: raw dg theory "
                    "imports the triangulated enhancement layer"
                )

    monoidal_root = SOURCE_ROOT / "CategoryTheory" / "Monoidal"
    enriched_module = "DerivedAlgGeo.CategoryTheory.Enriched"
    for path in sorted(monoidal_root.rglob("*.lean")):
        for module in imports_by_path[path]:
            if module == enriched_module or module.startswith(enriched_module + "."):
                failures.append(
                    f"{path.relative_to(ROOT)}: monoidal parent layer imports "
                    f"its enriched child {module}"
                )
            if module.startswith(enhancement_module):
                failures.append(
                    f"{path.relative_to(ROOT)}: monoidal parent layer imports "
                    f"the dg-enhancement child {module}"
                )

    enriched_umbrella = SOURCE_ROOT / "CategoryTheory" / "Enriched.lean"
    monoidal_module = "DerivedAlgGeo.CategoryTheory.Monoidal"
    if monoidal_module not in imports_by_path[enriched_umbrella]:
        failures.append(
            "CategoryTheory/Enriched.lean must import the monoidal parent layer"
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
    print(
        "ok: generic CategoryTheory has zero AlgebraicGeometry imports; "
        "explicit geometry-instance leaves are classified separately"
    )
    print("ok: raw dg theory is independent of the dg-enhancement layer")
    print("ok: the monoidal layer precedes enrichment and does not import its children")
    print(
        "ok: weak stability is independent of, and directly parented by, "
        "Bridgeland stability"
    )
    print(
        "ok: neutral triangulated-family declarations use the generic "
        "CategoryTheory.Triangulated.Families namespace"
    )
    print(
        "ok: generic stacks in groupoids use their CategoryTheory namespace"
    )
    print(
        "ok: weak-stability family declarations use the matching "
        "CategoryTheory.Triangulated.WeakStabilityCondition.Families namespace"
    )
    print(
        "ok: weak support-predicate declarations use the matching "
        "CategoryTheory.Triangulated.WeakStabilityCondition.Support namespace"
    )
    print(
        "ok: finite-length simple-charge declarations use the weak-parent "
        "namespace and the duplicate Foundations tree is absent"
    )
    print(
        "ok: Bridgeland-family declarations use the matching strong-child "
        "namespace"
    )
    print(
        "ok: Bridgeland wall declarations use the matching strong-child "
        "namespace"
    )
    print(
        "ok: Bridgeland Fourier--Mukai symmetry declarations use the matching "
        "strong-child namespace"
    )
    print(
        "ok: scheme-derived categories, families, Dqc, and geometric "
        "Fourier--Mukai declarations use their matching AlgebraicGeometry "
        "namespaces"
    )
    print(
        "ok: stability-family geometry and stability-specific Fourier--Mukai "
        "actions use their matching AlgebraicGeometry namespaces"
    )
    print(
        "ok: the retired flattened categorical stability-family namespace is "
        "absent from DerivedAlgGeo"
    )
    print(
        "ok: neutral scheme-derived families, geometric Fourier--Mukai, and "
        "stability-specific geometry have distinct AlgebraicGeometry owners"
    )
    print(
        "ok: Moduli/Stacks reverse-edge fixtures distinguish allowed and "
        "forbidden imports"
    )
    print(
        f"ok: {len(reverse_edges)} measured Moduli/Stacks -> "
        "StabilityCondition/Families edge(s); the migration allowlist is empty"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
