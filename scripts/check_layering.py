#!/usr/bin/env python3
"""Check the repository's subject and AlgebraicGeometry dependency direction.

An acyclic Lean module graph can still hide a cycle after modules are grouped
by their declared owners. This gate collapses imports to the top-level subject
directories, rejects cycles in that graph, and enforces the CategoryTheory /
AlgebraicGeometry ownership boundary introduced by issue #601.

The virtual ``GeometryInstances`` owner records explicit
``Instances/AlgebraicGeometry`` leaves below categorical sources. The gate
forbids algebraic geometry from importing back into those realization leaves,
rejects restoration of the retired geometric stability subtree, and keeps the
migration allowlist burned to zero. It also keeps neutral, weak, Bridgeland,
and geometric family declarations in the namespaces matching their owners.
It also guards the bicategorical adjunction and limit-preservation split, the
generic derived-category, cohomological, and stack roots, the algebraic
module-localization kernel owner, and requires ordinary prestability to expose
weak prestability structurally.
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
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
    "Families.Instances",
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Families.Instances",
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Symmetry.Autoequivalence.Instances",
}
GENERIC_FAMILIES_NAMESPACE = "CategoryTheory.Triangulated.Families"
GENERIC_MODULI_NAMESPACE = "CategoryTheory.Moduli"
GENERIC_STACKS_NAMESPACE = "CategoryTheory"
GENERIC_DERIVED_NAMESPACE = "CategoryTheory"
DERIVED_CATEGORY_NAMESPACE = "AlgebraicGeometry.DerivedCategory"
DERIVED_FAMILIES_NAMESPACE = "AlgebraicGeometry.DerivedCategory.Families"
DQC_NAMESPACE = "AlgebraicGeometry.DerivedCategory.Dqc"
GEOMETRIC_FOURIER_MUKAI_NAMESPACE = (
    "AlgebraicGeometry.DerivedCategory.FourierMukai"
)
CATEGORICAL_FOURIER_MUKAI_NAMESPACE = (
    "CategoryTheory.Triangulated.FourierMukai"
)
GEOMETRIC_HN_NAMESPACE = "AlgebraicGeometry.Moduli.HarderNarasimhan"
GEOMETRIC_SEMISTABILITY_NAMESPACE = "AlgebraicGeometry.Moduli.Semistability"
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
STRONG_STABILITY_NAMESPACE = (
    "CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition"
)
STRONG_FAMILIES_NAMESPACE = f"{STRONG_STABILITY_NAMESPACE}.Families"
STRONG_WALL_NAMESPACE = f"{STRONG_STABILITY_NAMESPACE}.Wall"
RETIRED_STRONG_WALL_NAMESPACE = (
    "CategoryTheory.Triangulated.StabilityCondition.Wall"
)
RETIRED_STRONG_SYMMETRY_NAMESPACE = (
    "CategoryTheory.Triangulated.StabilityCondition.Symmetry"
)
STRONG_GROUP_ACTION_NAMESPACE = f"{STRONG_STABILITY_NAMESPACE}.GroupAction"
RETIRED_STRONG_GROUP_ACTION_NAMESPACE = (
    "CategoryTheory.Triangulated.StabilityCondition.GroupAction"
)
STRONG_DEFORMATION_NAMESPACE = f"{STRONG_STABILITY_NAMESPACE}.Deformation"
RETIRED_STRONG_DEFORMATION_NAMESPACE = "CategoryTheory.Triangulated.Deformation"
RESTATE_GROUP_ACTION_NAMES = ROOT / "exe" / "RestateHistoricalNames.lean"
RETIRED_IMPORT_SHIMS = {
    "DerivedAlgGeo.CategoryTheory.PseudofunctorObjectProperty": (
        SOURCE_ROOT / "CategoryTheory" / "PseudofunctorObjectProperty.lean",
        "DerivedAlgGeo.CategoryTheory.Pseudofunctor.ObjectProperty",
    ),
    "DerivedAlgGeo.CategoryTheory.Triangulated.Families.Boundedness": (
        SOURCE_ROOT / "CategoryTheory" / "Triangulated" / "Families" /
            "Boundedness.lean",
        "DerivedAlgGeo.CategoryTheory.Moduli.Boundedness",
    ),
    "DerivedAlgGeo.CategoryTheory.WeakSerreExact": (
        SOURCE_ROOT / "CategoryTheory" / "WeakSerreExact.lean",
        "DerivedAlgGeo.CategoryTheory.Abelian.WeakSerre",
    ),
    "DerivedAlgGeo.CategoryTheory.ConstantSheafPullback": (
        SOURCE_ROOT / "CategoryTheory" / "ConstantSheafPullback.lean",
        "DerivedAlgGeo.CategoryTheory.Sites.Sheaves.ConstantPullback",
    ),
    "DerivedAlgGeo.CategoryTheory.SheafCohomologyPushforward": (
        SOURCE_ROOT / "CategoryTheory" / "SheafCohomologyPushforward.lean",
        "DerivedAlgGeo.CategoryTheory.Sites.Sheaves.CohomologyPushforward",
    ),
    "DerivedAlgGeo.CategoryTheory.TopologicalSheafCohomologyPushforward": (
        SOURCE_ROOT / "CategoryTheory" /
            "TopologicalSheafCohomologyPushforward.lean",
        "DerivedAlgGeo.Topology.Sheaves.CohomologyPushforward",
    ),
    "DerivedAlgGeo.CategoryTheory.Sites.CohomologyShortExact": (
        SOURCE_ROOT / "CategoryTheory" / "Sites" /
            "CohomologyShortExact.lean",
        "DerivedAlgGeo.CategoryTheory.Sites.Sheaves.CohomologyShortExact",
    ),
    "DerivedAlgGeo.CategoryTheory.Adjunction": (
        SOURCE_ROOT / "CategoryTheory" / "Adjunction.lean",
        "DerivedAlgGeo.CategoryTheory.Bicategory.Adjunction or "
        "DerivedAlgGeo.CategoryTheory.Limits.Preserves",
    ),
    "DerivedAlgGeo.CategoryTheory.Adjunction.PreservesColimits": (
        SOURCE_ROOT / "CategoryTheory" / "Adjunction" /
            "PreservesColimits.lean",
        "DerivedAlgGeo.CategoryTheory.Limits.Preserves",
    ),
    "DerivedAlgGeo.CategoryTheory.EquivalenceTransport": (
        SOURCE_ROOT / "CategoryTheory" / "EquivalenceTransport.lean",
        "DerivedAlgGeo.CategoryTheory.Pseudofunctor.Transport",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Duality.Serre.LinearDual": (
        SOURCE_ROOT / "AlgebraicGeometry" / "Duality" / "Serre" /
            "LinearDual.lean",
        "DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.LinearDual",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Modules.Affine.Exactness": (
        SOURCE_ROOT / "AlgebraicGeometry" / "Modules" / "Affine" /
            "Exactness.lean",
        "DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Exactness",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Modules.Presentation": (
        SOURCE_ROOT / "AlgebraicGeometry" / "Modules" / "Presentation.lean",
        "DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Modules.Presentation.Finite": (
        SOURCE_ROOT / "AlgebraicGeometry" / "Modules" / "Presentation" /
            "Finite.lean",
        "DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Finite",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Modules.Presentation.Transport": (
        SOURCE_ROOT / "AlgebraicGeometry" / "Modules" / "Presentation" /
            "Transport.lean",
        "DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Presentation.Transport",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Divisors.Tensor": (
        SOURCE_ROOT / "AlgebraicGeometry" / "Divisors" / "Tensor.lean",
        "DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Basic",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Divisors.Picard": (
        SOURCE_ROOT / "AlgebraicGeometry" / "Divisors" / "Picard.lean",
        "DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Picard",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Divisors.Monoidal": (
        SOURCE_ROOT / "AlgebraicGeometry" / "Divisors" / "Monoidal.lean",
        "DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal",
    ),
    "DerivedAlgGeo.AlgebraicGeometry.Stacks.Basic": (
        SOURCE_ROOT / "AlgebraicGeometry" / "Stacks" / "Basic.lean",
        "DerivedAlgGeo.CategoryTheory.Sites.StackInGroupoids",
    ),
    "DerivedAlgGeo.Compatibility.StabilityConditionFamilies": (
        SOURCE_ROOT / "Compatibility" / "StabilityConditionFamilies.lean",
        "the relevant narrow categorical or geometric owner",
    ),
    "DerivedAlgGeo.Compatibility.StabilityConditionGroupActionReview": (
        SOURCE_ROOT / "Compatibility" / "StabilityConditionGroupActionReview.lean",
        "the canonical GroupAction owner",
    ),
    "DerivedAlgGeo.Compatibility": (
        SOURCE_ROOT / "Compatibility.lean",
        "the relevant narrow categorical or geometric owner",
    ),
}
CENSUS_OWNER_IMPORTS = {
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Families",
    "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory",
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Families.Instances",
    "DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition."
    "StabilityCondition.Symmetry.Autoequivalence.Instances",
}
LEGACY_GENERIC_FAMILY_DECLARATION = re.compile(
    r"CategoryTheory\.Triangulated\.StabilityCondition\.Families\."
    r"(?:TriangulatedFiberFamily|BoundednessProblem|UniversalBoundedness)\b"
)
REVERSE_EDGE_ALLOWLIST = ROOT / "scripts" / "layering_reverse_edges.txt"
LAYERING_FIXTURES = ROOT / "scripts" / "fixtures" / "layering"

# Higher layers may import lower layers. Equal-rank support subjects may import
# one another provided the observed graph remains acyclic.
LAYER = {
    "Algebra": 0,
    "LinearAlgebra": 0,
    GENERIC_OWNER: 1,
    "Topology": 2,
    GEOMETRY_OWNER: 3,
    GEOMETRY_INSTANCES_OWNER: 4,
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
GEOMETRIC_FOURIER_MUKAI_MODULES = {
    "DerivedTensorCoherence",
    "KernelAdjunction",
    "KernelAssociativity",
    "KernelConvolution",
    "KernelCorrespondence",
    "KernelDualizingTwist",
    "KernelComposition",
    "KernelSwap",
    "KernelUnit",
    "KernelUnitConvolution",
}
GEOMETRIC_MODULI_MODULES = {
    pathlib.Path("HarderNarasimhan") / "RelativeFiltration.lean":
        GEOMETRIC_HN_NAMESPACE,
    pathlib.Path("Semistability") / "Locus.lean":
        GEOMETRIC_SEMISTABILITY_NAMESPACE,
}
GEOMETRIC_INSTANCE_MODULES = {
    pathlib.Path("CategoryTheory/Triangulated/WeakStabilityCondition/Families/")
    / "Instances/AlgebraicGeometry/Scheme.lean",
    pathlib.Path(
        "CategoryTheory/Triangulated/WeakStabilityCondition/"
        "StabilityCondition/Families/Instances/AlgebraicGeometry/"
        "DerivedPullback.lean"
    ),
    pathlib.Path(
        "CategoryTheory/Triangulated/WeakStabilityCondition/"
        "StabilityCondition/Families/Instances/AlgebraicGeometry/"
        "BoundedCoherentBaseChange.lean"
    ),
    pathlib.Path(
        "CategoryTheory/Triangulated/WeakStabilityCondition/"
        "StabilityCondition/Families/Instances/AlgebraicGeometry/"
        "SemistableLocus.lean"
    ),
    pathlib.Path(
        "CategoryTheory/Triangulated/WeakStabilityCondition/"
        "StabilityCondition/Families/Instances/AlgebraicGeometry/"
        "RelativeHarderNarasimhan.lean"
    ),
    pathlib.Path(
        "CategoryTheory/Triangulated/WeakStabilityCondition/"
        "StabilityCondition/Families/Instances/AlgebraicGeometry/FiniteType.lean"
    ),
    pathlib.Path(
        "CategoryTheory/Triangulated/WeakStabilityCondition/"
        "StabilityCondition/Symmetry/Autoequivalence/Instances/"
        "AlgebraicGeometry/FourierMukai.lean"
    ),
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


def is_geometry_instance_import(module: str) -> bool:
    """Whether ``module`` is an algebraic-geometric categorical bridge."""

    parts = module.split(".")
    return (
        module in GEOMETRY_INSTANCE_UMBRELLAS
        or (
            len(parts) >= 3
            and parts[:2] == ["DerivedAlgGeo", GENERIC_OWNER]
            and has_geometry_instances_segment(parts[2:])
        )
    )


def is_geometry_source(relative: pathlib.PurePath) -> bool:
    """Whether ``relative`` is owned by AlgebraicGeometry."""

    return bool(relative.parts) and relative.parts[0] == GEOMETRY_OWNER


def collect_geometry_reverse_edges(
    source_root: pathlib.Path, pattern: str = "*.lean"
) -> list[tuple[str, int, str]]:
    """Collect algebraic-geometry imports of categorical instance leaves.

    Source names are relative to ``source_root`` so the same scanner can run
    against both the repository and the known-answer fixture trees.
    """

    edges: list[tuple[str, int, str]] = []
    for path in sorted(source_root.rglob(pattern)):
        relative = path.relative_to(source_root)
        if not is_geometry_source(relative):
            continue
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), 1
        ):
            match = IMPORT.match(line)
            if match is not None and is_geometry_instance_import(match.group(1)):
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
            not is_geometry_source(source_path)
            or not is_geometry_instance_import(module)
        ):
            failures.append(
                f"{REVERSE_EDGE_ALLOWLIST.relative_to(ROOT)}:{line_number}: "
                "entry is outside the guarded geometry-to-instance boundary"
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
            "DerivedAlgGeo.CategoryTheory.Triangulated."
            "WeakStabilityCondition.StabilityCondition.Families."
            "Instances.AlgebraicGeometry.SemistableLocus",
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

    for module, (retired_path, canonical_owner) in RETIRED_IMPORT_SHIMS.items():
        if retired_path.exists():
            failures.append(
                f"retired import shim {retired_path.relative_to(ROOT)} was restored; "
                f"consumers must import {canonical_owner}"
            )
        for path, modules in imports_by_path.items():
            if module in modules:
                failures.append(
                    f"{path.relative_to(ROOT)}: imports retired shim {module}"
                )

    census_path = ROOT / "scripts" / "StabilityConditionCensus.lean"
    census_imports = {
        match.group(1)
        for line in census_path.read_text(encoding="utf-8").splitlines()
        if (match := IMPORT.match(line)) is not None
    }
    missing_census_imports = CENSUS_OWNER_IMPORTS - census_imports
    if missing_census_imports:
        failures.append(
            f"{census_path.relative_to(ROOT)}: missing canonical owner imports "
            f"{sorted(missing_census_imports)}"
        )
    retired_census_imports = set(RETIRED_IMPORT_SHIMS) & census_imports
    if retired_census_imports:
        failures.append(
            f"{census_path.relative_to(ROOT)}: imports retired compatibility "
            f"modules {sorted(retired_census_imports)}"
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

    retired_geometric_stability_root = (
        SOURCE_ROOT / "AlgebraicGeometry" / "StabilityCondition"
    )
    retired_geometric_stability_umbrella = (
        retired_geometric_stability_root.with_suffix(".lean")
    )
    if (
        retired_geometric_stability_root.exists()
        or retired_geometric_stability_umbrella.exists()
    ):
        failures.append(
            "retired AlgebraicGeometry/StabilityCondition path restored; "
            "geometric objects belong to their geometric owner and adapters "
            "belong to categorical Instances/AlgebraicGeometry leaves"
        )

    generic_stacks_root = SOURCE_ROOT / "CategoryTheory" / "Sites"
    generic_stack_sources = (
        generic_stacks_root / "StackInGroupoids.lean",
        generic_stacks_root / "StackInGroupoids" / "Discrete.lean",
        generic_stacks_root / "StackInGroupoids" / "Morphism.lean",
    )
    for generic_stacks_source in generic_stack_sources:
        if not generic_stacks_source.is_file():
            failures.append(
                f"generic stack module missing: {generic_stacks_source.relative_to(ROOT)}"
            )
            continue
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

    geometric_representable_stack = (
        SOURCE_ROOT / "AlgebraicGeometry" / "Stacks" / "Representable.lean"
    )
    geometric_representable_text = geometric_representable_stack.read_text(
        encoding="utf-8"
    )
    for generic_name in (
        "discretePseudofunctor",
        "discretePseudofunctor_isStack",
        "stackInGroupoidsOfSheaf",
        "StackMorphism",
    ):
        if re.search(
            rf"^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure|class)\s+"
            rf"{generic_name}\b",
            geometric_representable_text,
            re.MULTILINE,
        ):
            failures.append(
                f"{geometric_representable_stack.relative_to(ROOT)}: generic "
                f"stack declaration {generic_name} returned to geometry"
            )

    generic_families_source_root = (
        SOURCE_ROOT / "CategoryTheory" / "Triangulated" / "Families"
    )
    for module in ("BaseChange",):
        path = generic_families_source_root / f"{module}.lean"
        text = path.read_text(encoding="utf-8")
        if f"namespace {GENERIC_FAMILIES_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: generic family declarations must "
                f"use namespace {GENERIC_FAMILIES_NAMESPACE}"
            )

    generic_moduli_root = SOURCE_ROOT / "CategoryTheory" / "Moduli"
    generic_moduli_sources = (
        SOURCE_ROOT / "CategoryTheory" / "Moduli.lean",
        generic_moduli_root / "Boundedness.lean",
    )
    for path in generic_moduli_sources:
        if not path.is_file():
            failures.append(
                f"generic moduli module missing: {path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        if path.name == "Boundedness.lean" and not re.search(
            rf"^namespace {GENERIC_MODULI_NAMESPACE}$", text, re.MULTILINE
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: generic moduli declarations must "
                f"use namespace {GENERIC_MODULI_NAMESPACE}"
            )
        if re.search(
            r"(?:^import DerivedAlgGeo\.AlgebraicGeometry|"
            r"^import DerivedAlgGeo\.CategoryTheory\.Triangulated\."
            r"WeakStabilityCondition|^namespace AlgebraicGeometry)",
            text,
            re.MULTILINE,
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: generic moduli infrastructure "
                "depends on a geometric or stability-specific consumer"
            )

    generic_pseudofunctor_root = SOURCE_ROOT / "CategoryTheory" / "Pseudofunctor"
    generic_subprestack_sources = (
        SOURCE_ROOT / "CategoryTheory" / "Pseudofunctor.lean",
        generic_pseudofunctor_root / "ObjectProperty.lean",
        generic_pseudofunctor_root / "ObjectProperty" /
            "UniversallyStable.lean",
    )
    for path in generic_subprestack_sources:
        if not path.is_file():
            failures.append(
                f"generic subprestack module missing: {path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        if re.search(
            r"(?:^import (?:DerivedAlgGeo|Mathlib)\.AlgebraicGeometry|"
            r"^import DerivedAlgGeo\.CategoryTheory\.Triangulated\."
            r"WeakStabilityCondition|^namespace AlgebraicGeometry)",
            text,
            re.MULTILINE,
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: generic subprestack infrastructure "
                "depends on a geometric or stability-specific consumer"
            )

    pseudofunctor_transport = (
        generic_pseudofunctor_root / "Transport.lean"
    )
    if not pseudofunctor_transport.is_file():
        failures.append(
            "generic pseudofunctor transport root missing: "
            f"{pseudofunctor_transport.relative_to(ROOT)}"
        )
    else:
        transport_text = pseudofunctor_transport.read_text(encoding="utf-8")
        if "namespace CategoryTheory.Pseudofunctor" not in transport_text:
            failures.append(
                f"{pseudofunctor_transport.relative_to(ROOT)}: equivalence "
                "transport must use the pseudofunctor namespace"
            )
        for required_name in (
            "equivalenceTransportFunctor",
            "equivalenceTransportCompIso",
            "equivalenceTransportIdIso",
            "equivalenceTransport_associativity",
            "equivalenceTransport_leftUnitality",
            "equivalenceTransport_rightUnitality",
        ):
            if required_name not in transport_text:
                failures.append(
                    f"{pseudofunctor_transport.relative_to(ROOT)}: missing "
                    f"transport declaration {required_name}"
                )
        if re.search(
            r"^import (?:DerivedAlgGeo|Mathlib)\.AlgebraicGeometry",
            transport_text,
            re.MULTILINE,
        ):
            failures.append(
                f"{pseudofunctor_transport.relative_to(ROOT)}: generic "
                "pseudofunctor transport imports a geometric consumer"
            )

    transport_module = (
        "DerivedAlgGeo.CategoryTheory.Pseudofunctor.Transport"
    )
    transport_consumers = (
        SOURCE_ROOT / "AlgebraicGeometry" / "DerivedCategory" / "Dqc" /
            "AffineKProjectiveDerivedPseudofunctor.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "DerivedCategory" / "Dqc" /
            "AffineGeometricPseudofunctor.lean",
    )
    for path in transport_consumers:
        if transport_module not in imports_by_path[path]:
            failures.append(
                f"{path.relative_to(ROOT)}: affine pseudofunctor consumer must "
                "import the generic transport root directly"
            )

    geometric_source_root = SOURCE_ROOT / "AlgebraicGeometry"
    local_transport_declaration = re.compile(
        r"^(?:private\s+)?(?:def|theorem)\s+"
        r"(?:qhTransport|equivalenceTransport)"
        r"(?:Functor|CompIso|IdIso|_associativity|_leftUnitality|_rightUnitality)\b",
        re.MULTILINE,
    )
    for path in sorted(geometric_source_root.rglob("*.lean")):
        if local_transport_declaration.search(path.read_text(encoding="utf-8")):
            failures.append(
                f"{path.relative_to(ROOT)}: geometric consumer restored a "
                "local copy of pseudofunctor equivalence transport"
            )

    geometric_moduli_root = SOURCE_ROOT / "AlgebraicGeometry" / "Moduli"
    relative_perfect_selector = (
        geometric_moduli_root / "PerfectComplex" / "Boundedness.lean"
    )
    relative_perfect_subprestack = (
        geometric_moduli_root / "PerfectComplex" /
            "AffineFamilyRelativePerfectPseudofunctor.lean"
    )
    selector_text = relative_perfect_selector.read_text(encoding="utf-8")
    for required_fragment in (
        "structure RelativePerfectModuliSelector",
        "familyLocus (T : SchemeBaseChange S)",
        "geometricLocus (T : SchemeBaseChange S)",
        "familyLocus_iso (T : SchemeBaseChange S)",
        "geometricLocus_iso (T : SchemeBaseChange S)",
    ):
        if required_fragment not in selector_text:
            failures.append(
                f"{relative_perfect_selector.relative_to(ROOT)}: fiberwise "
                f"moduli selector is missing {required_fragment!r}"
            )
    if "subfunctor" in selector_text:
        failures.append(
            f"{relative_perfect_selector.relative_to(ROOT)}: an indexed "
            "isomorphism-closed selector must not be described as a subfunctor"
        )

    retired_selector_name = "RelativePerfectModuliSubproblem"
    for path in sorted(SOURCE_ROOT.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        if retired_selector_name in text:
            failures.append(
                f"{path.relative_to(ROOT)}: retired fiberwise selector name "
                f"{retired_selector_name} restored"
            )
        if path.is_relative_to(geometric_moduli_root) and re.search(
            r"(?:structure|class|def|abbrev)\s+\w*Subprestack\b", text
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: geometric moduli defines a "
                "competing Subprestack carrier"
            )
        if (
            path.is_relative_to(geometric_moduli_root)
            and re.search(r"\)\.fullsubcategory\b", text)
            and path != relative_perfect_subprestack
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: geometric moduli constructs a "
                "sub-pseudofunctor outside the reviewed restriction-stable leaf"
            )

    subprestack_import = (
        "DerivedAlgGeo.CategoryTheory.Pseudofunctor.ObjectProperty."
        "UniversallyStable"
    )
    if subprestack_import not in imports_by_path[relative_perfect_subprestack]:
        failures.append(
            f"{relative_perfect_subprestack.relative_to(ROOT)}: genuine "
            "geometric subprestack must import the generic object-property root"
        )
    relative_perfect_subprestack_text = relative_perfect_subprestack.read_text(
        encoding="utf-8"
    )
    for required_fragment in (
        "Pseudofunctor.ObjectProperty.universallyStable",
        "Pseudofunctor.ObjectProperty.IsClosedUnderMapObj",
        ".fullsubcategory",
    ):
        if required_fragment not in relative_perfect_subprestack_text:
            failures.append(
                f"{relative_perfect_subprestack.relative_to(ROOT)}: genuine "
                f"subprestack is missing canonical step {required_fragment!r}"
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

    triangulated_family_source = (
        SOURCE_ROOT / "CategoryTheory" / "Triangulated" / "Families" /
        "BaseChange.lean"
    )
    triangulated_family_text = triangulated_family_source.read_text(
        encoding="utf-8"
    )
    for required_fragment in (
        "fibers : Pseudofunctor (LocallyDiscrete Bᵒᵖ) Cat",
        "def pullIdIso",
        "def pullCompIso",
        "def ofFunctor",
        "fibers := fibers.toPseudofunctor'",
    ):
        if required_fragment not in triangulated_family_text:
            failures.append(
                f"{triangulated_family_source.relative_to(ROOT)}: "
                "pseudofunctorial triangulated-family root is missing "
                f"{required_fragment!r}"
            )
    if re.search(
        r"^\s*fibers\s*:\s*Functor\s+Bᵒᵖ\s+Cat",
        triangulated_family_text,
        re.MULTILINE,
    ):
        failures.append(
            f"{triangulated_family_source.relative_to(ROOT)}: canonical "
            "triangulated families must not regress to a strict functor root"
        )
    prestability_base_change = (
        SOURCE_ROOT / "CategoryTheory" / "Triangulated" /
        "WeakStabilityCondition" / "StabilityCondition" / "Families" /
        "PreStabilityBaseChange.lean"
    )
    prestability_base_change_text = prestability_base_change.read_text(
        encoding="utf-8"
    )
    for required_fragment in (
        "preimageData_pullComp",
        "F.pullCompIso f g",
        "preimage_pullComp",
    ):
        if required_fragment not in prestability_base_change_text:
            failures.append(
                f"{prestability_base_change.relative_to(ROOT)}: stability "
                "consumer must use pseudofunctor composition coherence via "
                f"{required_fragment!r}"
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

    retired_weak_compatibility = strong_stability_root / "WeakCompatibility"
    if retired_weak_compatibility.exists() or retired_weak_compatibility.with_suffix(
        ".lean"
    ).exists():
        failures.append(
            "the retired StabilityCondition/WeakCompatibility adapter tree was "
            "restored; ordinary prestability must expose its weak parent structurally"
        )
    strong_prestability_source = (
        strong_stability_root / "Foundation" / "PreStabilityCondition.lean"
    )
    strong_prestability_text = strong_prestability_source.read_text(encoding="utf-8")
    if not re.search(
        r"extends\s+toWeak\s*:\s*"
        r"WeakStabilityCondition\.WeakPreStabilityCondition",
        strong_prestability_text,
    ):
        failures.append(
            f"{strong_prestability_source.relative_to(ROOT)}: ordinary "
            "prestability must structurally extend WeakPreStabilityCondition"
        )

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

    strong_deformation_source_root = (
        strong_stability_root / "Foundation" / "Deformation"
    )
    for module in (
        "ChargePerturbation",
        "FiniteLengthHN",
        "FirstStrictSES",
        "LocalFiniteness",
        "NearIdentity",
        "PhaseArithmetic",
        "PullbackCokernel",
        "RelativePhase",
        "SkewedStability",
        "StabilitySeminorm",
        "StabilityTopology",
        "StrictMDQ",
    ):
        path = strong_deformation_source_root / f"{module}.lean"
        text = path.read_text(encoding="utf-8")
        if f"namespace {STRONG_DEFORMATION_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: Bridgeland deformation helpers "
                f"must use namespace {STRONG_DEFORMATION_NAMESPACE}"
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
        f"namespace {CATEGORICAL_FOURIER_MUKAI_NAMESPACE}"
        not in strong_symmetry_bridge_text
    ):
        failures.append(
            f"{strong_symmetry_bridge.relative_to(ROOT)}: Bridgeland "
            "Fourier--Mukai extensions must use the canonical kernel "
            f"namespace {CATEGORICAL_FOURIER_MUKAI_NAMESPACE}"
        )

    for relative in (
        pathlib.Path("Phase") / "NormalizedShift.lean",
        pathlib.Path("Symmetry") / "GLTilde" / "Basic.lean",
        pathlib.Path("Symmetry") / "GLTilde" / "Action" / "Slicing.lean",
        pathlib.Path("Symmetry")
        / "Autoequivalence"
        / "Stability"
        / "ClassMap.lean",
        pathlib.Path("Metric") / "Isometry" / "Full.lean",
    ):
        path = strong_stability_root / relative
        text = path.read_text(encoding="utf-8")
        if f"namespace {STRONG_GROUP_ACTION_NAMESPACE}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: Bridgeland group-action "
                f"declarations must use namespace {STRONG_GROUP_ACTION_NAMESPACE}"
            )

    review_group_action_text = RESTATE_GROUP_ACTION_NAMES.read_text(
        encoding="utf-8"
    )
    review_aliases = re.findall(
        r"^alias (\w+) :=\s*\n?\s*(\S+)",
        review_group_action_text,
        re.MULTILINE,
    )
    expected_review_aliases = [
        ("GLTilde", f"{STRONG_GROUP_ACTION_NAMESPACE}.GLTilde"),
        ("group", f"{STRONG_GROUP_ACTION_NAMESPACE}.GLTilde.group"),
        ("AutPairQuot", f"{STRONG_GROUP_ACTION_NAMESPACE}.AutPairQuot"),
        ("group", f"{STRONG_GROUP_ACTION_NAMESPACE}.AutPairQuot.group"),
        (
            "mulAction",
            f"{STRONG_GROUP_ACTION_NAMESPACE}.AutPairQuot.mulAction",
        ),
        (
            "gltildeSlicingMulAction",
            f"{STRONG_GROUP_ACTION_NAMESPACE}.gltildeSlicingMulAction",
        ),
    ]
    if review_aliases != expected_review_aliases:
        failures.append(
            f"{RESTATE_GROUP_ACTION_NAMES.relative_to(ROOT)}: expected "
            f"exactly the six restatement-only aliases {expected_review_aliases}, "
            f"found {review_aliases}"
        )
    if review_group_action_text.count("@[deprecated") != len(
        expected_review_aliases
    ):
        failures.append(
            f"{RESTATE_GROUP_ACTION_NAMES.relative_to(ROOT)}: every "
            "restatement-only alias must be deprecated"
        )
    review_group_action_module = "RestateHistoricalNames"
    restate_executable = ROOT / "exe" / "Restate.lean"
    restate_text = restate_executable.read_text(encoding="utf-8")
    restate_imports = [
        match.group(1)
        for line in restate_text.splitlines()
        if (match := IMPORT.match(line)) is not None
    ]
    if review_group_action_module not in restate_imports:
        failures.append(
            "exe/Restate.lean must import the executable-only GroupAction "
            "human-review bridge"
        )
    if not re.search(
        r"additionalRoots\s*:=\s*\[[^\]]*`RestateHistoricalNames",
        restate_text,
        re.DOTALL,
    ):
        failures.append(
            "exe/Restate.lean must load RestateHistoricalNames into the "
            "fresh restatement environment"
        )
    tracked_lean_paths = list(SOURCE_ROOT.rglob("*.lean"))
    tracked_lean_paths.extend((ROOT / "scripts").rglob("*.lean"))
    tracked_lean_paths.extend((ROOT / "exe").rglob("*.lean"))
    tracked_lean_paths.extend(ROOT.glob("*.lean"))
    for path in sorted(set(tracked_lean_paths)):
        path_text = path.read_text(encoding="utf-8")
        modules = [
            match.group(1)
            for line in path_text.splitlines()
            if (match := IMPORT.match(line)) is not None
        ]
        if path != restate_executable and review_group_action_module in modules:
            failures.append(
                f"{path.relative_to(ROOT)}: only the restatement executable "
                "may import the GroupAction human-review bridge"
            )
        if (
            path != RESTATE_GROUP_ACTION_NAMES
            and RETIRED_STRONG_GROUP_ACTION_NAMESPACE in path_text
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: only the executable restatement "
                "bridge may mention the retired GroupAction namespace"
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

    generic_derived_root = (
        SOURCE_ROOT / "CategoryTheory" / "Triangulated" / "DerivedCategory"
    )
    generic_derived_sources = (
        generic_derived_root / "TStructure.lean",
        generic_derived_root / "ExactFunctor.lean",
        generic_derived_root / "Homology.lean",
        generic_derived_root / "KProjective.lean",
        generic_derived_root / "BoundedAboveProjective.lean",
        generic_derived_root / "BoundedAboveProjective" / "Unitality.lean",
    )
    for path in generic_derived_sources:
        if not path.is_file():
            failures.append(
                f"generic derived-category module missing: {path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        if not re.search(
            rf"^namespace {GENERIC_DERIVED_NAMESPACE}$", text, re.MULTILINE
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: generic derived-category "
                f"declarations must use namespace {GENERIC_DERIVED_NAMESPACE}"
            )
        if "namespace AlgebraicGeometry" in text:
            failures.append(
                f"{path.relative_to(ROOT)}: generic derived-category module "
                "uses an AlgebraicGeometry declaration namespace"
            )

    derived_opposite_source = generic_derived_root / "Opposite.lean"
    derived_linear_dual_source = generic_derived_root / "LinearDual.lean"
    for path in (derived_opposite_source, derived_linear_dual_source):
        if not path.is_file():
            failures.append(
                f"generic derived-duality module missing: {path.relative_to(ROOT)}"
            )
    if derived_opposite_source.is_file():
        opposite_text = derived_opposite_source.read_text(encoding="utf-8")
        for required_fragment in (
            "namespace CategoryTheory.DerivedCategory",
            "structure OppositeComparison",
            "equivalence : (DerivedCategory C)ᵒᵖ ≌ DerivedCategory Cᵒᵖ",
        ):
            if required_fragment not in opposite_text:
                failures.append(
                    f"{derived_opposite_source.relative_to(ROOT)}: generic "
                    f"derived/opposite root is missing {required_fragment!r}"
                )
    if derived_linear_dual_source.is_file():
        linear_dual_text = derived_linear_dual_source.read_text(encoding="utf-8")
        opposite_import = (
            "DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.Opposite"
        )
        if opposite_import not in imports_by_path[derived_linear_dual_source]:
            failures.append(
                f"{derived_linear_dual_source.relative_to(ROOT)}: exact linear "
                f"duality must import its generic opposite root {opposite_import}"
            )
        for required_fragment in (
            "noncomputable instance moduleHasDerivedCategory",
            "noncomputable instance oppositeModuleHasDerivedCategory",
            "noncomputable def derivedLinearDualFunctor",
            "noncomputable def derivedLinearDualFromOpposite",
            "noncomputable def derivedLinearDualShift",
            "CategoryTheory.DerivedCategory.OppositeComparison",
        ):
            if required_fragment not in linear_dual_text:
                failures.append(
                    f"{derived_linear_dual_source.relative_to(ROOT)}: categorical "
                    f"linear-dual specialization is missing {required_fragment!r}"
                )
        if "AlgebraicGeometry" in linear_dual_text:
            failures.append(
                f"{derived_linear_dual_source.relative_to(ROOT)}: generic exact "
                "linear duality mentions algebraic geometry"
            )

    coherent_owner_module = (
        "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent"
    )
    linear_dual_module = (
        "DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.LinearDual"
    )
    canonical_duality_source = (
        SOURCE_ROOT / "AlgebraicGeometry" / "Duality" / "Canonical" /
            "Derived.lean"
    )
    serre_cohomology_source = (
        SOURCE_ROOT / "AlgebraicGeometry" / "Duality" / "Serre" /
            "Cohomology.lean"
    )
    if coherent_owner_module not in imports_by_path[canonical_duality_source]:
        failures.append(
            f"{canonical_duality_source.relative_to(ROOT)}: canonical duality "
            f"must import coherent-derived owner {coherent_owner_module}"
        )
    for required_import in (coherent_owner_module, linear_dual_module):
        if required_import not in imports_by_path[serre_cohomology_source]:
            failures.append(
                f"{serre_cohomology_source.relative_to(ROOT)}: Serre duality "
                f"must import canonical source {required_import}"
            )
    for path in (canonical_duality_source, serre_cohomology_source):
        text = path.read_text(encoding="utf-8")
        for forbidden_fragment in (
            "local instance coherentHasDerivedCategory",
            "local instance moduleHasDerivedCategory",
            "ModuleCat.DerivedOppositeComparison",
        ):
            if forbidden_fragment in text:
                failures.append(
                    f"{path.relative_to(ROOT)}: geometric duality restored "
                    f"private derived-category binding {forbidden_fragment!r}"
                )
    canonical_duality_text = canonical_duality_source.read_text(encoding="utf-8")
    if "DerivedCategory.SchemeCoherentDerivedCategory" not in canonical_duality_text:
        failures.append(
            f"{canonical_duality_source.relative_to(ROOT)}: canonical dualizing "
            "complex must use the coherent-derived owner"
        )
    serre_cohomology_text = serre_cohomology_source.read_text(encoding="utf-8")
    for required_fragment in (
        "SchemeCoherentDerivedCategory X.toVariety.toScheme",
        "CategoryTheory.DerivedCategory.OppositeComparison",
        "ModuleCat.derivedLinearDualShift",
    ):
        if required_fragment not in serre_cohomology_text:
            failures.append(
                f"{serre_cohomology_source.relative_to(ROOT)}: Serre-duality "
                f"consumer is missing {required_fragment!r}"
            )
    for path in sorted((SOURCE_ROOT / "AlgebraicGeometry").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for declaration in (
            "linearDualFunctor",
            "derivedLinearDualFunctor",
            "DerivedOppositeComparison",
        ):
            if re.search(
                rf"^(?:noncomputable\s+)?(?:def|structure)\s+{declaration}\b",
                text,
                re.MULTILINE,
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}: restored generic derived-duality "
                    f"declaration {declaration} inside algebraic geometry"
                )

    generic_cech_root = SOURCE_ROOT / "CategoryTheory" / "Sites" / "Cech"
    generic_cohomology_sources = (
        SOURCE_ROOT / "CategoryTheory" / "Sites" / "Cech.lean",
        *sorted(generic_cech_root.glob("*.lean")),
        SOURCE_ROOT / "CategoryTheory" / "Simplicial.lean",
        SOURCE_ROOT / "CategoryTheory" / "Simplicial" /
            "ExtraCodegeneracy.lean",
        SOURCE_ROOT / "CategoryTheory" / "SpectralSequence" /
            "ExtendHomologyNaturality.lean",
        SOURCE_ROOT / "CategoryTheory" / "SpectralSequence" /
            "FilteredComplexSpectralObject.lean",
        SOURCE_ROOT / "CategoryTheory" / "SpectralSequence" /
            "FilteredTotalComplex.lean",
        SOURCE_ROOT / "CategoryTheory" / "SpectralSequence" /
            "FilteredTotalComplexAdjacent.lean",
        SOURCE_ROOT / "CategoryTheory" / "SpectralSequence" /
            "FilteredTotalComplexFirstPageDifferential.lean",
        SOURCE_ROOT / "CategoryTheory" / "SpectralSequence" /
            "TotalFlipNaturality.lean",
        SOURCE_ROOT / "CategoryTheory" / "SpectralSequence" /
            "TotalQuasiIso.lean",
        generic_derived_root / "Ext" / "Adjunction.lean",
        generic_derived_root / "Ext" / "DimensionShift.lean",
        generic_derived_root / "Ext" / "InjectiveResolutionNaturality.lean",
    )
    for path in generic_cohomology_sources:
        if not path.is_file():
            failures.append(
                f"generic cohomology module missing: {path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        if re.search(
            r"(?:^import DerivedAlgGeo\.AlgebraicGeometry|"
            r"^namespace AlgebraicGeometry)",
            text,
            re.MULTILINE,
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: generic cohomological machinery "
                "depends on or declares algebraic geometry"
            )

    generic_bicategory_root = SOURCE_ROOT / "CategoryTheory" / "Bicategory"
    generic_limits_root = SOURCE_ROOT / "CategoryTheory" / "Limits"
    generic_abelian_root = SOURCE_ROOT / "CategoryTheory" / "Abelian"
    generic_sheaves_root = SOURCE_ROOT / "CategoryTheory" / "Sites" / "Sheaves"
    generic_foundation_sources = (
        SOURCE_ROOT / "CategoryTheory" / "Abelian.lean",
        SOURCE_ROOT / "CategoryTheory" / "Bicategory.lean",
        SOURCE_ROOT / "CategoryTheory" / "Limits.lean",
        SOURCE_ROOT / "CategoryTheory" / "Sites" / "Sheaves.lean",
        *sorted(generic_bicategory_root.rglob("*.lean")),
        *sorted(generic_limits_root.rglob("*.lean")),
        *sorted(generic_abelian_root.rglob("*.lean")),
        *sorted(generic_sheaves_root.rglob("*.lean")),
    )
    required_generic_foundations = (
        SOURCE_ROOT / "CategoryTheory" / "Bicategory.lean",
        generic_bicategory_root / "Basic.lean",
        generic_bicategory_root / "Adjunction.lean",
        generic_bicategory_root / "Adjunction" / "Basic.lean",
        generic_bicategory_root / "Adjunction" / "Cat.lean",
        SOURCE_ROOT / "CategoryTheory" / "Limits.lean",
        generic_limits_root / "Preserves.lean",
        generic_limits_root / "Preserves" / "Composition.lean",
        generic_limits_root / "Preserves" / "Reflective.lean",
        generic_abelian_root / "WeakSerre.lean",
        generic_sheaves_root / "ConstantPullback.lean",
        generic_sheaves_root / "CohomologyShortExact.lean",
        generic_sheaves_root / "CohomologyPushforward.lean",
        generic_sheaves_root / "Modules" / "Exactness.lean",
        generic_sheaves_root / "Modules" / "Presentation" / "Transport.lean",
        generic_sheaves_root / "Modules" / "Presentation" / "Finite.lean",
        SOURCE_ROOT / "Topology" / "Sheaves" / "CohomologyPushforward.lean",
    )
    for path in required_generic_foundations:
        if not path.is_file():
            failures.append(
                f"canonical categorical foundation missing: {path.relative_to(ROOT)}"
            )
    for path in generic_foundation_sources:
        if not path.is_file():
            failures.append(
                f"generic categorical umbrella missing: {path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        if re.search(
            r"(?:^import DerivedAlgGeo\.AlgebraicGeometry|"
            r"^namespace AlgebraicGeometry)",
            text,
            re.MULTILINE,
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: generic categorical "
                "infrastructure depends on or declares algebraic geometry"
            )

    bicategorical_cat = (
        generic_bicategory_root / "Adjunction" / "Cat.lean"
    )
    if bicategorical_cat.is_file() and "def bicategoricalEquiv" not in (
        bicategorical_cat.read_text(encoding="utf-8")
    ):
        failures.append(
            f"{bicategorical_cat.relative_to(ROOT)}: ordinary adjunctions must "
            "expose their equivalence with bicategorical adjunctions in Cat"
        )

    preserves_composition = (
        generic_limits_root / "Preserves" / "Composition.lean"
    )
    if preserves_composition.is_file():
        preserves_composition_text = preserves_composition.read_text(encoding="utf-8")
        if "namespace CategoryTheory.Limits" not in preserves_composition_text:
            failures.append(
                f"{preserves_composition.relative_to(ROOT)}: composition-only "
                "preservation must use the CategoryTheory.Limits namespace"
            )
        if "Mathlib.CategoryTheory.Adjunction" in "\n".join(
            imports_by_path[preserves_composition]
        ):
            failures.append(
                f"{preserves_composition.relative_to(ROOT)}: adjunction-free "
                "preservation imports an adjunction module"
            )

    preserves_reflective = (
        generic_limits_root / "Preserves" / "Reflective.lean"
    )
    if preserves_reflective.is_file():
        preserves_reflective_text = preserves_reflective.read_text(encoding="utf-8")
        if "namespace CategoryTheory.Adjunction" not in preserves_reflective_text:
            failures.append(
                f"{preserves_reflective.relative_to(ROOT)}: reflective "
                "preservation must extend Mathlib's ordinary Adjunction API"
            )
        if (
            "DerivedAlgGeo.CategoryTheory.Limits.Preserves.Composition"
            not in imports_by_path[preserves_reflective]
        ):
            failures.append(
                f"{preserves_reflective.relative_to(ROOT)}: reflective "
                "preservation must consume the adjunction-free composition root"
            )

    category_theory_umbrella = SOURCE_ROOT / "CategoryTheory.lean"
    for required_import in (
        "DerivedAlgGeo.CategoryTheory.Bicategory",
        "DerivedAlgGeo.CategoryTheory.Limits",
    ):
        if required_import not in imports_by_path[category_theory_umbrella]:
            failures.append(
                f"{category_theory_umbrella.relative_to(ROOT)}: missing "
                f"higher-categorical owner import {required_import}"
            )

    retired_generic_cohomology_paths = (
        SOURCE_ROOT / "CategoryTheory" / "ExtAdjunction.lean",
        SOURCE_ROOT / "CategoryTheory" / "ExtDimensionShift.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "SpectralSequence.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "SpectralSequence",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Derived" /
            "ExtResolutionNaturality.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "Differential.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "BasisComparison.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "Bicomplex.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "Comparison.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "ComplexNaturality.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "GlobalComparison.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "InitialPage.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "InjectiveAcyclic.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "SmallSiteResolution.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "TotalComparison.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Derived" /
            "FreeAbelianYonedaStalk.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Derived" /
            "InjectiveFlasque.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Simplicial.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Simplicial",
    )
    for path in retired_generic_cohomology_paths:
        if path.exists():
            failures.append(
                f"retired generic cohomology path restored: {path.relative_to(ROOT)}"
            )

    generic_declarations_retired_from_consumers = {
        SOURCE_ROOT / "AlgebraicGeometry" / "Modules" /
            "ExteriorPower.lean": (
                "namespace LinearMap\n",
                "namespace PresheafOfModules\n",
                "def topPowerset",
                "noncomputable def topExteriorFreeEquiv",
            ),
        SOURCE_ROOT / "AlgebraicGeometry" / "Divisors" /
            "Determinant.lean": (
                "namespace Module\n\nvariable (R",
            ),
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "Affine.lean": (
                "theorem cechComplex_exactAt_succ_of_isTerminal",
            ),
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "AffineBasisComparison.lean": (
                "namespace CategoryTheory\n",
            ),
        SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Finiteness" /
            "Boundedness.lean": (
                "namespace CategoryTheory.Sheaf\n",
            ),
    }
    for path, retired_fragments in generic_declarations_retired_from_consumers.items():
        text = path.read_text(encoding="utf-8")
        for fragment in retired_fragments:
            if fragment in text:
                failures.append(
                    f"{path.relative_to(ROOT)}: restored generic "
                    f"declaration fragment {fragment!r} in a geometric consumer"
                )

    localization_kernels = (
        SOURCE_ROOT / "Algebra" / "Module" / "Localization" / "Kernels.lean"
    )
    localization_umbrellas = {
        SOURCE_ROOT / "Algebra" / "Module" / "Localization.lean":
            "DerivedAlgGeo.Algebra.Module.Localization.Kernels",
        SOURCE_ROOT / "Algebra" / "Module.lean":
            "DerivedAlgGeo.Algebra.Module.Localization",
        SOURCE_ROOT / "Algebra.lean":
            "DerivedAlgGeo.Algebra.Module",
    }
    if not localization_kernels.is_file():
        failures.append(
            "canonical module-localization kernel owner is missing: "
            f"{localization_kernels.relative_to(ROOT)}"
        )
    else:
        localization_text = localization_kernels.read_text(encoding="utf-8")
        for fragment in (
            "def kerMap (a : M →ₗ",
            "theorem kerMap (a : M →ₗ",
            "theorem kernelMap {M M' N N' : ModuleCat",
            "theorem kernelNatTrans",
        ):
            if fragment not in localization_text:
                failures.append(
                    f"{localization_kernels.relative_to(ROOT)}: missing "
                    f"module-localization kernel declaration {fragment!r}"
                )
        if re.search(
            r"(?:^import DerivedAlgGeo\.AlgebraicGeometry|"
            r"^namespace AlgebraicGeometry)",
            localization_text,
            re.MULTILINE,
        ):
            failures.append(
                f"{localization_kernels.relative_to(ROOT)}: algebraic "
                "localization owner depends on or declares algebraic geometry"
            )

    for path, required_import in localization_umbrellas.items():
        if not path.is_file():
            failures.append(
                f"module-localization umbrella missing: {path.relative_to(ROOT)}"
            )
        elif required_import not in imports_by_path[path]:
            failures.append(
                f"{path.relative_to(ROOT)}: missing module-localization "
                f"umbrella import {required_import}"
            )

    coherent_kernel_consumer = (
        SOURCE_ROOT / "AlgebraicGeometry" / "CoherentSheaf" / "Abelian" /
            "Kernels.lean"
    )
    localization_import = "DerivedAlgGeo.Algebra.Module.Localization.Kernels"
    if localization_import not in imports_by_path[coherent_kernel_consumer]:
        failures.append(
            f"{coherent_kernel_consumer.relative_to(ROOT)}: coherent-sheaf "
            "kernels must import the algebraic localization owner directly"
        )
    coherent_kernel_text = coherent_kernel_consumer.read_text(encoding="utf-8")
    for fragment in (
        "def kerMap (a : M →ₗ",
        "theorem kerMap (a : M →ₗ",
        "theorem kernelMap {M M' N N' : ModuleCat",
        "theorem kernelNatTrans",
    ):
        if fragment in coherent_kernel_text:
            failures.append(
                f"{coherent_kernel_consumer.relative_to(ROOT)}: restored "
                f"generic module-localization declaration {fragment!r}"
            )

    graded_basis_owner = SOURCE_ROOT / "LinearAlgebra" / "GradedBasis.lean"
    numerical_graded_basis_consumer = (
        SOURCE_ROOT / "AlgebraicGeometry" / "Numerical" / "Core" /
            "GradedBasis.lean"
    )
    if not graded_basis_owner.is_file():
        failures.append(
            "canonical weighted-basis owner is missing: "
            f"{graded_basis_owner.relative_to(ROOT)}"
        )
    else:
        graded_basis_text = graded_basis_owner.read_text(encoding="utf-8")
        for fragment in (
            "namespace DerivedAlgGeo.LinearAlgebra",
            "def gradedPiece",
            "theorem gradedPiece_iSupIndep",
            "theorem gradedPiece_iSup_eq_top",
            "theorem gradedPiece_isInternal",
            "theorem gradedPiece_mul_mem",
        ):
            if fragment not in graded_basis_text:
                failures.append(
                    f"{graded_basis_owner.relative_to(ROOT)}: missing generic "
                    f"weighted-basis declaration {fragment!r}"
                )
        if re.search(
            r"(?:^import DerivedAlgGeo\.AlgebraicGeometry|"
            r"^namespace AlgebraicGeometry)",
            graded_basis_text,
            re.MULTILINE,
        ) or "NumericalRingData" in graded_basis_text:
            failures.append(
                f"{graded_basis_owner.relative_to(ROOT)}: weighted-basis owner "
                "depends on its geometric numerical consumer"
            )

    graded_basis_import = "DerivedAlgGeo.LinearAlgebra.GradedBasis"
    if graded_basis_import not in imports_by_path[numerical_graded_basis_consumer]:
        failures.append(
            f"{numerical_graded_basis_consumer.relative_to(ROOT)}: numerical "
            "constructor must import the generic weighted-basis owner directly"
        )
    numerical_graded_basis_text = numerical_graded_basis_consumer.read_text(
        encoding="utf-8"
    )
    if "def NumericalRingData.ofGradedBasis" not in numerical_graded_basis_text:
        failures.append(
            f"{numerical_graded_basis_consumer.relative_to(ROOT)}: missing "
            "geometric NumericalRingData consumer"
        )
    for declaration in (
        "gradedPiece",
        "mem_gradedPiece",
        "gradedPiece_eq_bot",
        "gradedPiece_iSupIndep",
        "gradedPiece_iSup_eq_top",
        "gradedPiece_isInternal",
        "gradedPiece_mul_mem",
    ):
        if re.search(
            rf"^(?:def|theorem)\s+{declaration}\b",
            numerical_graded_basis_text,
            re.MULTILINE,
        ):
            failures.append(
                f"{numerical_graded_basis_consumer.relative_to(ROOT)}: restored "
                f"generic weighted-basis declaration {declaration}"
            )

    graded_basis_umbrella = SOURCE_ROOT / "LinearAlgebra.lean"
    if graded_basis_import not in imports_by_path[graded_basis_umbrella]:
        failures.append(
            f"{graded_basis_umbrella.relative_to(ROOT)}: missing weighted-basis "
            "umbrella import"
        )

    div_monomial_owner = (
        SOURCE_ROOT / "Algebra" / "MvPolynomial" / "DivMonomial.lean"
    )
    laurent_projection_owner = (
        SOURCE_ROOT / "Algebra" / "MvPolynomial" / "LaurentProjection.lean"
    )
    if not div_monomial_owner.is_file():
        failures.append(
            "canonical multivariate monomial-division owner is missing: "
            f"{div_monomial_owner.relative_to(ROOT)}"
        )
    else:
        div_monomial_text = div_monomial_owner.read_text(encoding="utf-8")
        for fragment in (
            "namespace Finsupp",
            "theorem degree_eq_weight_one_apply",
            "namespace MvPolynomial",
            "theorem isHomogeneous_divMonomial",
            "theorem divMonomial_monomial_mul_add",
            "theorem divMonomial_monomial_mul_comm",
            "theorem divMonomial_pow_mul",
            "theorem divMonomial_single_mem_homogeneousSubmodule",
            "theorem X_pow_mul_divMonomial_single",
            "theorem X_pow_dvd_of_cross_mul",
        ):
            if fragment not in div_monomial_text:
                failures.append(
                    f"{div_monomial_owner.relative_to(ROOT)}: missing generic "
                    f"monomial-division declaration {fragment!r}"
                )
        if re.search(
            r"(?:^import DerivedAlgGeo\.AlgebraicGeometry|"
            r"^namespace AlgebraicGeometry)",
            div_monomial_text,
            re.MULTILINE,
        ):
            failures.append(
                f"{div_monomial_owner.relative_to(ROOT)}: algebraic "
                "monomial-division owner depends on geometry"
            )

    div_monomial_import = "DerivedAlgGeo.Algebra.MvPolynomial.DivMonomial"
    if div_monomial_import not in imports_by_path[laurent_projection_owner]:
        failures.append(
            f"{laurent_projection_owner.relative_to(ROOT)}: Laurent "
            "projection must import the algebraic monomial-division owner directly"
        )
    for path in sorted((SOURCE_ROOT / "AlgebraicGeometry" / "Proj").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for declaration in (
            "degree_eq_weight_one_apply",
            "isHomogeneous_divMonomial",
            "divMonomial_monomial_mul_add",
            "divMonomial_monomial_mul_comm",
            "divMonomial_pow_mul",
            "divMonomial_single_mem_homogeneousSubmodule",
            "X_pow_mul_divMonomial_single",
            "X_pow_dvd_of_cross_mul",
        ):
            if re.search(
                rf"^(?:def|theorem)\s+{declaration}\b", text, re.MULTILINE
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}: restored generic "
                    f"monomial-division declaration {declaration}"
                )

    div_monomial_umbrellas = {
        SOURCE_ROOT / "Algebra" / "MvPolynomial.lean": div_monomial_import,
        SOURCE_ROOT / "Algebra.lean": "DerivedAlgGeo.Algebra.MvPolynomial",
    }
    for path, required_import in div_monomial_umbrellas.items():
        if not path.is_file():
            failures.append(
                f"monomial-division umbrella missing: {path.relative_to(ROOT)}"
            )
        elif required_import not in imports_by_path[path]:
            failures.append(
                f"{path.relative_to(ROOT)}: missing monomial-division "
                f"umbrella import {required_import}"
            )

    graded_module_root = SOURCE_ROOT / "Algebra" / "Module" / "GradedModule"
    graded_module_owners = {
        graded_module_root / "Localization.lean": (
            "namespace GradedModule",
            "abbrev DegreeZeroLocalization",
            "structure GradedLinearMap",
        ),
        graded_module_root / "Shift.lean": (
            "namespace GradedModule",
            "def natShift",
            "def intShift",
            "theorem isDegreeZero_intShift_intShift_iff",
        ),
        graded_module_root / "TwistLocalization.lean": (
            "namespace GradedModule",
            "namespace DegreeZeroLocalization",
            "noncomputable def intShiftZeroLinearEquiv",
        ),
        graded_module_root / "PowersCongr.lean": (
            "namespace GradedModule.DegreeZeroLocalization",
            "noncomputable def powersCongr",
            "theorem powersCongr_faceMap",
        ),
    }
    for path, fragments in graded_module_owners.items():
        if not path.is_file():
            failures.append(
                f"canonical graded-module algebra owner is missing: "
                f"{path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        for fragment in fragments:
            if fragment not in text:
                failures.append(
                    f"{path.relative_to(ROOT)}: missing graded-module "
                    f"declaration {fragment!r}"
                )
        if re.search(
            r"(?:^import DerivedAlgGeo\.AlgebraicGeometry|"
            r"^namespace AlgebraicGeometry)",
            text,
            re.MULTILINE,
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: graded-module algebra owner "
                "depends on or declares algebraic geometry"
            )

    laurent_algebra_owners = {
        SOURCE_ROOT / "Algebra" / "Finsupp" / "LaurentExponent.lean": (
            "namespace Finsupp",
            "def natToIntExponent",
            "def laurentExponent",
            "theorem degree_laurentExponent_int",
        ),
        SOURCE_ROOT / "Algebra" / "MvPolynomial" / "Grading.lean": (
            "namespace MvPolynomial",
            "abbrev polynomialGrading",
            "theorem polynomialVariable_adjoin_eq_top",
        ),
        SOURCE_ROOT / "Algebra" / "MvPolynomial" / "LaurentBasis.lean": (
            "namespace MvPolynomial",
            "def IsPolynomialTwist",
            "theorem awayMk_monomial_eq_iff_laurentExponent",
            "theorem exists_sum_awayMk_monomial",
            "theorem sum_awayMk_monomial_eq_zero_iff",
        ),
        laurent_projection_owner: (
            "namespace MvPolynomial",
            "structure AwayRep",
            "noncomputable def signProjectionHom",
            "theorem signProjection_laurentFace_comm",
        ),
        SOURCE_ROOT / "Algebra" / "MvPolynomial" / "LaurentBlock.lean": (
            "namespace MvPolynomial",
            "noncomputable def intNegSupport",
            "noncomputable def blockProjHom",
            "theorem laurentFace_blockProj",
        ),
        SOURCE_ROOT / "Algebra" / "MvPolynomial" / "LaurentHomotopy.lean": (
            "namespace MvPolynomial",
            "noncomputable def laurentHomotopy",
            "theorem laurentHomotopy_laurentFace_comm",
        ),
        SOURCE_ROOT / "Algebra" / "MvPolynomial" / "LaurentFinite.lean": (
            "namespace MvPolynomial",
            "noncomputable def polynomialToHomogeneousLocalization",
            "theorem fg_blockSpan",
        ),
    }
    for path, fragments in laurent_algebra_owners.items():
        if not path.is_file():
            failures.append(
                f"canonical Laurent algebra owner is missing: "
                f"{path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        for fragment in fragments:
            if fragment not in text:
                failures.append(
                    f"{path.relative_to(ROOT)}: missing Laurent algebra "
                    f"declaration {fragment!r}"
                )
        if re.search(
            r"(?:^import DerivedAlgGeo\.AlgebraicGeometry|"
            r"^namespace AlgebraicGeometry)",
            text,
            re.MULTILINE,
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: Laurent algebra owner depends "
                "on or declares algebraic geometry"
            )

    polynomial_cech_root = SOURCE_ROOT / "Algebra" / "MvPolynomial" / "Cech"
    polynomial_cech_owners = {
        polynomial_cech_root / "Basic.lean": (
            "namespace MvPolynomial",
            "def polynomialVariableCechDenominator",
            "def polynomialVariableFraction",
            "noncomputable def polynomialVariableCechFace",
            "noncomputable def cechFace",
            "noncomputable def cechCofactor",
        ),
        polynomial_cech_root / "Homotopy.lean": (
            "namespace MvPolynomial",
            "noncomputable def tupleExponent",
            "noncomputable def cechBlockProj",
            "noncomputable def cechHomotopy",
        ),
        polynomial_cech_root / "Primitive.lean": (
            "namespace MvPolynomial",
            "noncomputable def cechBlockPrimitive",
            "noncomputable def cechPrimitive",
            "theorem cechPrimitive_isPrimitive",
        ),
        polynomial_cech_root / "Finite.lean": (
            "namespace MvPolynomial",
            "noncomputable def cechBlockSpan",
            "theorem fg_cechBlockSpan",
            "instance module_finite_pi_cechBlockSpan",
        ),
    }
    for path, fragments in polynomial_cech_owners.items():
        if not path.is_file():
            failures.append(
                f"canonical polynomial Čech algebra owner is missing: "
                f"{path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        for fragment in fragments:
            if fragment not in text:
                failures.append(
                    f"{path.relative_to(ROOT)}: missing polynomial Čech "
                    f"declaration {fragment!r}"
                )
        if re.search(
            r"(?:^import DerivedAlgGeo\.AlgebraicGeometry|"
            r"^namespace AlgebraicGeometry)",
            text,
            re.MULTILINE,
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: polynomial Čech algebra owner "
                "depends on or declares algebraic geometry"
            )

    retired_proj_algebra_paths = (
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "GradedLocalization.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "Shift.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "TwistLocalization.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "LaurentBasis.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "LaurentProjection.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "LaurentBlock.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "LaurentHomotopy.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "LaurentFinite.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "CechHomotopy.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "CechPrimitive.lean",
        SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "CechFinite.lean",
    )
    retired_proj_algebra_imports = {
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.GradedLocalization",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.Shift",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistLocalization",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.LaurentBasis",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.LaurentProjection",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.LaurentBlock",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.LaurentHomotopy",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.LaurentFinite",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.CechHomotopy",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.CechPrimitive",
        "DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.CechFinite",
    }
    for path in retired_proj_algebra_paths:
        if path.exists():
            failures.append(
                f"retired Proj algebra path restored: {path.relative_to(ROOT)}"
            )
    for path, modules in imports_by_path.items():
        restored = sorted(retired_proj_algebra_imports.intersection(modules))
        if restored:
            failures.append(
                f"{path.relative_to(ROOT)}: imports retired Proj algebra "
                f"path(s) {restored}"
            )
    for path in sorted((SOURCE_ROOT / "AlgebraicGeometry" / "Proj").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for declaration in (
            "AwayRep",
            "signProjection",
            "signProjectionHom",
            "laurentFace",
            "intNegSupport",
            "laurentFilter",
            "blockProj",
            "blockProjHom",
            "laurentHomotopy",
            "polynomialToHomogeneousLocalization",
            "blockRep",
            "fg_blockSpan",
            "polynomialVariableCechDenominator",
            "polynomialVariableCechDenominator_mem",
            "polynomialVariableCechDenominator_succAbove",
            "polynomialVariableCechDenominator_succAbove_mem",
            "polynomialVariableCechTerm",
            "polynomialVariableCechCochains",
            "polynomialVariableCechFace",
            "polynomialVariableFraction",
            "polynomialVariableIntCechTerm",
            "polynomialVariableIntCechCochains",
            "polynomialVariableIntCechFace",
            "cechTerm",
            "cechCochains",
            "cechFace",
            "cechFace_natShift",
            "cechFace_intShift",
            "cechCofactor",
            "X_mul_cechCofactor",
            "tupleExponent",
            "tupleDenominator_eq",
            "cechTermEquiv",
            "cechBlockProj",
            "cechHomotopy",
            "cechTermCongr",
            "cechBlockPrimitive",
            "cechPrimitive",
            "powersCongrLinear",
            "cechBlockSpan",
            "fg_cechBlockSpan",
            "polynomialVariable_adjoin_eq_top",
        ):
            if re.search(
                rf"^(?:noncomputable\s+)?(?:abbrev|def|structure|theorem)\s+{declaration}\b",
                text,
                re.MULTILINE,
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}: restored generic Laurent or "
                    f"polynomial Čech declaration {declaration}"
                )

    for path in sorted((SOURCE_ROOT / "AlgebraicGeometry").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for declaration in (
            "intShiftPiece_eq_bot_of_neg",
            "eq_zero_of_X_pow_dvd_of_isHomogeneous_of_lt",
            "num_eq_zero_of_cross_of_neg",
        ):
            if re.search(
                rf"^(?:noncomputable\s+)?(?:abbrev|def|structure|theorem)\s+{declaration}\b",
                text,
                re.MULTILINE,
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}: restored generic negative-twist "
                    f"arithmetic declaration {declaration}"
                )

    graded_module_consumers = (
        (SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "AssociatedSheaf.lean",
            "DerivedAlgGeo.Algebra.Module.GradedModule.Localization"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "TwistingSheaf.lean",
            "DerivedAlgGeo.Algebra.Module.GradedModule.Shift"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "TwistChart.lean",
            "DerivedAlgGeo.Algebra.Module.GradedModule.TwistLocalization"),
        (SOURCE_ROOT / "Algebra" / "MvPolynomial" / "Cech" /
            "Homotopy.lean",
            "DerivedAlgGeo.Algebra.Module.GradedModule.PowersCongr"),
        (SOURCE_ROOT / "Algebra" / "MvPolynomial" / "LaurentBlock.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.LaurentProjection"),
        (SOURCE_ROOT / "Algebra" / "MvPolynomial" / "LaurentHomotopy.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.LaurentBlock"),
        (SOURCE_ROOT / "Algebra" / "MvPolynomial" / "LaurentFinite.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.LaurentBlock"),
        (SOURCE_ROOT / "Algebra" / "MvPolynomial" / "Cech" /
            "Homotopy.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.LaurentHomotopy"),
        (SOURCE_ROOT / "Algebra" / "MvPolynomial" / "Cech" /
            "Homotopy.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Basic"),
        (SOURCE_ROOT / "Algebra" / "MvPolynomial" / "Cech" /
            "Primitive.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Homotopy"),
        (SOURCE_ROOT / "Algebra" / "MvPolynomial" / "Cech" /
            "Finite.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.LaurentFinite"),
        (SOURCE_ROOT / "Algebra" / "MvPolynomial" / "Cech" /
            "Finite.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Homotopy"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "ProjectiveSpace.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Basic"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "ProjectiveSpace.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.DivMonomial"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Proj" / "Modules" /
            "ProjectiveSpace.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.Grading"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "NegativeTwist.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.DivMonomial"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Proj" /
            "ProjectiveSpaceVariety.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.Grading"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Cech" /
            "Vanishing.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Primitive"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Finiteness" /
            "ProjectiveSpaceTopFinite.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Finite"),
        (SOURCE_ROOT / "AlgebraicGeometry" / "Cohomology" / "Finiteness" /
            "ProjectiveSpaceScalars.lean",
            "DerivedAlgGeo.Algebra.MvPolynomial.LaurentFinite"),
    )
    for path, required_import in graded_module_consumers:
        if required_import not in imports_by_path[path]:
            failures.append(
                f"{path.relative_to(ROOT)}: graded polynomial consumer must import "
                f"the algebraic owner {required_import} directly"
            )

    graded_module_umbrellas = {
        SOURCE_ROOT / "Algebra" / "Module" / "GradedModule.lean":
            "DerivedAlgGeo.Algebra.Module.GradedModule.Localization",
        SOURCE_ROOT / "Algebra" / "Module.lean":
            "DerivedAlgGeo.Algebra.Module.GradedModule",
        SOURCE_ROOT / "Algebra" / "Finsupp.lean":
            "DerivedAlgGeo.Algebra.Finsupp.LaurentExponent",
        SOURCE_ROOT / "Algebra" / "MvPolynomial.lean":
            "DerivedAlgGeo.Algebra.MvPolynomial.LaurentHomotopy",
    }
    for path, required_import in graded_module_umbrellas.items():
        if not path.is_file():
            failures.append(
                f"graded Laurent umbrella missing: {path.relative_to(ROOT)}"
            )
        elif required_import not in imports_by_path[path]:
            failures.append(
                f"{path.relative_to(ROOT)}: missing graded Laurent umbrella "
                f"import {required_import}"
            )

    polynomial_cech_umbrellas = {
        SOURCE_ROOT / "Algebra" / "MvPolynomial" / "Cech.lean": (
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Basic",
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Homotopy",
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Primitive",
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech.Finite",
        ),
        SOURCE_ROOT / "Algebra" / "MvPolynomial.lean": (
            "DerivedAlgGeo.Algebra.MvPolynomial.Cech",
        ),
    }
    for path, required_imports in polynomial_cech_umbrellas.items():
        if not path.is_file():
            failures.append(
                f"polynomial Čech umbrella missing: {path.relative_to(ROOT)}"
            )
            continue
        for required_import in required_imports:
            if required_import not in imports_by_path[path]:
                failures.append(
                    f"{path.relative_to(ROOT)}: missing polynomial Čech "
                    f"umbrella import {required_import}"
                )

    exterior_power_owners = {
        SOURCE_ROOT / "LinearAlgebra" / "ExteriorPower" /
            "Semilinear.lean": "namespace LinearMap\n",
        SOURCE_ROOT / "LinearAlgebra" / "ExteriorPower" /
            "Top.lean": "namespace Module\n",
        SOURCE_ROOT / "CategoryTheory" / "Sites" / "Sheaves" / "Modules" /
            "ExteriorPower.lean": "namespace PresheafOfModules\n",
    }
    for path, owner_fragment in exterior_power_owners.items():
        if not path.exists():
            failures.append(
                f"canonical exterior-power owner is missing: {path.relative_to(ROOT)}"
            )
        elif owner_fragment not in path.read_text(encoding="utf-8"):
            failures.append(
                f"{path.relative_to(ROOT)}: missing canonical exterior-power "
                f"owner fragment {owner_fragment!r}"
            )

    exterior_power_umbrellas = {
        SOURCE_ROOT / "LinearAlgebra.lean":
            "DerivedAlgGeo.LinearAlgebra.ExteriorPower",
        SOURCE_ROOT / "CategoryTheory" / "Sites" / "Sheaves" /
            "Modules.lean":
            "DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.ExteriorPower",
    }
    for path, required_import in exterior_power_umbrellas.items():
        if required_import not in imports_by_path[path]:
            failures.append(
                f"{path.relative_to(ROOT)}: missing canonical exterior-power "
                f"umbrella import {required_import}"
            )

    generic_families_root = strong_stability_root / "Families"
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
    bounded_geometry_source = neutral_derived_families_root / "BoundedGeometry.lean"
    bounded_geometry_text = bounded_geometry_source.read_text(encoding="utf-8")
    coherent_derived_source = neutral_derived_families_root.parent / "Coherent.lean"
    coherent_derived_text = coherent_derived_source.read_text(encoding="utf-8")
    if f"namespace {DERIVED_CATEGORY_NAMESPACE}" not in coherent_derived_text:
        failures.append(
            f"{coherent_derived_source.relative_to(ROOT)}: coherent-derived "
            f"declarations must use namespace {DERIVED_CATEGORY_NAMESPACE}"
        )
    if (
        "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families"
        in coherent_derived_text
    ):
        failures.append(
            f"{coherent_derived_source.relative_to(ROOT)}: canonical D(Coh X), "
            "Dᵇ(Coh X), and Perf(X) owner must not import family consumers"
        )
    if "DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant" in coherent_derived_text:
        failures.append(
            f"{coherent_derived_source.relative_to(ROOT)}: canonical coherent-"
            "derived owner must not import determinant consumers"
        )
    coherent_owner_import = (
        "DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent"
    )
    if coherent_owner_import not in imports_by_path[bounded_geometry_source]:
        failures.append(
            f"{bounded_geometry_source.relative_to(ROOT)}: family pullback "
            f"consumer must import canonical owner {coherent_owner_import}"
        )
    coherent_owner_declarations = (
        "schemeCoherentHasDerivedCategory",
        "SchemeCoherentDerivedCategory",
        "SchemeBoundedCoherentDerivedCategory",
        "schemeFiniteLocallyFreeGenerator",
        "schemePerfect",
        "SchemePerfectDerivedCategory",
    )
    for name in coherent_owner_declarations:
        if re.search(
            rf"^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure|class|instance)\s+"
            rf"{name}\b",
            bounded_geometry_text,
            re.MULTILINE,
        ):
            failures.append(
                f"{bounded_geometry_source.relative_to(ROOT)}: canonical "
                f"coherent-derived declaration {name} returned to Families"
            )
    if not re.search(
        r"instance(?:\s+\([^)]*\))?\s+schemeModulesHasDerivedCategory\b",
        derived_category_basic_text,
    ):
        failures.append(
            f"{derived_category_basic.relative_to(ROOT)}: module-sheaf derived "
            "category instance must be registered at the canonical owner"
        )
    if not re.search(
        r"instance(?:\s+\([^)]*\))?\s+schemeSheafOfModulesHasDerivedCategory\b",
        derived_category_basic_text,
    ):
        failures.append(
            f"{derived_category_basic.relative_to(ROOT)}: the explicit "
            "SheafOfModules carrier must reuse the canonical scheme-module "
            "derived-category instance"
        )
    if not re.search(
        r"schemeSheafOfModulesHasDerivedCategory[\s\S]*?:=[\s\n]*"
        r"schemeModulesHasDerivedCategory X",
        derived_category_basic_text,
    ):
        failures.append(
            f"{derived_category_basic.relative_to(ROOT)}: the explicit "
            "SheafOfModules adapter must delegate to "
            "schemeModulesHasDerivedCategory"
        )
    if "letI := HasDerivedCategory.standard X.Modules" in derived_category_basic_text:
        failures.append(
            f"{derived_category_basic.relative_to(ROOT)}: canonical abbreviations "
            "must consume schemeModulesHasDerivedCategory instead of choosing "
            "per-abbreviation instances"
        )
    dqc_source = neutral_derived_families_root.parent / "Dqc.lean"
    dqc_text = dqc_source.read_text(encoding="utf-8")
    geometric_generic_derived_names = {
        bounded_geometry_source: (
            "tStructureIsLE_of_retract",
            "tStructureIsGE_of_retract",
            "mapHomologicalComplex_isStrictlyLE",
            "mapHomologicalComplex_isStrictlyGE",
            "mapDerivedCategory_isLE",
            "mapDerivedCategory_isGE",
            "mapDerivedCategory_bounded",
        ),
        dqc_source: ("mapDerivedCategoryHomologyIso",),
    }
    for path, names in geometric_generic_derived_names.items():
        text = bounded_geometry_text if path == bounded_geometry_source else dqc_text
        for name in names:
            if re.search(
                rf"^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure|class)\s+"
                rf"{name}\b",
                text,
                re.MULTILINE,
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}: generic derived-category "
                    f"declaration {name} returned to geometry"
                )
    affine_generic_declarations = {
        "AffineKProjectivePullback.lean": (
            "kProjectiveHomotopy",
            "KProjectiveHomotopyCategory",
            "kProjectiveQh",
            "KProjectiveDerivedCategory",
            "kProjectiveDerivedFunctor",
            "kProjectiveLocusDerivedFunctor",
        ),
        "AffineKProjectiveCoherence.lean": (
            "boundedAboveProjectiveHomotopy",
            "BoundedAboveProjectiveHomotopyCategory",
            "boundedAboveProjectiveQh",
            "BoundedAboveProjectiveDerivedCategory",
            "mapBoundedAboveProjectiveHomotopy",
            "boundedAboveProjectiveDerivedFunctor",
        ),
        "AffineKProjectiveUnitality.lean": (
            "mapBoundedAboveProjectiveHomotopyIso",
            "mapBoundedAboveProjectiveHomotopyIdIso",
            "boundedAboveProjectiveDerivedFunctorIso",
            "boundedAboveProjectiveDerivedFunctorIdIso",
        ),
    }
    dqc_subtree = neutral_derived_families_root.parent / "Dqc"
    for filename, names in affine_generic_declarations.items():
        path = dqc_subtree / filename
        text = path.read_text(encoding="utf-8")
        for name in names:
            if re.search(
                rf"^(?:noncomputable\s+)?(?:def|abbrev|theorem|lemma|structure|class)\s+"
                rf"{name}\b",
                text,
                re.MULTILINE,
            ):
                failures.append(
                    f"{path.relative_to(ROOT)}: generic derived-category "
                    f"declaration {name} returned to the affine consumer"
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
    categorical_fourier_mukai_autoequivalence = (
        SOURCE_ROOT / "CategoryTheory" / "Triangulated" / "FourierMukai"
        / "Autoequivalence.lean"
    )
    categorical_fourier_mukai_text = (
        categorical_fourier_mukai_autoequivalence.read_text(encoding="utf-8")
    )
    if (
        f"namespace {CATEGORICAL_FOURIER_MUKAI_NAMESPACE}"
        not in categorical_fourier_mukai_text
    ):
        failures.append(
            f"{categorical_fourier_mukai_autoequivalence.relative_to(ROOT)}: "
            "generic kernel autoequivalences must use namespace "
            f"{CATEGORICAL_FOURIER_MUKAI_NAMESPACE}"
        )

    geometric_moduli_root = SOURCE_ROOT / "AlgebraicGeometry" / "Moduli"
    for relative, namespace in GEOMETRIC_MODULI_MODULES.items():
        path = geometric_moduli_root / relative
        if not path.is_file():
            failures.append(
                f"geometric stability object missing: {path.relative_to(ROOT)}"
            )
            continue
        text = path.read_text(encoding="utf-8")
        if f"namespace {namespace}" not in text:
            failures.append(
                f"{path.relative_to(ROOT)}: geometric stability objects must "
                f"use namespace {namespace}"
            )

    for relative in sorted(GEOMETRIC_INSTANCE_MODULES):
        path = SOURCE_ROOT / relative
        if not path.is_file():
            failures.append(
                f"algebraic-geometric categorical bridge missing: "
                f"{path.relative_to(ROOT)}"
            )
        elif owner(path) != GEOMETRY_INSTANCES_OWNER:
            failures.append(
                f"{path.relative_to(ROOT)}: bridge is not classified as "
                f"{GEOMETRY_INSTANCES_OWNER}"
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
        if "AlgebraicGeometry.StabilityCondition" in text:
            failures.append(
                f"{path.relative_to(ROOT)}: declaration or import restored the "
                "retired AlgebraicGeometry.StabilityCondition namespace"
            )
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
        if RETIRED_STRONG_DEFORMATION_NAMESPACE in text:
            failures.append(
                f"{path.relative_to(ROOT)}: declaration restored the retired "
                f"namespace {RETIRED_STRONG_DEFORMATION_NAMESPACE}"
            )
        if RETIRED_STRONG_GROUP_ACTION_NAMESPACE in text:
            failures.append(
                f"{path.relative_to(ROOT)}: declaration restored the retired "
                f"strong-sibling namespace {RETIRED_STRONG_GROUP_ACTION_NAMESPACE}"
            )

    all_geometry_modules = (
        NEUTRAL_DERIVED_FAMILY_MODULES | GEOMETRIC_FOURIER_MUKAI_MODULES
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

    for module in sorted(GEOMETRIC_FOURIER_MUKAI_MODULES):
        relocated = geometric_fourier_mukai_root / f"{module}.lean"
        if not relocated.exists():
            failures.append(
                f"geometric Fourier--Mukai module missing: "
                f"{relocated.relative_to(ROOT)}"
            )

    legacy_dqc = generic_families_root / "Dqc"
    relocated_dqc = SOURCE_ROOT / "AlgebraicGeometry" / "DerivedCategory" / "Dqc"
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
                f"DerivedAlgGeo/{source}:{line_number}: algebraic geometry "
                f"imports categorical realization leaf {module}"
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
        "ok: weak stability is independent of, and structurally parented by, "
        "Bridgeland stability; no compatibility adapter tree exists"
    )
    print(
        "ok: neutral triangulated-family declarations use the generic "
        "CategoryTheory.Triangulated.Families namespace"
    )
    print(
        "ok: neutral moduli boundedness and subprestack machinery use their "
        "CategoryTheory.Moduli and CategoryTheory.Pseudofunctor roots"
    )
    print(
        "ok: relative-perfect selectors are explicitly fiberwise; the genuine "
        "affine subprestack uses the generic restriction-stable object-property root"
    )
    print(
        "ok: generic stacks in groupoids use their CategoryTheory namespace"
    )
    print(
        "ok: generic derived-category, opposite, linear-dual, K-projective, "
        "and bounded-projective APIs use the CategoryTheory owner; geometric "
        "duality and affine files contain only consumers"
    )
    print(
        "ok: generic Ext, spectral-sequence, simplicial, and site-theoretic "
        "Cech APIs use categorical owners; geometric cohomology contains only consumers"
    )
    print(
        "ok: generic abelian and ringed-site sheaf APIs use their categorical "
        "roots; the topological cohomology specialization uses the Topology owner"
    )
    print(
        "ok: bicategorical adjunction is the higher source, ordinary adjunction "
        "is its Cat specialization, and preservation results use the Limits owner"
    )
    print(
        "ok: exterior-power algebra uses LinearAlgebra, arbitrary presheaf-module "
        "exterior powers use CategoryTheory, and geometry retains only consumers"
    )
    print(
        "ok: module-localization kernel maps use the Algebra owner, and "
        "coherent-sheaf geometry imports them as a direct consumer"
    )
    print(
        "ok: weighted-basis decompositions use LinearAlgebra and pure "
        "monomial-division identities use Algebra; geometric files are consumers"
    )
    print(
        "ok: graded-module localizations, polynomial generation and exact division, "
        "Laurent bases and projections, and polynomial variable Cech algebra use "
        "Algebra roots; Proj and geometric Cech modules are direct consumers"
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
        "ok: generic kernel autoequivalences use the categorical Fourier--Mukai "
        "namespace and Bridgeland actions extend it from the strong child"
    )
    print(
        "ok: Bridgeland GroupAction declarations use the matching strong-child "
        "namespace; retired names are confined to the executable restatement bridge"
    )
    print(
        "ok: Bridgeland deformation helpers use the matching strong-child "
        "namespace"
    )
    print(
        "ok: staged import-only compatibility shims are retired and the "
        "stability census imports canonical owners"
    )
    print(
        "ok: scheme-derived categories, families, Dqc, and geometric "
        "Fourier--Mukai declarations use their matching AlgebraicGeometry "
        "namespaces"
    )
    print(
        "ok: semistable loci and relative HN filtrations use their Moduli "
        "namespaces; categorical realizations use explicit geometry-instance leaves"
    )
    print(
        "ok: the retired flattened categorical stability-family namespace is "
        "absent from DerivedAlgGeo"
    )
    print(
        "ok: neutral scheme-derived families, geometric Fourier--Mukai, and "
        "stability realizations have distinct owners"
    )
    print(
        "ok: geometry-to-instance reverse-edge fixtures distinguish allowed "
        "and forbidden imports"
    )
    print(
        f"ok: {len(reverse_edges)} measured AlgebraicGeometry -> "
        "Instances/AlgebraicGeometry edge(s); the migration allowlist is empty"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
