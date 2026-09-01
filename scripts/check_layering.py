#!/usr/bin/env python3
"""Enforce the repository's dependency direction.

The source tree mirrors Mathlib's subject hierarchy, and Mathlib's subjects
are not a tower: ``Algebra/Homology`` imports ``CategoryTheory`` and
``CategoryTheory/Linear`` imports ``Algebra``. So this gate does not rank
subjects and does not look for subject-level cycles. Lean already rejects
module-level cycles, and that is the only acyclicity Mathlib has either.

What it enforces is the short list of *policy* edges the layout promises and
nothing else checks.

1. **Geometry firewall.** Only modules below ``AlgebraicGeometry/`` and
   ``Development/`` may import ``DerivedAlgGeo.AlgebraicGeometry`` or
   ``Mathlib.AlgebraicGeometry``, and only they may declare into the
   ``AlgebraicGeometry`` namespace. Everything else in the library is usable
   without schemes. A geometric realization of a categorical interface
   therefore lives with the geometric object, the way ``Abelian (ModuleCat R)``
   lives in ``Algebra/Category/ModuleCat/Abelian.lean``; there are no
   ``Instances/AlgebraicGeometry`` leaves below a generic subject.
2. **Development is a leaf.** No stable module imports it.
3. **Stability-neutral geometry.** Geometry outside the subtrees that exist to
   consume stability conditions must not reach the stability tree, even
   transitively. This is what lets ``Dᵇ(Coh X)``, ``Dqc``, coherent sheaves,
   and cohomology be imported without Bridgeland stability.
4. **Weak stability is independent of Bridgeland stability**, and the
   Bridgeland pre-stability structure extends the weak one instead of copying
   its fields.
5. **Retired paths stay retired**, so a shim removed by a cutover cannot drift
   back.
6. **New top-level subjects are deliberate.** A directory directly below the
   source root must be one of the Mathlib subjects this repository uses.

Fixtures under ``scripts/fixtures/layering`` are known-answer tests: every
``allowed`` fixture must pass rules 1-4 and every ``forbidden`` fixture must
fail at least one of them, so an edit that silently stops rejecting anything
is caught here rather than by the next regression.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIBRARY = "DerivedAlgGeo"
SOURCE_ROOT = ROOT / LIBRARY
FIXTURES = ROOT / "scripts" / "fixtures" / "layering"

# Lean's module system prefixes imports with `public`, `private`, or `meta`,
# and `import all` re-exports; a plain `^import` regex misses every one.
IMPORT = re.compile(
    r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)"
)
NAMESPACE = re.compile(r"^\s*namespace\s+(\S+)")

KNOWN_SUBJECTS = {
    "Algebra",
    "AlgebraicGeometry",
    "AlgebraicTopology",
    "CategoryTheory",
    "Development",
    "LinearAlgebra",
    "RingTheory",
    "Topology",
}

GEOMETRY = f"{LIBRARY}.AlgebraicGeometry"
DEVELOPMENT = f"{LIBRARY}.Development"
MATHLIB_GEOMETRY = "Mathlib.AlgebraicGeometry"
GEOMETRY_IMPORTERS = (GEOMETRY, DEVELOPMENT)
# The two aggregation roots import everything and own nothing.
AGGREGATION_ROOTS = {LIBRARY, f"{LIBRARY}Sweep"}

# The stability tree. Weak stability is the dependency parent of Bridgeland
# stability; the physical nesting is `WeakStabilityCondition/` with the
# Bridgeland child `StabilityCondition/` below it, so a weak module is one in
# the weak tree but outside the strong subtree.
STABILITY_ROOT = f"{LIBRARY}.CategoryTheory.Triangulated.WeakStabilityCondition"
WEAK_TREE = STABILITY_ROOT
STRONG_TREE = f"{STABILITY_ROOT}.StabilityCondition"
STRONG_PRESTABILITY_SOURCE = SOURCE_ROOT / (
    "CategoryTheory/Triangulated/WeakStabilityCondition/StabilityCondition/"
    "Foundation/PreStabilityCondition.lean"
)
STRONG_PRESTABILITY_EXTENDS = re.compile(
    r"extends\s+toWeak\s*:\s*WeakStabilityCondition\.WeakPreStabilityCondition"
)

# Geometry that exists to consume stability conditions. Every other module
# below AlgebraicGeometry/ must be importable without the stability tree.
STABILITY_CONSUMING_GEOMETRY = (
    f"{GEOMETRY}.Moduli",
    f"{GEOMETRY}.Numerical",
    f"{GEOMETRY}.DerivedCategory.Stability",
)

# Paths removed by a structural cutover, relative to the source root. An entry
# without a suffix names a directory and also forbids its same-named umbrella.
RETIRED_PATHS = (
    "Compatibility",
    "AlgebraicGeometry/StabilityCondition",
    "AlgebraicGeometry/Duality/Serre/LinearDual.lean",
    "AlgebraicGeometry/Modules/Affine/Exactness.lean",
    "AlgebraicGeometry/Modules/Presentation.lean",
    "AlgebraicGeometry/Modules/Presentation/Finite.lean",
    "AlgebraicGeometry/Modules/Presentation/Transport.lean",
    "AlgebraicGeometry/Divisors/Tensor.lean",
    "AlgebraicGeometry/Divisors/Picard.lean",
    "AlgebraicGeometry/Divisors/Monoidal.lean",
    "AlgebraicGeometry/Stacks/Basic.lean",
    "AlgebraicGeometry/IntersectionTheory/NumericalPolynomial",
    "AlgebraicGeometry/Numerical/GrothendieckGroup/Relative.lean",
    "AlgebraicGeometry/Numerical/GrothendieckGroup/RelativeOverlattice.lean",
    "AlgebraicGeometry/Proj/Modules/LaurentBasis.lean",
    "AlgebraicGeometry/Proj/Modules/LaurentProjection.lean",
    "AlgebraicGeometry/Proj/Modules/LaurentBlock.lean",
    "AlgebraicGeometry/Proj/Modules/LaurentHomotopy.lean",
    "AlgebraicGeometry/Proj/Modules/LaurentFinite.lean",
    "AlgebraicGeometry/Proj/Modules/CechHomotopy.lean",
    "AlgebraicGeometry/Proj/Modules/CechPrimitive.lean",
    "AlgebraicGeometry/Proj/Modules/CechFinite.lean",
    "Algebra/Category/ModuleCat/StalkTensor.lean",
    "CategoryTheory/Adjunction",
    "CategoryTheory/ConstantSheafPullback.lean",
    "CategoryTheory/EquivalenceTransport.lean",
    "CategoryTheory/PseudofunctorObjectProperty.lean",
    "CategoryTheory/SheafCohomologyPushforward.lean",
    "CategoryTheory/Sites/CohomologyShortExact.lean",
    "CategoryTheory/TopologicalSheafCohomologyPushforward.lean",
    "CategoryTheory/WeakSerreExact.lean",
    "CategoryTheory/Monoidal/Triangulated/Instances",
    "CategoryTheory/Triangulated/Families/Boundedness.lean",
    "CategoryTheory/Triangulated/WeakStabilityCondition/Foundations",
    "CategoryTheory/Triangulated/WeakStabilityCondition/Families/Instances",
    "CategoryTheory/Triangulated/WeakStabilityCondition/StabilityCondition/"
    "Families/Instances",
    "CategoryTheory/Triangulated/WeakStabilityCondition/StabilityCondition/"
    "Symmetry/Autoequivalence/Instances",
    "CategoryTheory/Triangulated/WeakStabilityCondition/StabilityCondition/"
    "WeakCompatibility",
)


def module_of(path: pathlib.Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def retired_module(entry: str) -> str:
    return f"{LIBRARY}." + ".".join(pathlib.PurePosixPath(entry).with_suffix("").parts)


def in_tree(module: str, root: str) -> bool:
    return module == root or module.startswith(root + ".")


def is_weak_module(module: str) -> bool:
    return in_tree(module, WEAK_TREE) and not in_tree(module, STRONG_TREE)


def is_strong_module(module: str) -> bool:
    return in_tree(module, STRONG_TREE)


def may_import_geometry(module: str) -> bool:
    return module in AGGREGATION_ROOTS or any(
        in_tree(module, root) for root in GEOMETRY_IMPORTERS
    )


def parse(path: pathlib.Path) -> tuple[list[str], list[str]]:
    imports: list[str] = []
    namespaces: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if match := IMPORT.match(line):
            imports.append(match.group(1))
        elif match := NAMESPACE.match(line):
            namespaces.append(match.group(1))
    return imports, namespaces


def load_modules() -> dict[str, tuple[pathlib.Path, list[str], list[str]]]:
    modules: dict[str, tuple[pathlib.Path, list[str], list[str]]] = {}
    sources = [*SOURCE_ROOT.rglob("*.lean")]
    for root in AGGREGATION_ROOTS:
        candidate = ROOT / f"{root}.lean"
        if candidate.exists():
            sources.append(candidate)
    for path in sorted(sources):
        imports, namespaces = parse(path)
        modules[module_of(path)] = (path, imports, namespaces)
    return modules


class Closure:
    """Transitive library imports, memoized. Lean guarantees the graph is acyclic."""

    def __init__(self, graph: dict[str, list[str]]) -> None:
        self.graph = graph
        self.memo: dict[str, frozenset[str]] = {}

    def of(self, module: str) -> frozenset[str]:
        if module in self.memo:
            return self.memo[module]
        acc: set[str] = set()
        for dep in self.graph.get(module, ()):
            if not dep.startswith(LIBRARY):
                continue
            acc.add(dep)
            acc |= self.of(dep)
        result = frozenset(acc)
        self.memo[module] = result
        return result


def direction_failures(
    module: str, imports: list[str], namespaces: list[str], label: str
) -> list[str]:
    """Rules 1, 2, and the import half of rule 4, for one module."""
    failures: list[str] = []
    for imp in imports:
        if (in_tree(imp, GEOMETRY) or in_tree(imp, MATHLIB_GEOMETRY)) and (
            not may_import_geometry(module)
        ):
            failures.append(
                f"{label}: imports geometry ({imp}) from a geometry-independent "
                "subject; only AlgebraicGeometry/ and Development/ may"
            )
        if in_tree(imp, DEVELOPMENT) and not (
            in_tree(module, DEVELOPMENT) or module in AGGREGATION_ROOTS
        ):
            failures.append(f"{label}: imports the Development leaf ({imp})")
        if is_weak_module(module) and is_strong_module(imp):
            failures.append(
                f"{label}: weak stability imports its Bridgeland child ({imp})"
            )
    if not may_import_geometry(module):
        for namespace in namespaces:
            if in_tree(namespace, "AlgebraicGeometry"):
                failures.append(
                    f"{label}: declares into namespace {namespace} outside "
                    "AlgebraicGeometry/; a geometric realization of a categorical "
                    "interface lives with the geometric object"
                )
    return failures


def neutral_geometry_failures(
    module: str, imports: list[str], closure: Closure, label: str
) -> list[str]:
    """Rule 3 for one geometry module."""
    if not in_tree(module, GEOMETRY) or module == GEOMETRY:
        return []
    if any(in_tree(module, root) for root in STABILITY_CONSUMING_GEOMETRY):
        return []
    for imp in imports:
        if in_tree(imp, STABILITY_ROOT) or any(
            in_tree(dep, STABILITY_ROOT) for dep in closure.of(imp)
        ):
            return [
                f"{label}: reaches the stability tree through {imp}; only "
                + ", ".join(
                    root.removeprefix(LIBRARY + ".").replace(".", "/") + "/"
                    for root in STABILITY_CONSUMING_GEOMETRY
                )
                + " may, so that the rest of geometry is importable without "
                "stability conditions"
            ]
    return []


def check_fixtures(closure: Closure) -> list[str]:
    failures: list[str] = []
    for verdict in ("allowed", "forbidden"):
        base = FIXTURES / verdict
        fixtures = sorted(base.rglob("*.imports")) if base.exists() else []
        if not fixtures:
            failures.append(f"no {verdict} layering fixtures found under {base}")
            continue
        for fixture in fixtures:
            module = f"{LIBRARY}." + ".".join(
                fixture.relative_to(base).with_suffix("").parts
            )
            imports, namespaces = parse(fixture)
            label = str(fixture.relative_to(ROOT))
            found = direction_failures(module, imports, namespaces, label)
            found += neutral_geometry_failures(module, imports, closure, label)
            if verdict == "allowed" and found:
                failures.append(
                    "allowed layering fixture was rejected: " + "; ".join(found)
                )
            if verdict == "forbidden" and not found:
                failures.append(
                    f"forbidden layering fixture {label} was not rejected"
                )
    return failures


def main() -> int:
    failures: list[str] = []
    modules = load_modules()
    closure = Closure({m: imports for m, (_, imports, _) in modules.items()})

    # Rule 6.
    for entry in sorted(SOURCE_ROOT.iterdir()):
        if entry.is_dir() and entry.name not in KNOWN_SUBJECTS:
            failures.append(
                f"{entry.relative_to(ROOT)}: not a known Mathlib subject; add "
                "it to KNOWN_SUBJECTS deliberately or place the code below an "
                "existing subject"
            )

    # Rule 5.
    retired_modules: set[str] = set()
    for entry in RETIRED_PATHS:
        path = SOURCE_ROOT / entry
        retired_modules.add(retired_module(entry))
        candidates = [path] if path.suffix else [path, path.with_suffix(".lean")]
        for candidate in candidates:
            if candidate.exists():
                failures.append(
                    f"retired path restored: {candidate.relative_to(ROOT)}; "
                    "see docs/architecture/cutover-ledger.md for its owner"
                )
    for path in SOURCE_ROOT.rglob("*"):
        parts = path.relative_to(SOURCE_ROOT).parts
        if parts and parts[0] != "AlgebraicGeometry" and any(
            parts[i] == "Instances" and parts[i + 1].startswith("AlgebraicGeometry")
            for i in range(len(parts) - 1)
        ):
            failures.append(
                f"{path.relative_to(ROOT)}: geometric instance leaf below a "
                "generic subject; the instance lives with the geometric object"
            )

    # Rules 1-4 per module.
    for module, (path, imports, namespaces) in modules.items():
        label = str(path.relative_to(ROOT))
        failures += direction_failures(module, imports, namespaces, label)
        failures += neutral_geometry_failures(module, imports, closure, label)
        for imp in imports:
            if imp in retired_modules or any(
                in_tree(imp, retired) for retired in retired_modules
            ):
                failures.append(f"{label}: imports retired module {imp}")

    # Rule 4, structural half.
    if not STRONG_PRESTABILITY_SOURCE.exists():
        failures.append(
            f"missing {STRONG_PRESTABILITY_SOURCE.relative_to(ROOT)}: the "
            "Bridgeland pre-stability structure is the seam rule 4 checks"
        )
    elif not STRONG_PRESTABILITY_EXTENDS.search(
        STRONG_PRESTABILITY_SOURCE.read_text(encoding="utf-8")
    ):
        failures.append(
            f"{STRONG_PRESTABILITY_SOURCE.relative_to(ROOT)}: ordinary "
            "prestability must structurally extend WeakPreStabilityCondition"
        )

    failures += check_fixtures(closure)

    if failures:
        print("layering gate failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1

    geometry = sum(1 for m in modules if in_tree(m, GEOMETRY))
    neutral = sum(
        1
        for m in modules
        if in_tree(m, GEOMETRY)
        and m != GEOMETRY
        and not any(in_tree(m, r) for r in STABILITY_CONSUMING_GEOMETRY)
    )
    print(
        f"ok: {len(modules)} modules; only AlgebraicGeometry/ and Development/ "
        f"import geometry; {neutral} of {geometry} geometry modules are "
        "stability-neutral; weak stability is independent of, and structurally "
        f"parented by, Bridgeland stability; {len(RETIRED_PATHS)} retired paths "
        "absent"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
