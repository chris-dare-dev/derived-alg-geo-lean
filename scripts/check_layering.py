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
3. **Stability-neutral geometry.** Geometry outside the *subcomponents* that
   exist to consume stability conditions must not reach the stability tree,
   even transitively. This is what lets ``Dᵇ(Coh X)``, ``Dqc``, coherent
   sheaves, and cohomology be imported without Bridgeland stability. The
   exemption is named by subcomponent rather than by top-level subtree
   (MO1.01, #1312), with one exception: a same-named umbrella over an exempt
   subcomponent reaches the tree by re-exporting it, and is exempt as an
   umbrella only -- its other children are not.
4. **Weak stability is independent of Bridgeland stability**, and the
   Bridgeland pre-stability structure extends the weak one instead of copying
   its fields.
5. **Retired paths stay retired**, so a shim removed by a cutover cannot drift
   back.
6. **New top-level subjects are deliberate.** A directory directly below the
   source root must be one of the Mathlib subjects this repository uses.
8. **Charge construction is upstream of walls.** Neutral continuity, Hodge,
   and complex-pairing roots reach neither stability conditions nor geometry;
   the central-charge subtree reaches neither wall-locus modules nor geometry;
   and the moved owner structures are declared exactly once.
9. **The linear Serre root is shift-free.** ``CategoryTheory/Linear/Yoneda.lean``
   needs Mathlib alone, nothing below ``CategoryTheory/Linear/SerreFunctor/``
   reaches ``CategoryTheory/Triangulated`` even transitively, and the three
   linear-Yoneda representability helpers are declared exactly once. This is
   the claim MO1.07 (#1318) moved those files to make true, and it is the kind
   of claim that decays silently: one convenience import from a triangulated
   consumer and the root is no longer importable without a shift.
7. **The ``ObjectProperty`` lift block stays at its carrier's path.**
   ``CategoryTheory/ObjectProperty/Lift.lean`` declares all six of
   it and imports nothing from ``DerivedAlgGeo``; no other module redeclares
   any of the six.

Fixtures under ``scripts/fixtures/layering`` are known-answer tests: every
``allowed`` fixture must pass rules 1-4 and every ``forbidden`` fixture must
fail at least one of them, so an edit that silently stops rejecting anything
is caught here rather than by the next regression.
"""

from __future__ import annotations

import pathlib
import re
import sys

from _output import force_utf8_output

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

# The stability tree. Bridgeland stability is the canonical concept and names
# the directory; weak stability, its dependency parent, is the child `Weak/`,
# as `PseudoMetricSpace` is `MetricSpace/Pseudo/` in Mathlib. A weak module is
# one below `Weak/`; a strong module is one in the tree but outside `Weak/`.
STABILITY_ROOT = f"{LIBRARY}.CategoryTheory.Triangulated.StabilityCondition"
WEAK_TREE = f"{STABILITY_ROOT}.Weak"
STRONG_TREE = STABILITY_ROOT
STRONG_PRESTABILITY_SOURCE = SOURCE_ROOT / (
    "CategoryTheory/Triangulated/StabilityCondition/"
    "Foundation/PreStabilityCondition.lean"
)
STRONG_PRESTABILITY_EXTENDS = re.compile(
    r"extends\s+toWeak\s*:\s*WeakStabilityCondition\.WeakPreStabilityCondition"
)

# Geometry that exists to consume stability conditions, named by SUBCOMPONENT
# rather than by top-level subtree (MO1.01, #1312; review finding 14).
#
# The four blanket roots this list replaced -- `Moduli`, `Numerical`,
# `Stability` and `DerivedCategory.Stability` -- exempted 122 modules to excuse
# the 60 that actually reach the stability tree. The other 62 were unguarded,
# which is why the gate could pass on a snapshot in which numerical parents
# import their own specializations. A subcomponent that does not reach
# stability today is not exempt, so a new edge into the stability tree from
# `Numerical/Core/`, `Numerical/Mukai/`, `Numerical/RiemannRoch/`,
# `Numerical/Specializations/`, `Moduli/PerfectComplex/`, `Moduli/Quot/` or the
# non-charge `Numerical/GrothendieckGroup/` modules is now rejected here.
#
# This is a narrowing, not a subject order: it says nothing about which subject
# may import which, only which geometry subcomponents are allowed to reach the
# one tree the layout promises the rest of geometry is free of.
#
# Narrowing further is MO1.05, MO1.06 and MO1.13 work, not a free edit: each
# entry below still contains modules that do NOT reach stability, and the
# remaining queue is recorded in docs/architecture/cutover-ledger.md.
STABILITY_CONSUMING_GEOMETRY = (
    # The Dqc/families lane: base change of pre-stability data and the
    # geometric Fourier--Mukai action.
    f"{GEOMETRY}.DerivedCategory.Stability",
    # The two moduli subcomponents whose subject is a stability notion. The
    # rest of Moduli/ -- perfect complexes and Quot -- is stability-neutral and
    # is now held to that.
    f"{GEOMETRY}.Moduli.HarderNarasimhan",
    f"{GEOMETRY}.Moduli.Semistability",
    # Numerical models that carry charge and wall calculations. Dimension-zero
    # and rank-one examples do not, and are held to that.
    #
    # The fourfold leaves were in that neutral group when #1328 narrowed this
    # list, and they left it the same day: #1225 gave `ℙ⁴` and the sextic their
    # wall families, so the directory now carries charge like its two siblings.
    # The entry is the fact that changed, not an exemption bought to pass a gate.
    f"{GEOMETRY}.Numerical.Examples.Surface",
    f"{GEOMETRY}.Numerical.Examples.Threefold",
    f"{GEOMETRY}.Numerical.Examples.Fourfold",
    # The single K-theoretic charge adapter; the lattice, Euler-pairing,
    # discriminant and Mukai-vector modules beside it are neutral.
    f"{GEOMETRY}.Numerical.GrothendieckGroup.CategoricalCharge",
    f"{GEOMETRY}.Numerical.Stability",
    # Stability of sheaves: slope and Gieseker theory on `Coh X`, whose whole
    # purpose is to instantiate the abstract slope theory, so it necessarily
    # reaches the stability tree. Distinct from `DerivedCategory.Stability`,
    # which is the Dqc/families lane.
    f"{GEOMETRY}.Stability.Gieseker",
)

# Paths removed by a structural cutover, relative to the source root. An entry
# without a suffix names a directory and also forbids its same-named umbrella.
RETIRED_PATHS = (
    # 2026-09-02 Euler-characteristic lane: restated on Mathlib's GradedObject.eulerChar.
    "LinearAlgebra/AlternatingFinsum.lean",
    "LinearAlgebra/AlternatingSum.lean",
    # 2026-09-02 placement follow-ups to the Mathlib-mesh restructure.
    "Algebra/Homology/DerivedCategory/TStructure.lean",
    "CategoryTheory/Triangulated/QuasiAbelian.lean",
    "CategoryTheory/Triangulated/LinearOpposite.lean",
    "CategoryTheory/StabilityCharge.lean",
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
    "AlgebraicGeometry/ProjectiveSpectrum/HomogeneousLocalizationDomain.lean",
    "AlgebraicGeometry/ProjectiveSpectrum/Modules/LaurentBasis.lean",
    "AlgebraicGeometry/ProjectiveSpectrum/Modules/LaurentProjection.lean",
    "AlgebraicGeometry/ProjectiveSpectrum/Modules/LaurentBlock.lean",
    "AlgebraicGeometry/ProjectiveSpectrum/Modules/LaurentHomotopy.lean",
    "AlgebraicGeometry/ProjectiveSpectrum/Modules/LaurentFinite.lean",
    "AlgebraicGeometry/ProjectiveSpectrum/Modules/CechHomotopy.lean",
    "AlgebraicGeometry/ProjectiveSpectrum/Modules/CechPrimitive.lean",
    "AlgebraicGeometry/ProjectiveSpectrum/Modules/CechFinite.lean",
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
    "CategoryTheory/Triangulated/StabilityCondition/Weak/Foundations",
    "CategoryTheory/Triangulated/StabilityCondition/Weak/Families/Instances",
    "CategoryTheory/Triangulated/StabilityCondition/"
    "Families/Instances",
    "CategoryTheory/Triangulated/StabilityCondition/"
    "Symmetry/Autoequivalence/Instances",
    "CategoryTheory/Triangulated/StabilityCondition/"
    "WeakCompatibility",
    # 2026-09-13 MO1.02: charge construction moved upstream of wall loci.
    "LinearAlgebra/QuadraticForm/CentralCharge.lean",
    "CategoryTheory/Triangulated/StabilityCondition/Walls/Exp",
    "CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Charge.lean",
    "CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Coordinates.lean",
    "CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Discriminant.lean",
    "CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Mukai.lean",
    "CategoryTheory/Triangulated/StabilityCondition/Walls/Divisorial/Support.lean",
    # 2026-09-13 MO1.07: the k-linear Serre duality data and its uniqueness
    # need no shift, so they moved to CategoryTheory/Linear/SerreFunctor/.
    "CategoryTheory/Triangulated/SerreFunctor/Basic.lean",
    "CategoryTheory/Triangulated/SerreFunctor/Uniqueness.lean",
)


# Rule 7. The `ObjectProperty` lift block was hoisted out of the t-structure
# restriction file on 2026-09-04. It is generic by construction: its file needs
# Mathlib alone. Both halves of that are checked, because either one drifting
# back is how the block would return to its consumer -- an added `DerivedAlgGeo`
# import first, then a declaration following it.
OBJECT_PROPERTY_ROOT = "CategoryTheory/ObjectProperty/Lift.lean"
OBJECT_PROPERTY_BLOCK = (
    "liftOfLE",
    "preimageLift",
    "inverseImageLift",
    "liftToInverseImage",
    "restrictInverseImageLeft",
    "restrictInverseImageRight",
)
# Rule 8. MO1.02 moved charge construction upstream of wall loci. The Hodge
# carrier is neutral linear algebra, while Chern coordinates and charge
# parameters live below CentralCharge/. Geometric files may still add lemmas
# into these namespaces for dot notation, so only structures are pinned.
DIVISORIAL_ROOT_DIR = (
    "CategoryTheory/Triangulated/StabilityCondition/CentralCharge/Divisorial"
)
DIVISORIAL_BLOCK = (
    "ChargeCoordinates",
    "ChernCharacter",
    "DivisorialParameters",
    "OrthogonalSlice",
    "SqrtTodd",
    "StabilityParameters",
)
HODGE_INDEX_ROOT = "LinearAlgebra/BilinearForm/HodgeIndex.lean"
HODGE_INDEX_BLOCK = ("DivisorSpace", "HodgeIndex", "HodgeDefinite")
CENTRAL_CHARGE_TREE = f"{STABILITY_ROOT}.CentralCharge"
WALL_TREE = f"{STABILITY_ROOT}.Walls"
NEUTRAL_CHARGE_ROOTS = (
    "LinearAlgebra/QuadraticForm/ComplexPairing.lean",
    "LinearAlgebra/QuadraticForm/Continuous.lean",
    "LinearAlgebra/QuadraticForm/Bounds.lean",
    HODGE_INDEX_ROOT,
)
PAIRING_CORE_MODULE = f"{LIBRARY}.LinearAlgebra.QuadraticForm.ComplexPairing"
PAIRING_DOWNSTREAM_TREES = (
    f"{LIBRARY}.LinearAlgebra.QuadraticForm.PeriodDomain",
    f"{LIBRARY}.LinearAlgebra.QuadraticForm.WallFiniteness",
    f"{LIBRARY}.LinearAlgebra.QuadraticForm.WallRegion",
    f"{LIBRARY}.LinearAlgebra.QuadraticForm.Orientation",
)
# Rule 9. The k-linear Serre duality data and the linear Yoneda representability
# helpers moved out of Triangulated/ on 2026-09-13 (MO1.07, #1318) because they
# mention no shift and no distinguished triangle -- the previous owner's own
# module docstring said as much. Pinned in both directions: the Yoneda file
# needs Mathlib alone, the Serre root reaches no triangulated module, and the
# three helpers are declared once so a consumer cannot quietly re-derive them.
LINEAR_YONEDA_ROOT = "CategoryTheory/Linear/Yoneda.lean"
LINEAR_YONEDA_BLOCK = (
    "isoOfLinearYonedaIso",
    "map_isoOfLinearYonedaIso",
    "hom_ext_of_linearYoneda",
)
LINEAR_SERRE_ROOT_DIR = "CategoryTheory/Linear/SerreFunctor"
TRIANGULATED_TREE = f"{LIBRARY}.CategoryTheory.Triangulated"

STRUCTURE_DECLARES = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*structure\s+(\S+)"
)


def structure_names(text: str) -> set[str]:
    """Structure names a module declares, for the rule 8 site check."""
    return {
        match.group(1)
        for match in (STRUCTURE_DECLARES.match(line) for line in text.splitlines())
        if match
    }


DECLARES = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:def|abbrev|instance|theorem|lemma)\s+(?:_root_\.)?(\S+)"
)


def declared_names(text: str) -> set[str]:
    """Final name components declared in a module, for the rule 7 site check."""
    return {
        match.group(1).split(".")[-1]
        for match in (DECLARES.match(line) for line in text.splitlines())
        if match
    }


def module_of(path: pathlib.Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def retired_module(entry: str) -> str:
    return f"{LIBRARY}." + ".".join(pathlib.PurePosixPath(entry).with_suffix("").parts)


def in_tree(module: str, root: str) -> bool:
    return module == root or module.startswith(root + ".")


def is_weak_module(module: str) -> bool:
    return in_tree(module, WEAK_TREE)


def is_strong_module(module: str) -> bool:
    return in_tree(module, STRONG_TREE) and not in_tree(module, WEAK_TREE)


def may_import_geometry(module: str) -> bool:
    return module in AGGREGATION_ROOTS or any(
        in_tree(module, root) for root in GEOMETRY_IMPORTERS
    )


def is_umbrella(module: str) -> bool:
    """Whether `module` is the same-named umbrella of a source directory.

    `DerivedAlgGeo/AlgebraicGeometry/Numerical.lean` beside
    `DerivedAlgGeo/AlgebraicGeometry/Numerical/` is an umbrella;
    `Numerical/Core/Basic.lean` is not. A fixture module names no directory, so
    fixtures are never umbrellas and the exception below cannot launder one.
    """
    return (ROOT / pathlib.Path(*module.split("."))).is_dir()


def may_consume_stability(module: str) -> bool:
    """Rule 3's exemption, subcomponent-scoped with one umbrella exception.

    A same-named umbrella re-exports its direct children, so an umbrella over a
    subcomponent that legitimately consumes stability reaches the tree by
    construction, and holding it neutral would mean dropping a child from an
    umbrella -- breaking the layout's own promise that every non-leaf directory
    has a complete one. The exception is therefore granted to the umbrella *as
    an umbrella*, and is not inherited by the umbrella's other children. That
    is the distinction between a narrowly imported module and a full subject
    umbrella that review finding 14 asks the policy to keep.
    """
    if any(in_tree(module, root) for root in STABILITY_CONSUMING_GEOMETRY):
        return True
    return is_umbrella(module) and any(
        in_tree(root, module) for root in STABILITY_CONSUMING_GEOMETRY
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
    if may_consume_stability(module):
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
                + " and the umbrellas above them may, so that the rest of "
                "geometry is importable without stability conditions"
            ]
    return []


def owner_boundary_failures(
    module: str, imports: list[str], closure: Closure, label: str
) -> list[str]:
    """Rule 8 import boundaries for actual modules and known-answer fixtures."""
    reached: set[str] = set(imports)
    for imp in imports:
        reached |= closure.of(imp)
    neutral_modules = tuple(
        retired_module(entry) for entry in NEUTRAL_CHARGE_ROOTS
    )
    if any(in_tree(module, root) for root in neutral_modules):
        forbidden = sorted(
            dep
            for dep in reached
            if in_tree(dep, STABILITY_ROOT) or in_tree(dep, GEOMETRY)
        )
        if forbidden:
            return [
                f"{label}: reaches {forbidden[0]}; neutral charge roots may "
                "depend on neither stability conditions nor geometry"
            ]
    if in_tree(module, PAIRING_CORE_MODULE):
        forbidden = sorted(
            dep
            for dep in reached
            if any(in_tree(dep, root) for root in PAIRING_DOWNSTREAM_TREES)
        )
        if forbidden:
            return [
                f"{label}: reaches {forbidden[0]}; the paired-functional core "
                "must remain independent of period-domain and wall-arrangement consumers"
            ]
    if in_tree(module, CENTRAL_CHARGE_TREE):
        forbidden = sorted(
            dep
            for dep in reached
            if in_tree(dep, WALL_TREE) or in_tree(dep, GEOMETRY)
        )
        if forbidden:
            return [
                f"{label}: reaches {forbidden[0]}; central-charge construction "
                "must remain upstream of walls and geometry"
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
            found += owner_boundary_failures(module, imports, closure, label)
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
            # An empty directory is a leftover of a move, not a restoration:
            # git does not track it, so a clean checkout never has one.
            restored = candidate.is_file() or (
                candidate.is_dir() and any(candidate.rglob("*.lean"))
            )
            if restored:
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
        failures += owner_boundary_failures(module, imports, closure, label)
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

    # Rule 7.
    op_root = SOURCE_ROOT / OBJECT_PROPERTY_ROOT
    if not op_root.is_file():
        failures.append(
            f"missing {op_root.relative_to(ROOT)}: it owns the ObjectProperty "
            "lift block; see docs/architecture/cutover-ledger.md"
        )
    else:
        op_module = module_of(op_root)
        op_imports, _ = parse(op_root)
        for imp in op_imports:
            if in_tree(imp, LIBRARY):
                failures.append(
                    f"{op_root.relative_to(ROOT)}: imports {imp}; this root is "
                    "generic and must need Mathlib alone"
                )
        op_declared = declared_names(op_root.read_text(encoding="utf-8"))
        for name in OBJECT_PROPERTY_BLOCK:
            if name not in op_declared:
                failures.append(
                    f"{op_root.relative_to(ROOT)}: no longer declares {name}; "
                    "the lift block's canonical owner is this file"
                )
        for module, (path, _, _) in modules.items():
            if module == op_module:
                continue
            stray = declared_names(path.read_text(encoding="utf-8")) & set(
                OBJECT_PROPERTY_BLOCK
            )
            if stray:
                failures.append(
                    f"{path.relative_to(ROOT)}: redeclares {sorted(stray)} from "
                    f"the ObjectProperty lift block; import {op_module} instead"
                )

    # Rule 8, canonical structure owners.
    div_dir = SOURCE_ROOT / DIVISORIAL_ROOT_DIR
    if not div_dir.is_dir():
        failures.append(
            f"missing {div_dir.relative_to(ROOT)}: it owns the divisorial "
            "charge block; see docs/architecture/cutover-ledger.md"
        )
    else:
        div_declared: set[str] = set()
        for path in sorted(div_dir.glob("*.lean")):
            div_declared |= structure_names(path.read_text(encoding="utf-8"))
        for name in DIVISORIAL_BLOCK:
            if name not in div_declared:
                failures.append(
                    f"{div_dir.relative_to(ROOT)}: no longer declares {name}; "
                    "the divisorial charge block's canonical owner is this subtree"
                )
        for module, (path, _, _) in modules.items():
            if not may_import_geometry(module):
                continue
            stray = structure_names(path.read_text(encoding="utf-8")) & (
                set(DIVISORIAL_BLOCK) | set(HODGE_INDEX_BLOCK)
            )
            if stray:
                failures.append(
                    f"{path.relative_to(ROOT)}: redeclares {sorted(stray)} from "
                    "the divisorial charge block; import "
                    f"{module_of(next(div_dir.glob('Charge.lean')))} or the neutral "
                    "Hodge-index owner instead"
                )

    hodge_root = SOURCE_ROOT / HODGE_INDEX_ROOT
    if not hodge_root.is_file():
        failures.append(
            f"missing {hodge_root.relative_to(ROOT)}: it owns the neutral "
            "Hodge-index block"
        )
    else:
        hodge_declared = structure_names(hodge_root.read_text(encoding="utf-8"))
        for name in HODGE_INDEX_BLOCK:
            if name not in hodge_declared:
                failures.append(
                    f"{hodge_root.relative_to(ROOT)}: no longer declares {name}; "
                    "the neutral Hodge-index block's canonical owner is this file"
                )

    family_root = SOURCE_ROOT / (
        "CategoryTheory/Triangulated/StabilityCondition/CentralCharge/Family.lean"
    )
    if not family_root.is_file() or "ChargeFamily" not in structure_names(
        family_root.read_text(encoding="utf-8") if family_root.is_file() else ""
    ):
        failures.append(
            "CentralCharge/Family.lean must own the ChargeFamily structure"
        )

    # Rule 8, owner existence. Import boundaries were checked uniformly above
    # so the known-answer fixtures exercise the same predicate as the tree.
    for entry in NEUTRAL_CHARGE_ROOTS:
        path = SOURCE_ROOT / entry
        if not path.is_file():
            failures.append(f"missing neutral charge root {path.relative_to(ROOT)}")

    # Rule 9.
    yoneda_root = SOURCE_ROOT / LINEAR_YONEDA_ROOT
    if not yoneda_root.is_file():
        failures.append(
            f"missing {yoneda_root.relative_to(ROOT)}: it owns the linear "
            "Yoneda representability block; see "
            "docs/architecture/cutover-ledger.md"
        )
    else:
        yoneda_module = module_of(yoneda_root)
        yoneda_imports, _ = parse(yoneda_root)
        for imp in yoneda_imports:
            if in_tree(imp, LIBRARY):
                failures.append(
                    f"{yoneda_root.relative_to(ROOT)}: imports {imp}; these "
                    "three helpers are Mathlib's full and faithful "
                    "`linearYoneda` and nothing else"
                )
        yoneda_declared = declared_names(yoneda_root.read_text(encoding="utf-8"))
        for name in LINEAR_YONEDA_BLOCK:
            if name not in yoneda_declared:
                failures.append(
                    f"{yoneda_root.relative_to(ROOT)}: no longer declares "
                    f"{name}; the linear Yoneda block's canonical owner is "
                    "this file"
                )
        for module, (path, _, _) in modules.items():
            if module == yoneda_module:
                continue
            stray = declared_names(path.read_text(encoding="utf-8")) & set(
                LINEAR_YONEDA_BLOCK
            )
            if stray:
                failures.append(
                    f"{path.relative_to(ROOT)}: redeclares {sorted(stray)} "
                    f"from the linear Yoneda block; import {yoneda_module} "
                    "instead"
                )
    serre_root_dir = SOURCE_ROOT / LINEAR_SERRE_ROOT_DIR
    if not serre_root_dir.is_dir():
        failures.append(
            f"missing {serre_root_dir.relative_to(ROOT)}: it owns the k-linear "
            "Serre duality data; see docs/architecture/cutover-ledger.md"
        )
    else:
        serre_root_module = module_of(serre_root_dir.with_suffix(".lean"))
        for module in modules:
            if not (
                module == serre_root_module
                or in_tree(module, serre_root_module)
                or module == module_of(SOURCE_ROOT / LINEAR_YONEDA_ROOT)
            ):
                continue
            reached = sorted(
                dep
                for dep in closure.of(module)
                if in_tree(dep, TRIANGULATED_TREE)
            )
            if reached:
                failures.append(
                    f"{module}: reaches {reached[0]}; the linear Serre root "
                    "exists to be importable without a shift or a "
                    "triangulation (MO1.07)"
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
        and not may_consume_stability(m)
    )
    print(
        f"ok: {len(modules)} modules; only AlgebraicGeometry/ and Development/ "
        f"import geometry; {neutral} of {geometry} geometry modules are "
        f"stability-neutral against {len(STABILITY_CONSUMING_GEOMETRY)} exempt "
        "subcomponents; weak stability is independent of, and structurally "
        f"parented by, Bridgeland stability; {len(RETIRED_PATHS)} retired paths "
        f"absent; the {len(OBJECT_PROPERTY_BLOCK)}-declaration ObjectProperty "
        "lift block is generic and declared once; the "
        f"{len(DIVISORIAL_BLOCK)}-structure divisorial charge block and "
        f"{len(HODGE_INDEX_BLOCK)}-structure neutral Hodge block are declared once; "
        "central-charge roots reach neither walls nor geometry and the paired "
        "functional reaches no wall arrangement; the "
        f"{len(LINEAR_YONEDA_BLOCK)}-declaration linear Yoneda block needs "
        "Mathlib alone and the linear Serre root reaches no triangulated module"
    )
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
