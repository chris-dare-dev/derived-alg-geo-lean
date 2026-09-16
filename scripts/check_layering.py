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
10. **Positive frames, positive planes, and wall loci stay distinct.** The
   frame-to-plane map, orthogonality arrangement, determinant-alignment locus,
   signed-ray locus, and stability-space charge-zero locus have separate
   owners. Retired compressed paths stay absent, and positive frames do not
   import orthogonality finiteness.
9. **The linear Serre root is shift-free.** ``CategoryTheory/Linear/Yoneda.lean``
   needs Mathlib alone, nothing below ``CategoryTheory/Linear/SerreFunctor/``
   reaches ``CategoryTheory/Triangulated`` even transitively, and the three
   linear-Yoneda representability helpers are declared exactly once. This is
   the claim MO1.07 (#1318) moved those files to make true, and it is the kind
   of claim that decays silently: one convenience import from a triangulated
   consumer and the root is no longer importable without a shift.
12. **A numerical model is not a demonstration, and not a scheme.**
   ``Numerical/Models/`` holds formal rank-degree-coordinate models: a ring, a
   grading, a degree map, Chern and Todd coefficients. It reaches neither the
   stability tree nor ``Numerical/Examples/``, which owns the realization maps,
   charges and walls built on those models. The named surface models are
   siblings over one shared carrier, and the arbitrary-divisor-rank charge
   demonstrations reach the shared exponential kernel without passing through
   the scalar ``H``-degree compression. This is MO1.06 (#1317).
13. **Abelian stability, slope stability and Gieseker stability are three
   subjects, not one nest.** ``CategoryTheory/Abelian/Stability/`` reaches no
   ``CategoryTheory/Triangulated`` module, so stability functions and their
   Harder--Narasimhan theory are importable without a shift, a t-structure or a
   heart. Below ``AlgebraicGeometry/Stability/``, ``Slope/`` and ``Gieseker/``
   reach neither each other nor the stability tree; ``Comparison.lean`` reaches
   both and is reached by neither; and ``Purity.lean`` declares ``IsPure``
   exactly once, because it is the one notion the two geometric theories share.
   This is MO1.08 (#1319), and the sheaf-stability exemption rule 3 used to
   grant is gone with it.
14. **The neutral planar core is category-free and stability-free.** Nothing
   below ``Analysis/`` reaches ``CategoryTheory/``, ``AlgebraicGeometry/`` or
   the stability tree, and nothing below it imports ``Mathlib.CategoryTheory``
   either. That is the whole reason MO1.13 (#1324) gave the Euclidean
   perimeter comparison a subject of its own instead of leaving it inside a
   mass-subadditivity proof directory, and it is exactly the kind of claim one
   convenience import erases.
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
    # Added by MO1.13 (#1324), deliberately and after the check rule 6 asks
    # for: the pinned Mathlib has no polygonal-chain length and no perimeter
    # of any kind, so the Euclidean comparison under mass subadditivity had no
    # Mathlib owner to reuse. `Analysis` rather than `Geometry` because the
    # convexity API it consumes, `convexHull`, is owned at the pinned revision
    # by `Mathlib/Analysis/Convex/Hull.lean`. Recorded in the cutover ledger.
    "Analysis",
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
    # The numerical demonstrations: realization maps, charges, walls, slices
    # and regions instantiated on a model. Every module below these three
    # entries reaches the stability tree, and MO1.06 (#1317) is what made that
    # true -- the formal rank-degree-coordinate models they are built on moved
    # to `Numerical/Models/`, which is deliberately absent from this list and
    # is therefore held stability-neutral by rule 3.
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
    f"{GEOMETRY}.Numerical.GrothendieckGroup.CategoricalChargeK3",
    f"{GEOMETRY}.Numerical.Stability",
    # `AlgebraicGeometry/Stability/` was the third entry here until MO1.08
    # (#1319). It instantiates a slope theory, but that theory is abelian and
    # now lives at `CategoryTheory/Abelian/Stability/`, so sheaves, Hilbert
    # polynomials and slopes reach no triangulated stability condition at all.
    # The exemption was removed rather than renamed, and rule 13 below pins the
    # claim that made removing it possible.
)

# Paths removed by a structural cutover, relative to the source root. An entry
# without a suffix names a directory and also forbids its same-named umbrella.
RETIRED_PATHS = (
    # 2026-09-15 MO1.13 (#1324): mass became a sibling of metric, and the
    # Euclidean planar core left the mass-subadditivity proof directory.
    # The finite-sum half-plane bounds went one step further than MO1.08 sent
    # them: that file mentions no category at all, so it owns
    # Analysis/Complex/PhaseFiniteSums.lean rather than a path below
    # CategoryTheory/. MO1.08's own parent entry covers where it used to live.
    "CategoryTheory/Triangulated/StabilityCondition/Metric/Mass",
    "CategoryTheory/Triangulated/StabilityCondition/Weak/Metric",
    "CategoryTheory/Abelian/Stability/FiniteSums.lean",
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
    # 2026-09-14 MO1.03: neutral frames and planes, orthogonality
    # arrangements, determinant alignment, and charge-zero loci received
    # separate owners. Historical declaration spellings live only in the
    # executable restatement bridge.
    "LinearAlgebra/QuadraticForm/PeriodDomain.lean",
    "LinearAlgebra/QuadraticForm/Orientation.lean",
    "LinearAlgebra/QuadraticForm/PositivePairOpen.lean",
    "LinearAlgebra/QuadraticForm/OrientationCocycle.lean",
    "LinearAlgebra/QuadraticForm/WallFiniteness.lean",
    "LinearAlgebra/QuadraticForm/WallRegion.lean",
    "LinearAlgebra/QuadraticForm/CutNonempty.lean",
    "CategoryTheory/Triangulated/StabilityCondition/Walls/ChargeFamily.lean",
    # 2026-09-13 MO1.07: the k-linear Serre duality data and its uniqueness
    # need no shift, so they moved to CategoryTheory/Linear/SerreFunctor/.
    "CategoryTheory/Triangulated/SerreFunctor/Basic.lean",
    "CategoryTheory/Triangulated/SerreFunctor/Uniqueness.lean",
    # 2026-09-13 MO1.11: pseudo-coherence, Tor amplitude and relative
    # perfection are properties of one complex over one morphism, so they moved
    # to AlgebraicGeometry/DerivedCategory/Perfect/, and stalkwise flatness of
    # a module sheaf moved to AlgebraicGeometry/Modules/Flat.lean.
    "AlgebraicGeometry/Moduli/PerfectComplex/Relative.lean",
    # 2026-09-13 MO1.14: four paths that disagreed with the API each file
    # extends. Linear duality on ModuleCat is one subject at ModuleCat's own
    # Mathlib path; the exterior-power file under Sheaf/ constructs presheaf
    # exterior powers; quasicoherent extension closure is about the modules,
    # not the cohomology its proof uses; exterior-power restriction is about
    # module sheaves, not divisors.
    "CategoryTheory/ModuleCat",
    "Algebra/Category/ModuleCat/Sheaf/ExteriorPower.lean",
    "AlgebraicGeometry/Cohomology/Quasicoherent",
    "AlgebraicGeometry/Divisors/ExteriorPower.lean",
    # 2026-09-15 MO1.06: formal rank-degree-coordinate models moved out of the
    # example leaves into AlgebraicGeometry/Numerical/Models/, and the two
    # K3-only charge adapters took a visibly K3 filename. Examples/ keeps the
    # realizations, charges and walls built on those models.
    "AlgebraicGeometry/Numerical/Examples/RankOne.lean",
    "AlgebraicGeometry/Numerical/Examples/DimensionZero",
    "AlgebraicGeometry/Numerical/Examples/Surface/RankOne.lean",
    "AlgebraicGeometry/Numerical/Examples/Surface/K3.lean",
    "AlgebraicGeometry/Numerical/Examples/Surface/K3Mukai.lean",
    "AlgebraicGeometry/Numerical/Examples/Surface/K3MukaiIntegral.lean",
    "AlgebraicGeometry/Numerical/Examples/Surface/Abelian.lean",
    "AlgebraicGeometry/Numerical/Examples/Surface/Enriques.lean",
    "AlgebraicGeometry/Numerical/Examples/Surface/ProjectivePlane.lean",
    "AlgebraicGeometry/Numerical/Examples/Surface/Comparison.lean",
    "AlgebraicGeometry/Numerical/Examples/Threefold/CalabiYau.lean",
    "AlgebraicGeometry/Numerical/Examples/Threefold/LinearSection.lean",
    "AlgebraicGeometry/Numerical/Examples/Threefold/ProjectiveSpace.lean",
    "AlgebraicGeometry/Numerical/Examples/Fourfold/CalabiYau.lean",
    "AlgebraicGeometry/Numerical/Examples/Fourfold/LinearSection.lean",
    "AlgebraicGeometry/Numerical/Examples/Fourfold/ProjectiveSpace.lean",
    "AlgebraicGeometry/Numerical/GrothendieckGroup/CentralCharge.lean",
    "AlgebraicGeometry/Numerical/GrothendieckGroup/CategoricalCharge.lean",
    # 2026-09-15 MO1.08: abelian stability functions and their
    # Harder-Narasimhan theory moved to CategoryTheory/Abelian/Stability/, with
    # the weak variants as its children and the class datum as its neutral
    # core. Only the heart adapter stayed behind, at
    # Weak/Foundation/HeartDatum.lean.
    "CategoryTheory/Triangulated/StabilityCondition/Weak/Foundation/"
    "StabilityFunction",
    "CategoryTheory/Triangulated/StabilityCondition/Weak/Charge.lean",
    # 2026-09-15 MO1.08: the mu-slope datum and the mu-Harder-Narasimhan
    # existence theorem are not Gieseker theory and stopped being filed under
    # it; the shared Hilbert-polynomial data moved up to the common parent, and
    # the statements that mention both theories moved to Comparison.lean.
    "AlgebraicGeometry/Stability/Gieseker/MuStability.lean",
    "AlgebraicGeometry/Stability/Gieseker/HilbertPolynomial.lean",
    "AlgebraicGeometry/Stability/Gieseker/Coefficients.lean",
    "AlgebraicGeometry/Stability/Gieseker/HarderNarasimhan",
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
    f"{LIBRARY}.LinearAlgebra.QuadraticForm.PositivePlane",
    f"{LIBRARY}.LinearAlgebra.QuadraticForm.OrthogonalityLocus",
    f"{LIBRARY}.LinearAlgebra.QuadraticForm.OrthogonalityFiniteness",
    f"{LIBRARY}.LinearAlgebra.QuadraticForm.OrthogonalityRegion",
    f"{LIBRARY}.LinearAlgebra.QuadraticForm.PositiveFrame",
)
# Rule 10. MO1.03 gives the distinct carriers and loci owners that match
# their actual equations. These are declaration names rather than a common
# superclass because their codimensions and categorical content differ.
POSITIVE_PLANE_ROOT = "LinearAlgebra/QuadraticForm/PositivePlane.lean"
POSITIVE_FRAME_ROOT = "LinearAlgebra/QuadraticForm/PositiveFrame.lean"
ORTHOGONALITY_LOCUS_ROOT = "LinearAlgebra/QuadraticForm/OrthogonalityLocus.lean"
ALIGNMENT_LOCUS_ROOT = (
    "CategoryTheory/Triangulated/StabilityCondition/Walls/Alignment.lean"
)
CHARGE_FAMILY_ROOT = (
    "CategoryTheory/Triangulated/StabilityCondition/CentralCharge/Family.lean"
)
CHARGE_ZERO_ROOT = (
    "CategoryTheory/Triangulated/StabilityCondition/Chambers/Basic.lean"
)
# Rule 11. MO1.05 keeps numerical foundations upstream of their named and
# dimension-specific consumers.
SQRT_TODD_ROOT = f"{GEOMETRY}.Numerical.Mukai.SqrtTodd"
SLOPE_ROOT = f"{GEOMETRY}.Numerical.Stability.Slope"
POLARISED_TRANSPORT_ROOT = (
    f"{GEOMETRY}.Numerical.Stability.PolarisedWallTransport"
)
NUMERICAL_SPECIALIZATIONS = (
    f"{GEOMETRY}.Numerical.RiemannRoch.K3",
    f"{GEOMETRY}.Numerical.Examples",
    # MO1.06 moved the named and dimension-specific models here; rule 11 has to
    # follow them or a generic root could import `ℙ²` again without failing.
    f"{GEOMETRY}.Numerical.Models",
    f"{GEOMETRY}.Numerical.Stability.WallTransport",
    f"{GEOMETRY}.Numerical.Stability.ThreefoldWallTransport",
)
# Rule 12. MO1.06 separates the formal numerical models from the
# demonstrations built on them, and keeps the multi-divisor charge a sibling
# input of the exponential kernel rather than a child of the compressed
# `H`-degree families.
NUMERICAL_MODELS_TREE = f"{GEOMETRY}.Numerical.Models"
NUMERICAL_DEMONSTRATIONS_TREE = f"{GEOMETRY}.Numerical.Examples"
NUMERICAL_MODELS_UMBRELLA = "AlgebraicGeometry/Numerical/Models.lean"
MO1_06_OWNERS = {
    "AlgebraicGeometry/Numerical/Models/MonogenicRing.lean": (
        "rankOneNumericalRing",
        "rankOneNumericalVariety",
    ),
    "AlgebraicGeometry/Numerical/Models/Surface/RankOne.lean": (
        "surfaceNumericalRing",
        "surfaceCh",
    ),
    "AlgebraicGeometry/Numerical/GrothendieckGroup/CentralChargeK3.lean": (
        "numericalCharge",
        "numericalChargeHom",
    ),
}
# Each named surface model reaches the shared carrier and no sibling model.
SURFACE_MODEL_CARRIER = f"{GEOMETRY}.Numerical.Models.Surface.RankOne"
SURFACE_MODEL_SIBLINGS = (
    f"{GEOMETRY}.Numerical.Models.Surface.K3",
    f"{GEOMETRY}.Numerical.Models.Surface.Abelian",
    f"{GEOMETRY}.Numerical.Models.Surface.Enriques",
    f"{GEOMETRY}.Numerical.Models.Surface.ProjectivePlane",
)
# The arbitrary-divisor-rank branch: two independent classes in the full real
# divisor space, with no degree vector to hand the kernel. `Exp.ofMoments`
# takes a moment sequence precisely so that this branch and the compressed
# families are siblings under it.
ARBITRARY_RANK_CHARGE_DEMONSTRATIONS = (
    f"{GEOMETRY}.Numerical.Examples.Surface.SmoothQuadric",
    f"{GEOMETRY}.Numerical.Examples.Surface.SmoothQuadricCharge",
    f"{GEOMETRY}.Numerical.Examples.Surface.BlowUpPlane",
    f"{GEOMETRY}.Numerical.Examples.Surface.BlowUpPlaneWalls",
    f"{GEOMETRY}.Numerical.Examples.Surface.BlowUpPlaneSlice",
)
EXPONENTIAL_KERNEL_ROOT = f"{STABILITY_ROOT}.CentralCharge.Exponential.Kernel"
ARBITRARY_RANK_CHARGE_BRANCH = (
    f"{STABILITY_ROOT}.CentralCharge.Exponential.Divisorial"
)
COMPRESSED_DEGREE_BRANCH = (
    f"{STABILITY_ROOT}.CentralCharge.Exponential.Comparison"
)
# The compressed branch: a vector of `H`-degrees, which is not injective once
# the Picard rank exceeds one.
SCALAR_DEGREE_COMPRESSION = (
    f"{STABILITY_ROOT}.CentralCharge.Numerical",
    f"{GEOMETRY}.Numerical.Models.MonogenicRing",
    f"{GEOMETRY}.Numerical.Models.Surface.RankOne",
    f"{GEOMETRY}.Numerical.Stability.PolarisedWallTransport",
)
# Rule 13. MO1.08 (#1319) unnested three subjects. The abelian stability
# functions were a foundation directory inside the triangulated theory they are
# a foundation for; the mu-slope datum and the mu-Harder-Narasimhan existence
# theorem were children of the Gieseker directory although neither mentions the
# Gieseker order. Each claim below is one a single convenience import would
# silently undo, which is why all three are pinned rather than documented.
ABELIAN_STABILITY_TREE = f"{LIBRARY}.CategoryTheory.Abelian.Stability"
ABELIAN_STABILITY_UMBRELLA = "CategoryTheory/Abelian/Stability.lean"
ABELIAN_STABILITY_WEAK_UMBRELLA = "CategoryTheory/Abelian/Stability/Weak.lean"
HEART_DATUM_ADAPTER = (
    "CategoryTheory/Triangulated/StabilityCondition/Weak/Foundation/"
    "HeartDatum.lean"
)
SHEAF_STABILITY_TREE = f"{GEOMETRY}.Stability"
SHEAF_SLOPE_TREE = f"{SHEAF_STABILITY_TREE}.Slope"
SHEAF_GIESEKER_TREE = f"{SHEAF_STABILITY_TREE}.Gieseker"
SHEAF_COMPARISON_MODULE = f"{SHEAF_STABILITY_TREE}.Comparison"
SHEAF_PURITY_ROOT = "AlgebraicGeometry/Stability/Purity.lean"
SHEAF_PURITY_BLOCK = ("IsPure",)

MO1_03_OWNERS = {
    POSITIVE_PLANE_ROOT: ("IsPositivePlane", "positivePlanes"),
    POSITIVE_FRAME_ROOT: (
        "framePlane",
        "IsPositiveFrame",
        "positiveFrames",
        "forgetPositiveFrame",
    ),
    ORTHOGONALITY_LOCUS_ROOT: (
        "orthogonalityLocus",
        "positivePlanesAway",
    ),
    CHARGE_FAMILY_ROOT: ("zeroLocus",),
    ALIGNMENT_LOCUS_ROOT: (
        "alignmentValue",
        "alignmentLocus",
        "positiveRayLocus",
    ),
    CHARGE_ZERO_ROOT: (
        "stabilityChargeFamily",
        "chargeZeroLocus",
        "chargeRegularLocus",
    ),
}
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

# Rule 14. `Analysis/` is the neutral planar subject MO1.13 (#1324) added:
# the polygonal-path carrier, the real continuous linear functionals on `C`
# and the Euclidean perimeter comparison, none of which mentions an object,
# a filtration or a stability function. The point of the move is that it can
# be imported with no category theory and no stability, so that is checked
# rather than asserted in a docstring.
ANALYSIS_ROOT = f"{LIBRARY}.Analysis"
ANALYSIS_FORBIDDEN_PREFIXES = (
    f"{LIBRARY}.CategoryTheory",
    f"{LIBRARY}.AlgebraicGeometry",
    f"{LIBRARY}.Development",
    "Mathlib.CategoryTheory",
    "Mathlib.AlgebraicGeometry",
)
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
    if in_tree(module, ABELIAN_STABILITY_TREE):
        forbidden = sorted(
            dep for dep in reached if in_tree(dep, TRIANGULATED_TREE)
        )
        if forbidden:
            return [
                f"{label}: reaches {forbidden[0]}; abelian stability functions "
                "and their Harder-Narasimhan theory are importable without a "
                "shift, a t-structure or a heart (MO1.08)"
            ]
    if in_tree(module, SHEAF_SLOPE_TREE):
        forbidden = sorted(
            dep for dep in reached if in_tree(dep, SHEAF_GIESEKER_TREE)
        )
        if forbidden:
            return [
                f"{label}: reaches {forbidden[0]}; mu-slope stability and its "
                "Harder-Narasimhan theory are a sibling of Gieseker stability "
                "over the shared Hilbert-polynomial data, not a child of it. "
                "Statements mentioning both belong in "
                f"{SHEAF_COMPARISON_MODULE}"
            ]
    if in_tree(module, SHEAF_GIESEKER_TREE):
        forbidden = sorted(
            dep for dep in reached if in_tree(dep, SHEAF_SLOPE_TREE)
        )
        if forbidden:
            return [
                f"{label}: reaches {forbidden[0]}; the Gieseker order is "
                "defined without a slope, and the comparison between the two "
                f"theories belongs in {SHEAF_COMPARISON_MODULE}"
            ]
    if module in (SQRT_TODD_ROOT, SLOPE_ROOT, POLARISED_TRANSPORT_ROOT):
        forbidden = sorted(
            dep for dep in reached
            if any(in_tree(dep, root) for root in NUMERICAL_SPECIALIZATIONS)
        )
        if forbidden:
            return [
                f"{label}: reaches {forbidden[0]}; generic numerical roots "
                "must not import K3, surface, or dimension-specific consumers"
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

    # Rule 10, declaration owners and the one import edge that matters to the
    # frame/plane split. The executable-only historical aliases are outside
    # SOURCE_ROOT and therefore cannot satisfy these checks.
    for entry, names in MO1_03_OWNERS.items():
        path = SOURCE_ROOT / entry
        if not path.is_file():
            failures.append(f"missing MO1.03 owner {path.relative_to(ROOT)}")
            continue
        declared = declared_names(path.read_text(encoding="utf-8")) | structure_names(
            path.read_text(encoding="utf-8")
        )
        for name in names:
            if name not in declared:
                failures.append(
                    f"{path.relative_to(ROOT)}: no longer declares {name}; "
                    "the frame/plane/locus split requires this canonical owner"
                )

    # Rule 12, MO1.06. Owners first, then the four claims the split makes.
    for entry, names in MO1_06_OWNERS.items():
        path = SOURCE_ROOT / entry
        if not path.is_file():
            failures.append(f"missing MO1.06 owner {path.relative_to(ROOT)}")
            continue
        text = path.read_text(encoding="utf-8")
        declared = declared_names(text) | structure_names(text)
        for name in names:
            if name not in declared:
                failures.append(
                    f"{path.relative_to(ROOT)}: no longer declares {name}; "
                    "the model/demonstration split requires this canonical owner"
                )
    if not (SOURCE_ROOT / NUMERICAL_MODELS_UMBRELLA).is_file():
        failures.append(
            f"missing {NUMERICAL_MODELS_UMBRELLA}: the formal numerical models "
            "need an umbrella of their own, separate from the demonstrations"
        )

    # (a) No model may buy a stability exemption. Rule 3 already holds the tree
    # neutral; this keeps a future edit from adding `Numerical.Models` to the
    # exempt list instead of fixing the import that made it necessary.
    for root in STABILITY_CONSUMING_GEOMETRY:
        if in_tree(root, NUMERICAL_MODELS_TREE):
            failures.append(
                f"{root}: a formal numerical model may not be exempted from "
                "rule 3; move the charge or wall material to "
                "Numerical/Examples/ instead"
            )

    # (b) Models are upstream of the demonstrations built on them.
    for module in sorted(modules):
        if not in_tree(module, NUMERICAL_MODELS_TREE):
            continue
        reached = sorted(
            dep
            for dep in closure.of(module)
            if in_tree(dep, NUMERICAL_DEMONSTRATIONS_TREE)
        )
        if reached:
            failures.append(
                f"{module}: reaches {reached[0]}; a numerical model is "
                "upstream of the realizations, charges and walls demonstrated "
                "on it"
            )

    # (c) The named surface models are siblings over one shared carrier.
    for sibling in SURFACE_MODEL_SIBLINGS:
        if sibling not in modules:
            failures.append(
                f"missing named surface model {sibling}; K3, abelian, Enriques "
                "and the projective plane are siblings over "
                f"{SURFACE_MODEL_CARRIER}"
            )
            continue
        reached = closure.of(sibling)
        if SURFACE_MODEL_CARRIER not in reached:
            failures.append(
                f"{sibling}: does not reach {SURFACE_MODEL_CARRIER}; a named "
                "surface model specializes the shared rank-one carrier"
            )
        for other in SURFACE_MODEL_SIBLINGS:
            if other != sibling and other in reached:
                failures.append(
                    f"{sibling}: reaches sibling model {other}; named surface "
                    "models share a carrier, not each other"
                )

    # (d) The arbitrary-divisor-rank charge is a sibling input of the shared
    # exponential kernel, not a child of the compressed `H`-degree families.
    # Both branches must reach the kernel; only the compressed one may reach a
    # degree vector.
    for branch in (ARBITRARY_RANK_CHARGE_BRANCH, COMPRESSED_DEGREE_BRANCH):
        if branch not in modules:
            failures.append(
                f"missing {branch}; the exponential kernel needs both of its "
                "input branches to stay a shared root"
            )
        elif EXPONENTIAL_KERNEL_ROOT not in closure.of(branch):
            failures.append(
                f"{branch}: no longer reaches {EXPONENTIAL_KERNEL_ROOT}; the "
                "two charge branches are siblings under one kernel"
            )
    if ARBITRARY_RANK_CHARGE_BRANCH in modules:
        reached = closure.of(ARBITRARY_RANK_CHARGE_BRANCH)
        forbidden = sorted(
            dep
            for dep in reached
            if dep == COMPRESSED_DEGREE_BRANCH
            or any(in_tree(dep, root) for root in SCALAR_DEGREE_COMPRESSION)
        )
        if forbidden:
            failures.append(
                f"{ARBITRARY_RANK_CHARGE_BRANCH}: reaches {forbidden[0]}; the "
                "multi-divisor charge takes two classes in the full real "
                "divisor space, has no degree vector to hand the kernel, and "
                "is therefore a sibling of the compressed families rather "
                "than a child of them"
            )
    # The geometry demonstrations of that branch keep the same discipline: a
    # rank-two or rank-three divisor model does not import the rank-one
    # carrier or the scalar polarised transport to obtain its charge.
    for module in ARBITRARY_RANK_CHARGE_DEMONSTRATIONS:
        if module not in modules:
            failures.append(
                f"missing arbitrary-divisor-rank demonstration {module}; the "
                "multi-divisor charge branch has no other witness"
            )
            continue
        direct = set(modules[module][1])
        forbidden = sorted(
            dep
            for dep in direct
            if any(in_tree(dep, root) for root in SCALAR_DEGREE_COMPRESSION)
        )
        if forbidden:
            failures.append(
                f"{module}: imports {forbidden[0]}; an arbitrary-rank divisor "
                "model builds its charge from the intersection form, not by "
                "specializing the lossy scalar H-degree compression"
            )

    # Rule 13, MO1.08. The closure claims are checked uniformly in
    # `owner_boundary_failures` above, so the fixtures exercise the same
    # predicate; what is left here is the existence of the owners, the one
    # claim about the comparison module, and the single declaration of IsPure.
    for entry in (
        ABELIAN_STABILITY_UMBRELLA,
        ABELIAN_STABILITY_WEAK_UMBRELLA,
        HEART_DATUM_ADAPTER,
        SHEAF_PURITY_ROOT,
    ):
        if not (SOURCE_ROOT / entry).is_file():
            failures.append(
                f"missing MO1.08 owner {entry}; see "
                "docs/architecture/cutover-ledger.md"
            )

    # No module below AlgebraicGeometry/Stability/ may buy back the rule 3
    # exemption MO1.08 removed. The same guard rule 12 puts on numerical models.
    for root in STABILITY_CONSUMING_GEOMETRY:
        if in_tree(root, SHEAF_STABILITY_TREE):
            failures.append(
                f"{root}: stability of sheaves may not be exempted from rule "
                "3; it instantiates the abelian slope theory at "
                f"{ABELIAN_STABILITY_TREE} and needs no stability condition"
            )

    # The comparison owner joins the two geometric theories and is joined by
    # neither. An empty Comparison.lean with the statements left in a sibling
    # would pass the two closure checks above and defeat the point of the row.
    if SHEAF_COMPARISON_MODULE not in modules:
        failures.append(
            f"missing {SHEAF_COMPARISON_MODULE}; the slope/Gieseker comparison "
            "needs an owner that is not either theory"
        )
    else:
        reached = closure.of(SHEAF_COMPARISON_MODULE)
        for tree in (SHEAF_SLOPE_TREE, SHEAF_GIESEKER_TREE):
            if not any(in_tree(dep, tree) for dep in reached):
                failures.append(
                    f"{SHEAF_COMPARISON_MODULE}: does not reach {tree}; the "
                    "comparison owner is the module that sees both theories"
                )
        for module in sorted(modules):
            if not (
                in_tree(module, SHEAF_SLOPE_TREE)
                or in_tree(module, SHEAF_GIESEKER_TREE)
            ):
                continue
            if SHEAF_COMPARISON_MODULE in closure.of(module):
                failures.append(
                    f"{module}: reaches {SHEAF_COMPARISON_MODULE}; a theory "
                    "does not import its own comparison with another one"
                )

    purity_root = SOURCE_ROOT / SHEAF_PURITY_ROOT
    if purity_root.is_file():
        purity_module = module_of(purity_root)
        purity_declared = declared_names(purity_root.read_text(encoding="utf-8"))
        for name in SHEAF_PURITY_BLOCK:
            if name not in purity_declared:
                failures.append(
                    f"{purity_root.relative_to(ROOT)}: no longer declares "
                    f"{name}; purity is what the slope and Gieseker theories "
                    "share, and it has one owner"
                )
        for module, (path, _, _) in modules.items():
            if module == purity_module:
                continue
            stray = declared_names(path.read_text(encoding="utf-8")) & set(
                SHEAF_PURITY_BLOCK
            )
            if stray:
                failures.append(
                    f"{path.relative_to(ROOT)}: redeclares {sorted(stray)} "
                    f"from the purity block; import {purity_module} instead"
                )

    positive_frame_module = module_of(SOURCE_ROOT / POSITIVE_FRAME_ROOT)
    forbidden_frame_dependencies = (
        f"{LIBRARY}.LinearAlgebra.QuadraticForm.OrthogonalityFiniteness",
        f"{LIBRARY}.LinearAlgebra.QuadraticForm.OrthogonalityRegion",
    )
    if positive_frame_module in modules:
        reached = closure.of(positive_frame_module)
        for dependency in forbidden_frame_dependencies:
            if dependency in reached:
                failures.append(
                    f"{positive_frame_module}: reaches {dependency}; positive "
                    "frames forget to positive planes and do not depend on an "
                    "orthogonality arrangement or its finiteness theorem"
                )

    all_library_text = "\n".join(
        path.read_text(encoding="utf-8") for path, _, _ in modules.values()
    )
    if "RealCodimensionOneSubmanifold" in all_library_text:
        failures.append(
            "RealCodimensionOneSubmanifold appears in the library; MO1.03 "
            "forbids a common codimension-one parent for charge-zero, "
            "alignment, and signed-ray loci"
        )

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

    # Rule 14.
    analysis_modules = [
        m for m in modules if m == ANALYSIS_ROOT or in_tree(m, ANALYSIS_ROOT)
    ]
    if not analysis_modules:
        failures.append(
            f"missing {ANALYSIS_ROOT}: it owns the neutral planar core -- the "
            "polygonal-path carrier, the real continuous linear functionals on "
            "the complex plane, and the Euclidean perimeter comparison; see "
            "docs/architecture/cutover-ledger.md"
        )
    for module in analysis_modules:
        reached = sorted(
            dep
            for dep in closure.of(module)
            if dep != module
            and any(
                dep == prefix or dep.startswith(prefix + ".")
                for prefix in ANALYSIS_FORBIDDEN_PREFIXES
            )
        )
        if reached:
            failures.append(
                f"{module}: reaches {reached[0]}; the neutral planar core "
                "exists to be importable with no category theory and no "
                "stability (MO1.13)"
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
        "functional reaches no wall arrangement; the positive-plane, "
        "positive-frame, orthogonality, charge-zero, determinant-alignment, "
        "and signed-ray owners are distinct, with no common codimension-one "
        "parent; the "
        f"{len(LINEAR_YONEDA_BLOCK)}-declaration linear Yoneda block needs "
        "Mathlib alone and the linear Serre root reaches no triangulated module; "
        "generic square-root, slope, and polarised-transport roots reach no "
        "K3, surface, or dimension-specific consumers; the "
        f"{len(MO1_06_OWNERS)} numerical-model owners exist, no model reaches "
        "a demonstration, the "
        f"{len(SURFACE_MODEL_SIBLINGS)} named surface models share one carrier "
        "and no sibling, and the arbitrary-divisor-rank charge reaches the "
        "exponential kernel without a degree vector; abelian stability reaches "
        "no triangulated module, sheaf slope and Gieseker stability reach "
        "neither each other nor the stability tree, and IsPure is declared once; "
        f"the {len(analysis_modules)} neutral planar modules below Analysis/ "
        "reach no category, no scheme and no stability condition"
    )
    return 0


if __name__ == "__main__":
    force_utf8_output()
    sys.exit(main())
