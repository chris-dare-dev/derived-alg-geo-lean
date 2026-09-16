# Dependency direction

This document records the implemented broad dependency checks and the current
import map for `DerivedAlgGeo/`. Mathlib's subjects are not a total hierarchy.
The finer foundation/application policy is in
[mathematical-ownership.md](mathematical-ownership.md); its pending source
cutovers are tracked in [the ledger](cutover-ledger.md).

## Subjects are not a tower

`Mathlib/Algebra/Homology/HomologicalComplex.lean` imports
`Mathlib.CategoryTheory.Subobject.Limits`; `Mathlib/CategoryTheory/Linear/Basic.lean`
imports `Mathlib.Algebra.Algebra.Defs`. Algebra and category theory import
each other, and so do topology and category theory. A rank order between
subjects would be false the moment `Algebra/Homology/DerivedCategory/` exists
here, so there is none, and `scripts/check_layering.py` does not look for
subject-level cycles. Lean rejects module-level cycles, which is the only
acyclicity Mathlib has either.

The former rank model (`Algebra` 0, `CategoryTheory` 1, `Topology` 2,
`AlgebraicGeometry` 3, a virtual `GeometryInstances` 4, `Development` 5) is
retired together with the `Instances/AlgebraicGeometry` leaves it existed to
classify.

## The policy edges

These broad rules are implemented in `scripts/check_layering.py`, with
known-answer fixtures under `scripts/fixtures/layering/`. They are not the
complete mathematical ownership policy.

1. **Geometry firewall.** Only modules below `AlgebraicGeometry/` and
   `Development/` import `DerivedAlgGeo.AlgebraicGeometry` or
   `Mathlib.AlgebraicGeometry`, and only they declare into the
   `AlgebraicGeometry` namespace. Everything else in the library is usable
   without schemes. The two aggregation roots `DerivedAlgGeo.lean` and
   `DerivedAlgGeoSweep.lean` import everything and own nothing.
2. **`Development/` is a leaf.** No stable module imports it.
3. **Stability-neutral geometry.** A module below `AlgebraicGeometry/` that is
   not below one of the eight subcomponents that exist to consume stability
   never reaches the stability tree, even transitively. The eight are
   `DerivedCategory/Stability/`, `Moduli/HarderNarasimhan/`,
   `Moduli/Semistability/`, `Numerical/Stability/`,
   `Numerical/Examples/Surface/`, `Numerical/Examples/Threefold/`,
   `Numerical/Examples/Fourfold/` and
   `Numerical/GrothendieckGroup/CategoricalChargeK3.lean`.
   A same-named umbrella over one of them re-exports it and is exempt as an
   umbrella only; its other children are not. This keeps `Dᵇ(Coh X)`, `Dqc`,
   coherent sheaves, and cohomology importable without Bridgeland stability.
   Before 2026-09-13 the exemption named the whole `Moduli/`, `Numerical/`,
   `Stability/` and `DerivedCategory/Stability/` subtrees, which exempted 122
   modules to excuse the 60 that use the tree; MO1.01 (#1312) narrowed it.
   `Numerical/Examples/Fourfold/` was neutral at that moment and stopped being
   so the same day, when #1225 gave the fourfold models their wall families.
   MO1.06 (#1317) made the three `Numerical/Examples/` entries exact by moving
   the formal models to `Numerical/Models/`, which is held neutral. MO1.08
   (#1319) removed the ninth entry, `Stability/Gieseker/`: the slope theory
   sheaf stability instantiates is abelian, it moved to
   `CategoryTheory/Abelian/Stability/`, and the whole `Stability/` subtree is
   now held neutral by this rule rather than exempted from it.
4. **Weak stability is independent of Bridgeland stability.** No module of the
   weak theory imports the Bridgeland theory, and
   `PreStabilityCondition` structurally `extends toWeak :
   WeakPreStabilityCondition` rather than copying its fields.
5. **Retired paths stay retired.** The gate carries the list of paths removed
   by past cutovers so that a shim cannot drift back.
6. **A new top-level subject is deliberate.** A directory directly below the
   source root must be one of the Mathlib subjects the repository uses, named
   in the gate's `KNOWN_SUBJECTS`.
7. **A numerical model is not a demonstration.** `Numerical/Models/` holds
   formal rank--degree--coordinate models -- a ring, a grading, a degree map,
   Chern and Todd coefficients -- and reaches neither the stability tree nor
   `Numerical/Examples/`, which owns the realization maps, charges and walls
   built on them. The four named surface models share one carrier and import
   no sibling, and the arbitrary-divisor-rank charge reaches the exponential
   kernel without passing through the scalar `H`-degree compression. MO1.06
   (#1317).
8. **Abelian stability, slope stability and Gieseker stability are three
   subjects.** `CategoryTheory/Abelian/Stability/` -- stability functions, their
   Harder--Narasimhan theory, and the `Weak/` variants below it -- reaches no
   `CategoryTheory/Triangulated` module, so it is importable without a shift, a
   t-structure or a heart. Below `AlgebraicGeometry/Stability/`, `Slope/` and
   `Gieseker/` are siblings over the shared `HilbertPolynomial.lean`,
   `Coefficients.lean` and `Purity.lean`: neither reaches the other,
   `Comparison.lean` reaches both and is reached by neither, and `IsPure` is
   declared exactly once. MO1.08 (#1319).

## Component boundaries and coverage limits

New generic roots must not import their specializations or downstream
comparisons, including transitively through umbrellas. The stability exemption
does not authorize such imports. Since 2026-09-13 it is also no longer broad:
rule 3 names nine subcomponents, so `Numerical/Core/`, `Numerical/Mukai/`,
`Numerical/RiemannRoch/`, `Numerical/Specializations/` and `Numerical/Models/`
are mechanically held to being separate from the charge and geometric
comparison consumers rather than only asked to be. #1316 and #1317 split the
numerical subtrees, so seven of those nine entries are now exact: every module
below them reaches the stability tree. `Stability/Gieseker/` was the eighth;
MO1.08 (#1319) removed it from the list altogether, because the subtree no
longer reaches the stability tree at all. A parent importing its own
specialization *inside* `Numerical/Stability/`, the one entry that still mixes,
stays a review obligation.
The gate's hard-coded divisorial root is a source location to migrate in
#1313, not a rule that charge construction must remain in Walls.

MO1 cutovers add focused component checks and regression fixtures with the
source move. Preserve the broad firewalls and umbrella coverage while doing
so. A documentation update neither installs these checks nor means all
existing reverse imports have been repaired.

## AlgebraicGeometry sublayers

Geometry is organized by object, and a few of its subtrees exist to consume
stability conditions. The finer direction below `AlgebraicGeometry/` is:

```text
Modules, ProjectiveSpectrum, Cohomology, Divisors, Duality,
IntersectionTheory, RiemannRoch, Sites, Stacks, Surface, Variety, Spec,
Morphisms
        stability-neutral: never reach the stability tree

DerivedCategory
  ├─ Basic, Coherent, Dqc, Families, Tensor,
  │  TwistedPushforward, FourierMukai                  stability-neutral
  └─ Stability                                         imports the stability tree;
                                                        omitted by the DerivedCategory
                                                        umbrella, imported by the
                                                        AlgebraicGeometry umbrella
Moduli
  ├─ HarderNarasimhan, Semistability                  may import the stability tree
  └─ PerfectComplex, Quot                             stability-neutral
Numerical
  ├─ Stability                                        may import the stability tree
  ├─ Examples/{Surface,Threefold,Fourfold}            realizations, charges and walls
                                                        demonstrated on a model; every
                                                        module here imports the tree
  ├─ GrothendieckGroup/CategoricalChargeK3            may import the stability tree
  ├─ Models                                           formal rank-degree-coordinate
                                                        models; stability-neutral, and
                                                        upstream of Examples
  └─ Core, Mukai, RiemannRoch, Specializations        stability-neutral
Stability
  ├─ HilbertPolynomial, Coefficients, Purity          shared polarization data
  ├─ Slope, Gieseker                                  siblings; neither imports the
  │                                                     other, and both are
  │                                                     stability-neutral -- the slope
  │                                                     theory they instantiate is
  │                                                     CategoryTheory/Abelian/Stability
  └─ Comparison                                       imports both siblings; imported
                                                        by neither
```

Each same-named umbrella above a "may import" row re-exports it and is exempt
as an umbrella; the exemption does not reach the umbrella's other children.

A geometric realization of a categorical interface sits with the geometric
object it is about: the `IsCompatibleWithTriangulation` instance for
`Dᵇ(Coh X)` in `DerivedCategory/Tensor/Coherent.lean`,
the scheme probes and semistable-locus probes in `Moduli/Semistability/`, the
relative Harder--Narasimhan problem in `Moduli/HarderNarasimhan/`, and the
base-change and Fourier--Mukai actions on stability data in
`DerivedCategory/Stability/`. A declaration in such a file may keep the
namespace of the categorical structure it extends so that dot notation
resolves; the file's path records what it is about.

## Where each theory currently lives

This map describes existing modules. The ownership policy and cutover ledger
identify mixed roots still to split, including dg H⁰ under DGEnhancement.
Their appearance here is not permission to extend a misplaced foundation in
place. Derived operations (#1321) and perfectness (#1322) are no longer among
them.

Arrows point from a refinement or consumer to the root it builds on.

```text
Algebra/Homology
  ├─→ DerivedCategory                         extends Mathlib's DerivedCategory
  │     ├─→ TStructure, ExactFunctor, Homology, CohomologyObjectProperty
  │     ├─→ SingleTriangle                    identity/composition laws for maps
  │     ├─→ Opposite → LinearDual
  │     ├─→ Ext (adjunction, dimension shift, resolution naturality)
  │     └─→ KProjective, BoundedAboveProjective
  ├─→ HomotopyCategory                        extends Mathlib's HomotopyCategory
  │     ├─→ Bounded
  │     └─→ DGEnhancement                     C^dg enhances K(A); agreement with
  │                                           Mathlib's shift and triangles
  ├─→ DGCategory                              bespoke class on HomComplex (ADR-0010/0011)
  │     ├─→ Functor, Opposite, Product, Linear, Shift, H0, LinearH0
  │     ├─→ NaturalTransformationH0            closed degree-zero transformations on H⁰
  │     ├─→ AdjunctionH0                       a dg adjunction as a Mathlib adjunction
  │     │     └─→ AdjunctionH0Presentation           transport through equivalences to named functors
  │     ├─→ Pretriangulated                   cones, shifts, rotation, chosen homotopy squares
  │     │     ├─→ ConeCategory                chosen cones and homotopy-coherent maps
  │     │     └─→ Functor                     composable shift/cone preservation capabilities
  │     └─→ Model/Complexes                   C^dg(A)
  └─→ SpectralSequence                        filtered and total complexes

Algebra/Category/ModuleCat/Sheaf              extends Mathlib's SheafOfModules
  ├─→ Exactness, Over, GeneratingSections, Invertible, Tensor, ExteriorPower
  └─→ Presentation
        ├─→ Transport, Finite, Over
        ├─→ Isomorphism, Locality
        └─→ Zero, Extensions

CategoryTheory/Sites
  ├─→ Over, CoversTop                         arbitrary sites
  ├─→ Sheaves                                 constant pullback, cohomology pushforward, CoversTop detection
  ├─→ SheafCohomology/Cech                    extends Mathlib's Čech cohomology
  └─→ Descent/StackInGroupoids                extends Mathlib's IsStack

CategoryTheory/Bicategory
  ├─→ Adjunction                              adjunctions of 1-morphisms; Cat specialization
  └─→ Functor/Cat                             pseudofunctor transport; ObjectProperty/UniversallyStable

CategoryTheory/Abelian
  ├─→ SerreClass, QuasiAbelian
  └─→ Stability                               stability functions on an abelian category,
        │                                     their HN theory, and the neutral ClassDatum;
        │                                     needs no shift, t-structure or heart
        └─→ Weak                              the variant whose charge may vanish; the
                                              stronger theory one level up imports it

CategoryTheory/Shift
  └─→ FunctorCategory                         pointwise shift on `X ⥤ Y`; strict
                                              commutation of the evaluations

CategoryTheory/Triangulated
  ├─→ PretriangulatedAxioms, TStructure, PostnikovTower, ExtensionClosure, QuasiAbelian
  ├─→ TriangleFunctorNormalization             first-map transport for triangle-valued functors
  ├─→ FullSubcategory                         objectwise triangle and map lifts
  ├─→ GrothendieckGroup                        K₀, realizations, Euler forms
  ├─→ CompactlyGenerated, SemiorthogonalDecomposition, SphericalTwist
  ├─→ FourierMukai                            generic kernel autoequivalences;
  │                                           kernels vary through `kernelTransform`,
  │                                           enhanced cones map pointwise to transform triangles;
  │                                           consumes presented dg adjunction triangles through
  │                                           objectwise, supplied-natural, and shift-compatible layers
  ├─→ Families                                pseudofunctorial fiber categories
  ├─→ DGEnhancement                           enhancement interface, H⁰ triangulation,
  │                                           functorial distinguished cone triangles and
  │                                           presented dg-adjunction cone triangles and their
  │                                           conventional cotwist inverse rotation;
  │                                           H0/Triangle owns the triangles;
  │                                           H0/{Functor,FunctorTransport} own transport of
  │                                           dg-functor capabilities through H⁰ and ordinary
  │                                           equivalences
  └─→ StabilityCondition                      Bridgeland stability (canonical concept)
        ├─→ Weak                              weak stability: the dependency parent
        │     └─→ Foundation, Families, HarderNarasimhan, Support, Tilting
        │           Foundation owns slicings, interval categories and the heart
        │           class datum, and consumes CategoryTheory/Abelian/Stability
        ├─→ Foundation (Deformation), Phase, Metric, Symmetry, Support, Walls
        └─→ Families                          abstract categorical families

CategoryTheory/Monoidal
  └─→ Triangulated                            compatibility class; instances come from geometry

RingTheory/Spectrum/Prime
  └─→ BasicOpen                               finite products of basic opens

Topology
  ├─→ Sheaves                                 Basis, ModuleTensor (StalkTensor)
  └─→ Category/TopCat/Opens                   limits and CoversTop in the category of opens

AlgebraicGeometry
  ├─→ Modules                                 X.Modules: affine, presentation, pullback, pushforward, restriction, tensor
  │     ├─→ Quasicoherent
  │     └─→ Coherent                          Coh X, its abelian instance, descent, pushforward
  ├─→ ProjectiveSpectrum                      Proj, twists, Čech on projective space
  ├─→ Cohomology                              affine and projective Čech, finiteness, Euler characteristic
  ├─→ DerivedCategory
  │     ├─→ Basic, Coherent                   D(X.Modules), D(Coh X), Dᵇ(Coh X), Perf(X)
  │     ├─→ CartierDivisor                   canonical coherent/derived/bounded objects
  │     ├─→ DivisorSequence                   short-exact triangles; arbitrary-line
  │     │                                     Cartier twists; bounded lift
  │     │                                          consumes generic FullSubcategory API
  │     ├─→ Dqc → Comparison                  locus, canonical zero, explicit comparison evidence
  │     ├─→ Families                          base change, pullback and the supplied derived pushforward
  │     ├─→ Tensor                            derived tensor: unbounded K-flat, bounded-coherent,
  │     │                                     monoidal-coherent, relative; the monoidal-triangulated instance
  │     ├─→ TwistedPushforward                Rf_*(K ⊗^L -), from Tensor and Families alone
  │     ├─→ FourierMukai                      geometric kernels and convolution, consuming all of those
  │     └─→ Stability                         base change of pre-stability data; kernel actions on stability
  ├─→ Divisors
  │     ├─→ CartierLineBundle                 associated sheaf as LineBundleData;
  │     │                                     agreement with direct Picard class
  │     └─→ EffectiveLineBundle               exact Cartier sequences tensored by
  │                                           arbitrary line-bundle data
  ├─→ Duality, IntersectionTheory, RiemannRoch, Numerical
  ├─→ Moduli
  │     ├─→ PerfectComplex, Quot
  │     ├─→ Semistability                     loci, scheme probes, locus probes, finite-type openness
  │     └─→ HarderNarasimhan                  relative filtrations, the Dedekind HN problem
  ├─→ Sites                                   direct extensions of Mathlib's big Zariski,
  │                                           étale, fppf and fpqc topologies on schemes
  ├─→ Stacks
  │     ├─→ Representable                     big-Zariski representables
  │     ├─→ Descent                           fppf and étale descent for those representables,
  │     │                                     and covering families from Mathlib covers
  │     └─→ Algebraic                         provisional big-Zariski presentation data:
  │                                           scheme fibers, scheme diagonals, atlases
  └─→ Variety, Surface
```

## Import guide

| Client need | Import |
| --- | --- |
| Generic derived-category extensions | `DerivedAlgGeo.Algebra.Homology.DerivedCategory` |
| Derived/opposite comparison and exact linear duality | `DerivedAlgGeo.Algebra.Homology.DerivedCategory.Opposite`, `…LinearDual` |
| Generic spectral sequences | `DerivedAlgGeo.Algebra.Homology.SpectralSequence` |
| dg categories | `DerivedAlgGeo.Algebra.Homology.DGCategory` |
| dg enhancements of an abstract triangulated category | `DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement` |
| The dg enhancement of the homotopy category | `DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement` |
| Module sheaves on an arbitrary ringed site | `DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf` |
| Generic site-theoretic Čech machinery | `DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech` |
| Generic stacks and representable fibers | `DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids` |
| Étale/fppf/fpqc topology comparisons on schemes | `DerivedAlgGeo.AlgebraicGeometry.Sites.Comparison` |
| Fppf and étale descent for representable stacks | `DerivedAlgGeo.AlgebraicGeometry.Stacks.Descent` |
| Pseudofunctor transport, loci, and subprestacks | `DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat` |
| Neutral moduli boundedness | `DerivedAlgGeo.CategoryTheory.Moduli` |
| Fiber categories and pullbacks | `DerivedAlgGeo.CategoryTheory.Triangulated.Families` |
| Bridgeland stability | `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition` |
| Weak stability only | `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak` |
| Stability functions and HN theory on an abelian category | `DerivedAlgGeo.CategoryTheory.Abelian.Stability` |
| Slope and Gieseker stability of coherent sheaves | `DerivedAlgGeo.AlgebraicGeometry.Stability` |
| Basiswise isomorphism detection for topological sheaves | `DerivedAlgGeo.Topology.Sheaves.Basis` |
| Finite products of prime-spectrum basic opens | `DerivedAlgGeo.RingTheory.Spectrum.Prime.BasicOpen` |
| Coherent sheaves | `DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent` |
| Cartier divisors as line bundles | `DerivedAlgGeo.AlgebraicGeometry.Divisors.CartierLineBundle` |
| Effective-divisor sequences twisted by line bundles | `DerivedAlgGeo.AlgebraicGeometry.Divisors.EffectiveLineBundle` |
| Cartier divisors as coherent derived objects | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.CartierDivisor` |
| Scheme-derived categories and `Dqc`, without stability | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory` |
| Scheme-derived pullback | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families` |
| Derived tensor on schemes, in three tiers | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Tensor` |
| Supplied derived pushforward on `Dᵇ(Coh)` | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.DerivedPushforward` |
| Geometric kernels and convolution | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai` |
| Stability on scheme-derived categories | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability` |
| Semistable loci, probes, finite-type openness, relative HN | `DerivedAlgGeo.AlgebraicGeometry.Moduli` |

Consult `docs/architecture/cutover-ledger.md` for pending cutovers and confirm
the chosen import exists in the current checkout. A proposed target is not
an implemented import or an additional canonical root.

## Retired conventions

- `CategoryTheory/<source>/Instances/AlgebraicGeometry/` leaves, their
  umbrellas, the `GeometryInstances` virtual layer, and the reverse-edge
  allowlist. A geometric realization lives with the geometric object.
- The subject rank order and subject-level cycle check.
- The weakest-vocabulary ranking of subjects. Sufficient hypotheses help
  split foundations from applications; they do not determine subject order.
- `AlgebraicGeometry/StabilityCondition/`, `Compatibility/`, and the
  import-only shims listed in the gate's `RETIRED_PATHS`.
- The `CohLean`, `DGLean`, and `BridgelandStabLean` roots.
