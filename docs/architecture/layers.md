# Dependency direction

This document records the dependency contract between the subjects of
`DerivedAlgGeo/`. It is short because the contract is short: the tree mirrors
Mathlib's, and Mathlib's subjects are not layered.

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

These are the edges the layout promises and nothing else checks. Each is a
rule in `scripts/check_layering.py`, and each has a known-answer fixture under
`scripts/fixtures/layering/`.

1. **Geometry firewall.** Only modules below `AlgebraicGeometry/` and
   `Development/` import `DerivedAlgGeo.AlgebraicGeometry` or
   `Mathlib.AlgebraicGeometry`, and only they declare into the
   `AlgebraicGeometry` namespace. Everything else in the library is usable
   without schemes. The two aggregation roots `DerivedAlgGeo.lean` and
   `DerivedAlgGeoSweep.lean` import everything and own nothing.
2. **`Development/` is a leaf.** No stable module imports it.
3. **Stability-neutral geometry.** A module below `AlgebraicGeometry/` that is
   not below `Moduli/`, `Numerical/`, or `DerivedCategory/Stability/` never
   reaches the stability tree, even transitively. This keeps `Dᵇ(Coh X)`,
   `Dqc`, coherent sheaves, and cohomology importable without Bridgeland
   stability.
4. **Weak stability is independent of Bridgeland stability.** No module of the
   weak theory imports the Bridgeland theory, and
   `PreStabilityCondition` structurally `extends toWeak :
   WeakPreStabilityCondition` rather than copying its fields.
5. **Retired paths stay retired.** The gate carries the list of paths removed
   by past cutovers so that a shim cannot drift back.
6. **A new top-level subject is deliberate.** A directory directly below the
   source root must be one of the Mathlib subjects the repository uses, named
   in the gate's `KNOWN_SUBJECTS`.

## AlgebraicGeometry sublayers

Geometry is organized by object, and a few of its subtrees exist to consume
stability conditions. The finer direction below `AlgebraicGeometry/` is:

```text
Modules, ProjectiveSpectrum, Cohomology, Divisors, Duality,
IntersectionTheory, RiemannRoch, Stacks, Surface, Variety, Spec, Morphisms
        stability-neutral: never reach the stability tree

DerivedCategory
  ├─ Basic, Coherent, Dqc, Families, FourierMukai     stability-neutral
  └─ Stability                                         imports the stability tree;
                                                        omitted by the DerivedCategory
                                                        umbrella, imported by the
                                                        AlgebraicGeometry umbrella
Moduli, Numerical                                       may import the stability tree
```

A geometric realization of a categorical interface sits with the geometric
object it is about: the `IsCompatibleWithTriangulation` instance for
`Dᵇ(Coh X)` in `DerivedCategory/FourierMukai/DerivedTensorCoherence.lean`,
the scheme probes and semistable-locus probes in `Moduli/Semistability/`, the
relative Harder--Narasimhan problem in `Moduli/HarderNarasimhan/`, and the
base-change and Fourier--Mukai actions on stability data in
`DerivedCategory/Stability/`. A declaration in such a file may keep the
namespace of the categorical structure it extends so that dot notation
resolves; the file's path records what it is about.

## Where each theory lives

Arrows point from a refinement or consumer to the root it builds on.

```text
Algebra/Homology
  ├─→ DerivedCategory                         extends Mathlib's DerivedCategory
  │     ├─→ TStructure, ExactFunctor, Homology, CohomologyObjectProperty
  │     ├─→ Opposite → LinearDual
  │     ├─→ Ext (adjunction, dimension shift, resolution naturality)
  │     └─→ KProjective, BoundedAboveProjective
  ├─→ HomotopyCategory                        extends Mathlib's HomotopyCategory
  │     ├─→ Bounded
  │     └─→ DGEnhancement                     C^dg enhances K(A); agreement with
  │                                           Mathlib's shift and triangles
  ├─→ DGCategory                              bespoke class on HomComplex (ADR-0010/0011)
  │     ├─→ Functor, Opposite, Product, Linear, Shift, H0, LinearH0
  │     ├─→ Pretriangulated                   cones, shifts, rotation inside the dg category
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

CategoryTheory/Triangulated
  ├─→ PretriangulatedAxioms, TStructure, PostnikovTower, ExtensionClosure, QuasiAbelian
  ├─→ GrothendieckGroup                        K₀, realizations, Euler forms
  ├─→ CompactlyGenerated, SemiorthogonalDecomposition, SphericalTwist
  ├─→ FourierMukai                            generic kernel autoequivalences
  ├─→ Families                                pseudofunctorial fiber categories
  ├─→ DGEnhancement                           enhancement interface, H⁰ triangulation
  └─→ StabilityCondition                      Bridgeland stability (canonical concept)
        ├─→ Weak                              weak stability: the dependency parent
        │     └─→ Foundation, Families, HarderNarasimhan, Support, Tilting
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
  │     ├─→ Dqc → Comparison                  locus, canonical zero, explicit comparison evidence
  │     ├─→ Families                          base change and pullback consumers
  │     ├─→ FourierMukai                      geometric kernels and convolution; the monoidal-triangulated instance
  │     └─→ Stability                         base change of pre-stability data; kernel actions on stability
  ├─→ Divisors, Duality, IntersectionTheory, RiemannRoch, Numerical
  ├─→ Moduli
  │     ├─→ PerfectComplex, Quot
  │     ├─→ Semistability                     loci, scheme probes, locus probes, finite-type openness
  │     └─→ HarderNarasimhan                  relative filtrations, the Dedekind HN problem
  ├─→ Stacks                                  big-Zariski representables
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
| Pseudofunctor transport, loci, and subprestacks | `DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat` |
| Neutral moduli boundedness | `DerivedAlgGeo.CategoryTheory.Moduli` |
| Fiber categories and pullbacks | `DerivedAlgGeo.CategoryTheory.Triangulated.Families` |
| Bridgeland stability | `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition` |
| Weak stability only | `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak` |
| Basiswise isomorphism detection for topological sheaves | `DerivedAlgGeo.Topology.Sheaves.Basis` |
| Finite products of prime-spectrum basic opens | `DerivedAlgGeo.RingTheory.Spectrum.Prime.BasicOpen` |
| Coherent sheaves | `DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent` |
| Scheme-derived categories and `Dqc`, without stability | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory` |
| Scheme-derived pullback | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families` |
| Geometric kernels and convolution | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai` |
| Stability on scheme-derived categories | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability` |
| Semistable loci, probes, finite-type openness, relative HN | `DerivedAlgGeo.AlgebraicGeometry.Moduli` |

Lanes still moving toward these paths are listed in
`docs/architecture/cutover-ledger.md`; the import guide names the target.

## Retired conventions

- `CategoryTheory/<source>/Instances/AlgebraicGeometry/` leaves, their
  umbrellas, the `GeometryInstances` virtual layer, and the reverse-edge
  allowlist. A geometric realization lives with the geometric object.
- The subject rank order and subject-level cycle check.
- The weakest-vocabulary signature test as the primary placement rule; it is
  now the Tier 2 tie-breaker in `placement.md`.
- `AlgebraicGeometry/StabilityCondition/`, `Compatibility/`, and the
  import-only shims listed in the gate's `RETIRED_PATHS`.
- The `CohLean`, `DGLean`, and `BridgelandStabLean` roots.
