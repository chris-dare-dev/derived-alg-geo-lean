# Subject ownership and dependency direction

This document records the stable source-layer contract. An arrow `A → B`
means that modules owned by subject `A` may import modules owned by subject
`B`. The graph is intentionally acyclic:

```text
Development ─┬→ GeometryInstances ─┬→ AlgebraicGeometry
             │                     └→ CategoryTheory
             ├→ AlgebraicGeometry
             ├→ Topology
             └→ CategoryTheory

AlgebraicGeometry ─┬→ CategoryTheory
                  ├→ Algebra
                  ├→ LinearAlgebra
                  └→ Topology

Topology → CategoryTheory

CategoryTheory → LinearAlgebra
```

The support subjects `Algebra` and `LinearAlgebra` are the lowest layers.
`Topology` may consume generic categorical sheaf theory while remaining below
scheme geometry. `DerivedAlgGeo.lean` is a public aggregation root, not a
subject owner, so its imports do not add edges to this graph.

`GeometryInstances` is a virtual leaf owner, not a top-level source directory.
It consists exactly of modules below a path segment
`Instances/AlgebraicGeometry/` inside `CategoryTheory`. This makes the generic
construction the visible parent while keeping its geometric realizations out
of generic umbrellas. The layering gate classifies those leaves separately;
all other modules below `CategoryTheory` remain geometry-independent.

## Ownership rule

`CategoryTheory` owns interfaces whose statements are independent of a
geometric realization, including sheaves on arbitrary sites.
`AlgebraicGeometry` owns declarations specialized to schemes, scheme-indexed
sheaf categories, geometric fibers, `Dqc`, derived pullback, finite-type
morphisms, or Fourier--Mukai kernels—even when their proofs are primarily
category theoretic. Proof technique does not determine source ownership.

When a geometric construction realizes a reusable categorical interface, its
registration and comparison theorems may instead be placed in the generic
construction's explicit `Instances/AlgebraicGeometry/` leaf. These modules may
import both owners. Generic category-theory modules and algebraic-geometry
modules may not import them; they are opt-in leaves exported only by an
instance umbrella or the public repository root.

In particular:

- bicategorical adjunctions, adjoint equivalences, and mates extend Mathlib
  below `DerivedAlgGeo.CategoryTheory.Bicategory`; ordinary adjoint functors
  are their specialization in `Cat`;
- generic preservation and reflective transport results live below
  `DerivedAlgGeo.CategoryTheory.Limits`, even when an ordinary adjunction is
  one of their hypotheses;
- ordinary module and ring theory lives under `DerivedAlgGeo.Algebra`, while
  generic sheaves and sheaves of modules on arbitrary ringed sites live below
  `DerivedAlgGeo.CategoryTheory.Sites.Sheaves`;
- repository-owned theorems about arbitrary abelian categories live below
  `DerivedAlgGeo.CategoryTheory.Abelian` and extend Mathlib's existing
  `CategoryTheory.Abelian` typeclass;
- abstract fiber categories and pullback functors live in
  `DerivedAlgGeo.CategoryTheory.Triangulated.Families`, while shared moduli
  boundedness lives in `DerivedAlgGeo.CategoryTheory.Moduli`;
- generic derived-category t-structure, exact-functor, homology-comparison,
  and K-projective APIs live below
  `DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory`;
- generic `Ext`, filtered-complex spectral-sequence, and site-theoretic Čech
  machinery live below their categorical derived, spectral-sequence, and site
  roots; Čech injective comparisons and compact-basis boundedness remain
  generic until an affine or projective object enters the statement;
- weak-family probes and weak stability data live in
  `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families`;
- ordinary Bridgeland family packages live in
  `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`;
- scheme-derived categories, `Dqc`, derived pullback, and geometric kernel
  realizations live below `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory`;
- actual semistable loci and relative HN filtrations live below
  `DerivedAlgGeo.AlgebraicGeometry.Moduli`, while declarations realizing weak-
  or Bridgeland-family interfaces live in those categorical sources' explicit
  `Instances.AlgebraicGeometry` leaves;
- `CategoryTheory` must not import either `DerivedAlgGeo.AlgebraicGeometry` or
  `Mathlib.AlgebraicGeometry`;
- `Development` is a leaf layer and must never become a dependency of stable
  subject modules. The former public `Compatibility` layer has been retired.

## Generic constructions and refinements

The source tree follows general constructions before concrete instances:

- derived categories are constructed once from an abelian category;
  `DerivedCategory (Coh X)` is an instance, not a geometric reimplementation;
- abstract pullback, pseudofunctor, and Fourier--Mukai interfaces are
  categorical, while scheme-derived categories and kernels remain geometric;
  registration-only adapters may use explicit geometric instance leaves;
- weak stability is the dependency parent of ordinary Bridgeland stability,
  and the Lean structures must expose the corresponding projection or
  constructor.

The physical module tree records that refinement directly:

```text
Algebra/Module/Localization
  └─→ Kernels                                linear, ModuleCat, natural forms

Algebra/MvPolynomial
  ├─→ Grading                                standard grading and variable generation
  ├─→ DivMonomial                            homogeneous and exact-division identities
  ├─→ LaurentBasis → LaurentProjection
          ├─→ LaurentBlock → LaurentHomotopy
          └─→ LaurentBlock → LaurentFinite   one-localization algebra
  └─→ Cech
        └─→ Basic                            denominators, terms, faces, canonical p/1
              └─→ Homotopy
                    ├─→ Primitive            algebraic cocycle contraction
                    └─→ Finite               finite full-block cochains

LinearAlgebra
  └─→ GradedBasis                            weighted spans and internal sums

CategoryTheory/Bicategory
  └─→ Adjunction
        ├─→ Basic                               adjunctions of 1-morphisms
        └─→ Cat                                 ordinary functor specialization

CategoryTheory/Pseudofunctor
  ├─→ Transport                                 Cat-presentation coherence transport
  └─→ ObjectProperty
        └─→ UniversallyStable                   replete subprestack closure

CategoryTheory/Limits/Preserves
  ├─→ Composition                              no adjunction required
  └─→ Reflective                               ordinary Cat-level consumer

CategoryTheory/Triangulated/Families
  ├─→ pseudofunctorial fiber categories and pullback coherence
  └─→ strict category-valued functors through `ofFunctor`

CategoryTheory/Triangulated/DerivedCategory
  ├─→ TStructure, ExactFunctor, Homology       arbitrary abelian categories
  ├─→ Opposite                                generic derived/opposite comparison
  ├─→ LinearDual                              exact ModuleCat consumer of Opposite
  ├─→ Ext                                     adjunction and resolution naturality
  ├─→ KProjective                             generic supported derivation
  └─→ BoundedAboveProjective                  functorial projective locus

CategoryTheory/SpectralSequence
  └─→ filtered and total complexes             arbitrary abelian categories

CategoryTheory/Sites/StackInGroupoids
  ├─→ Discrete                                sheaves of types as stacks
  └─→ Morphism                                fibers and representability

CategoryTheory/Moduli
  └─→ Boundedness                              neutral moduli predicate

CategoryTheory/Sites/Cech
  ├─→ Differential, Contractible               arbitrary presheaves on a site
  ├─→ Bicomplex, Comparison                    arbitrary sheaves on a site
  ├─→ GlobalComparison, ComplexNaturality      Čech-to-derived comparison
  └─→ BasisComparison, Boundedness             topological-space sheaves

CategoryTheory/Abelian
  └─→ WeakSerre                                arbitrary abelian categories

CategoryTheory/Sites/Sheaves
  ├─→ ConstantPullback, CohomologyPushforward  arbitrary sites
  └─→ Modules
        ├─→ Exactness                           arbitrary ringed sites
        └─→ Presentation                        finite-presentation transport

CategoryTheory/Triangulated/WeakStabilityCondition
  ├─→ Foundation, Families, HarderNarasimhan, Support, Tilting
  └─→ StabilityCondition
        ├─→ Foundation/Deformation              Bridgeland deformation
        ├─→ Foundation, Phase, Metric, Symmetry, Support, Walls
        ├─→ Families                         abstract categorical families
        │     └─→ Instances/AlgebraicGeometry scheme-family realizations
        ├─→ Symmetry/Autoequivalence
        │     └─→ Instances/AlgebraicGeometry geometric kernel actions
        └─→ structural projection to weak prestability

CategoryTheory/Triangulated/FourierMukai
  └─→ Autoequivalence                       generic kernel autoequivalences

AlgebraicGeometry/DerivedCategory
  ├─→ Basic                                 module-sheaf derived categories
  ├─→ Coherent                              D(Coh X), Dᵇ(Coh X), and Perf(X)
  ├─→ Dqc                                   locus, canonical zero, perfect image
  │    └─→ Comparison                       explicit-evidence consumer API
  ├─→ Families                              base-change and pullback consumers
  └─→ FourierMukai                          geometric kernels and convolution

AlgebraicGeometry/Numerical/Core
  └─→ GradedBasis                            NumericalRingData consumer

AlgebraicGeometry/Proj/Modules/ProjectiveSpace
  └─→ consumes Grading, DivMonomial, and Cech/Basic for basic opens and sections

AlgebraicGeometry/Cohomology
  └─→ projective Čech vanishing/finiteness consume the algebraic primitive/block

AlgebraicGeometry/Moduli/PerfectComplex
  ├─→ Relative                             base-dependent perfect locus
  ├─→ Comparison                           two-term → absolute → Dqc adapters
  ├─→ Boundedness                          fiberwise replete selectors/witnesses
  └─→ AffineFamilyRelativePerfectPseudofunctor
        └─→ generic ObjectProperty.fullsubcategory

AlgebraicGeometry/SheafOfModules
  └─→ QuasicoherentSheaf
        └─→ CoherentSheaf                   supplies `Abelian (Coh X)`

AlgebraicGeometry/Stacks
  ├─→ Representable                          big-Zariski scheme instances
  └─→ Algebraic                              geometric representability data

AlgebraicGeometry/Moduli
  ├─→ Semistability                         actual semistable loci
  └─→ HarderNarasimhan                      actual relative HN filtrations
```

The weak umbrella is independently importable and the layering gate rejects
imports from that parent into the `StabilityCondition` child. The path cutover
initially preserved declaration names, but the neutral categorical, weak, and
Bridgeland family APIs have now completed separate namespace cutovers to
`CategoryTheory.Triangulated.Families` and
`CategoryTheory.Triangulated.WeakStabilityCondition.Families`, and
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`,
respectively. The scheme-derived category and family foundations have likewise
completed their cutover to `AlgebraicGeometry.DerivedCategory` and
`AlgebraicGeometry.DerivedCategory.Families`. The `Dqc` subtree has completed
its cutover to `AlgebraicGeometry.DerivedCategory.Dqc`. Neutral geometric
Fourier--Mukai declarations have completed their cutover to
`AlgebraicGeometry.DerivedCategory.FourierMukai`, and generic kernel
autoequivalences now live in `CategoryTheory.Triangulated.FourierMukai`.
Scheme-family and stability-action realizations are attached to their exact
categorical sources through `Instances.AlgebraicGeometry` leaves. Actual
semistable loci and relative HN filtrations live in
`AlgebraicGeometry.Moduli.Semistability` and
`AlgebraicGeometry.Moduli.HarderNarasimhan`. The former
`AlgebraicGeometry.StabilityCondition` source and namespace are absent, and no
geometry-owned declaration remains in the retired flattened categorical family
namespace.
Bridgeland wall declarations have also completed their cutover from the former
sibling namespace to
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall`.
Generic numerical support predicates and their weak-stability bindings have
completed their cutover from the former strong-sibling namespace to
`CategoryTheory.Triangulated.WeakStabilityCondition.Support`.
The finite-length simple-charge lattice model has moved from the duplicate
plural `WeakStabilityCondition/Foundations/` tree into the canonical
`WeakStabilityCondition/Foundation/StabilityFunction/` subtree, and now uses
`CategoryTheory.Triangulated.WeakStabilityCondition.FiniteLength`.
Generic kernel autoequivalences and the strong-child extension that acts on
Bridgeland stability conditions now share the canonical
`CategoryTheory.Triangulated.FourierMukai` namespace. The strong-dependent
implementation remains physically below the stability child's `Symmetry/`
subtree without creating a second API owner.
The associated slicing, pre-stability, and stability group actions have
completed their cutover to
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`.
No public module retains aliases in the former sibling namespace. The
executable-only `exe/RestateHistoricalNames.lean` module supplies the exact
historical names while immutable reviewed statements are re-elaborated; it is
unreachable from the public and sweep umbrellas and therefore is not a second
library API.
Bridgeland deformation helpers have completed their cutover from the flattened
`CategoryTheory.Triangulated.Deformation` namespace to
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation`.
Extensions of canonical structures remain in the established `Slicing`,
`PreStabilityCondition.WithClassMap`, or `StabilityCondition.WithClassMap`
namespace: directory placement groups the implementation, but does not create
a second owner for those APIs.

Monoidal structure supplies the base for enrichment, but monoidality and
triangulation are independent axes. The intended categorical refinement map
is:

```text
CategoryTheory/Monoidal
  ├─→ CategoryTheory/Enriched
  │     └─→ DGCategory
  │           └─→ Monoidal        (optional refinement)
  └─→ Monoidal/Triangulated            (compatibility interface)
                 └─→ geometric exact tensors via instance leaves

CategoryTheory/Triangulated
  └─→ DGEnhancement
        └─→ Monoidal                    (compatibility on H⁰)
```

The arrows here mean dependency or refinement, not that every object in the
parent has every structure shown below it. In particular, a tensor bifunctor
need not carry associators or unitors, a dg category need not be monoidal, and
a triangulated category need not be monoidal. Concrete tensor products on
sheaves, invertible sheaves, and `Dᵇ(Coh X)` remain geometry-owned and expose
instances of the generic compatibility interfaces.

The word “module” does not by itself determine ownership. Ring/module theory
with no site belongs to `Algebra`; module sheaves on an arbitrary ringed site
belong to `CategoryTheory/Sites/Sheaves/Modules`; only scheme-indexed module,
quasicoherent, and coherent sheaves belong to algebraic geometry. Likewise,
the repository reuses Mathlib's abelian typeclass: the generic derived category
depends on an arbitrary abelian category, while geometry proves that `Coh(X)`
is one and then supplies registration or comparison consumers.

Raw dg categories require an additional distinction. A dg category is an
enriched category and need not be triangulated, so its basic theory and its
internal pretriangulated refinement live in
`CategoryTheory.Enriched.DGCategory`. The triangulated structure on `H⁰` and
the interface for a dg enhancement of an ordinary triangulated category live
in `CategoryTheory.Triangulated.DGEnhancement`. Thus a dg-*enhanced*
triangulated category is a child of the triangulated theory without falsely
making every dg category triangulated.

The source-layer gate in `scripts/check_layering.py` reconstructs the collapsed
graph from every tracked library import, rejects cycles and forbidden reverse
edges, verifies that the weak-stability parent does not import its Bridgeland
child, rejects restoration of either retired `StabilityCondition` path, and
verifies that algebraic geometry does not import a categorical
`Instances/AlgebraicGeometry` leaf.

## AlgebraicGeometry sublayers

The top-level graph alone cannot distinguish a categorical source from its
algebraic-geometric implementation. The finer direction is:

```text
CategoryTheory/<source>/Instances/AlgebraicGeometry
  ├─→ CategoryTheory/<source>
  └─→ AlgebraicGeometry/<geometric owner>

AlgebraicGeometry/<geometric owner> → CategoryTheory/<source>
AlgebraicGeometry/<geometric owner> ↛ Instances/AlgebraicGeometry
```

`CategoryTheory/Sites/StackInGroupoids.lean` is the canonical module for the
generic groupoid-valued stack extension. Its `Discrete/` and `Morphism/`
children own sheaf-to-stack construction and site-object representability;
all use the matching `CategoryTheory` namespace. The former `AlgebraicGeometry/Stacks/Basic.lean`
reexport has been retired; clients import the canonical module directly.
Scheme-specific representability and presentation data remain below
`AlgebraicGeometry/Stacks`.

Scheme-derived `Dqc`, derived pullback, and their preservation theorems now
live under `DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/`, including the
active surfaces for issues #721 and #554. Relative-perfect adapters that
intrinsically define a moduli problem live under `Moduli/PerfectComplex`, not
under `Dqc`. Generic derived t-structure, exact-functor, homology-comparison,
K-projective, and bounded-above-projective results live instead under
`DerivedAlgGeo/CategoryTheory/Triangulated/DerivedCategory/`; the affine
subtree contains only ring/module specializations of those interfaces.
The same generic root owns the explicit comparison between opposites and
derived categories and the exact derived lift of algebraic linear duality.
Canonical and Serre duality import that root together with
`AlgebraicGeometry/DerivedCategory/Coherent.lean`; they do not construct
parallel localizations of `Coh(X)` or `ModuleCat`.
The bounded-coherent and compact/perfect identifications remain explicit
propositions in `Dqc.lean`; `Dqc/Comparison.lean` consumes supplied evidence
to construct representatives and membership equivalences without installing
global instances. Relative-perfect geometry imports that conditional API and
states the additional bounded-cohomology hypothesis at its actual use site.
`Dqc.lean` also owns the canonical zero object of the full subcategory for an
arbitrary scheme. The relative-perfect consumer proves pseudo-coherence,
finite Tor amplitude, and universal gluability for that object; it does not
rebuild zero objects in the coherent or ambient derived categories.

Perfect-complex terminology is linked by proved one-way adapters rather than
directory nesting. `schemePerfect` is absolute coherent-derived data,
`schemeRelativePerfect` depends on a base morphism, and
`TwoTermPerfectDeterminantData` is presentation data of fixed amplitude. The
comparison leaf proves two-term presentation data gives an absolute perfect
object and then uses the canonical Dqc essential-image map. No reverse or
absolute/relative equivalence is registered.

The layering gate rejects imports from algebraic geometry back into any
`Instances/AlgebraicGeometry` leaf and rejects restoration of the retired
`AlgebraicGeometry/StabilityCondition` subtree. The former migration allowlist
in `scripts/layering_reverse_edges.txt` is empty and must remain empty.

## Migration compatibility

The former CategoryTheory families umbrella mixed generic interfaces with
geometric realizations. It now exports only triangulated-family interfaces.
`TriangulatedFiberFamily` lives in `CategoryTheory.Triangulated.Families` and
is based on a Cat-valued pseudofunctor over `LocallyDiscrete Bᵒᵖ`; strict
functors are admitted through `TriangulatedFiberFamily.ofFunctor` rather than
serving as the root;
the more general `BoundednessProblem` and `UniversalBoundedness` live in
`CategoryTheory.Moduli` and are consumed by both stability and geometry.
Weak-family probes and structures live in
`CategoryTheory.Triangulated.WeakStabilityCondition.Families`. Ordinary
Bridgeland family packages live in
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`.
Clients of all three groups must migrate imports and qualified names.
Scheme-derived category, pullback, and `Dqc` declarations now use
`AlgebraicGeometry.DerivedCategory` and
`AlgebraicGeometry.DerivedCategory.Families`, and
`AlgebraicGeometry.DerivedCategory.Dqc`, respectively. Neutral geometric
Fourier--Mukai declarations now use
`AlgebraicGeometry.DerivedCategory.FourierMukai`. Stability realizations use
the explicit instance umbrellas attached to their categorical sources:

| Client need | Import |
| --- | --- |
| Fiber categories and pullbacks | `DerivedAlgGeo.CategoryTheory.Triangulated.Families` |
| Pseudofunctor-presentation transport through equivalences | `DerivedAlgGeo.CategoryTheory.Pseudofunctor.Transport` |
| Neutral moduli boundedness | `DerivedAlgGeo.CategoryTheory.Moduli` |
| Pseudofunctor loci and subprestacks | `DerivedAlgGeo.CategoryTheory.Pseudofunctor.ObjectProperty` |
| Generic derived-category extensions | `DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory` |
| Derived/opposite comparison and exact linear duality | `DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.Opposite` and `DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.LinearDual` |
| Generic spectral sequences | `DerivedAlgGeo.CategoryTheory.SpectralSequence` |
| Generic site-theoretic Čech machinery | `DerivedAlgGeo.CategoryTheory.Sites.Cech` |
| Polynomial-variable Čech algebra | `DerivedAlgGeo.Algebra.MvPolynomial.Cech` |
| Projective basic-open and section comparison | `DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ProjectiveSpace` |
| Generic abelian-category extensions | `DerivedAlgGeo.CategoryTheory.Abelian` |
| Generic sheaves and ringed-site module sheaves | `DerivedAlgGeo.CategoryTheory.Sites.Sheaves` |
| Generic stacks and representable fibers | `DerivedAlgGeo.CategoryTheory.Sites` |
| Weak-stability family interfaces | `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families` |
| Ordinary Bridgeland family interfaces | `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families` |
| Scheme-derived categories and `Dqc` | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory` |
| Scheme-derived pullback | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families` |
| Geometric kernels and convolution | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai` |
| Actual semistable loci and relative HN | `DerivedAlgGeo.AlgebraicGeometry.Moduli` |
| Weak scheme-family realization | `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families.Instances` |
| Bridgeland scheme-family realizations | `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.Instances` |
| Geometric stability actions of kernels | `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Instances` |

The former combined
`DerivedAlgGeo.Compatibility.StabilityConditionFamilies` import has been
retired now that all repository consumers use their narrow owner imports. The
`DerivedAlgGeo.Compatibility` umbrella and final GroupAction compatibility leaf
are also retired. Immutable historical review text is supported only inside the
restatement executable, while review-to-declaration joins follow canonical
renames by statement digest.
