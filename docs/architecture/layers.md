# Subject ownership and dependency direction

This document records the stable source-layer contract. An arrow `A → B`
means that modules owned by subject `A` may import modules owned by subject
`B`. The graph is intentionally acyclic:

```text
Development ─┬→ Compatibility ─┬→ GeometryInstances ─┬→ AlgebraicGeometry
             │                 │                       └→ CategoryTheory
             │                 ├→ AlgebraicGeometry
             │                 └→ CategoryTheory
             ├→ GeometryInstances
             ├→ AlgebraicGeometry
             └→ CategoryTheory

AlgebraicGeometry ─┬→ CategoryTheory
                  ├→ Algebra
                  ├→ LinearAlgebra
                  └→ Topology

CategoryTheory → LinearAlgebra
```

The support subjects `Algebra`, `LinearAlgebra`, and `Topology` are lower
layers. `DerivedAlgGeo.lean` is a public aggregation root, not a subject owner,
so its imports do not add edges to this graph.

`GeometryInstances` is a virtual leaf owner, not a top-level source directory.
It consists exactly of modules below a path segment
`Instances/AlgebraicGeometry/` inside `CategoryTheory`. This makes the generic
construction the visible parent while keeping its geometric realizations out
of generic umbrellas. The layering gate classifies those leaves separately;
all other modules below `CategoryTheory` remain geometry-independent.

## Ownership rule

`CategoryTheory` owns interfaces whose statements are independent of a
geometric realization. `AlgebraicGeometry` owns declarations specialized to
schemes, sheaves, geometric fibers, `Dqc`, derived pullback, finite-type
morphisms, or Fourier--Mukai kernels—even when their proofs are primarily
category theoretic. Proof technique does not determine source ownership.

When a geometric construction realizes a reusable categorical interface, its
registration and comparison theorems may instead be placed in the generic
construction's explicit `Instances/AlgebraicGeometry/` leaf. These modules may
import both owners. Generic category-theory modules and algebraic-geometry
modules may not import them; they are opt-in leaves exported only by an
instance umbrella or the public repository root.

In particular:

- abstract fiber categories, pullback functors, and shared boundedness
  interfaces live in
  `DerivedAlgGeo.CategoryTheory.Triangulated.Families`;
- weak-family probes and weak stability data live in
  `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families`;
- ordinary Bridgeland family packages live in
  `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`;
- scheme-derived categories, `Dqc`, derived pullback, and geometric kernel
  realizations live below `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory`;
- scheme semistable loci, relative HN data, and other constructions that
  actually consume stability data live below
  `DerivedAlgGeo.AlgebraicGeometry.StabilityCondition`;
- `CategoryTheory` must not import either `DerivedAlgGeo.AlgebraicGeometry` or
  `Mathlib.AlgebraicGeometry`;
- `Compatibility` and `Development` are leaf layers and must never become
  dependencies of stable subject modules.

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
CategoryTheory/Triangulated/Families
  └─→ abstract fiber categories, pullback functors, and boundedness

CategoryTheory/Triangulated/WeakStabilityCondition
  ├─→ Foundation, Families, HarderNarasimhan, Support, Tilting
  └─→ StabilityCondition
        ├─→ Foundation/Deformation              Bridgeland deformation
        ├─→ Foundation, Phase, Metric, Symmetry, Support, Walls
        ├─→ Families                         abstract categorical families
        └─→ WeakCompatibility                strong-to-weak adapters

AlgebraicGeometry/DerivedCategory
  ├─→ Basic                                 module-sheaf derived categories
  ├─→ Dqc                                   quasicoherent-cohomology locus
  ├─→ Families                              scheme base change and pullback
  └─→ FourierMukai                          geometric kernels and convolution

AlgebraicGeometry/StabilityCondition
  ├─→ Families                              semistable loci and relative HN
  ├─→ FourierMukai                          stability-specific kernel actions
  └─→ future slope-to-Bridgeland instances  only under valid hypotheses
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
`AlgebraicGeometry.DerivedCategory.FourierMukai`. Stability-family geometry and
stability-specific Fourier--Mukai actions have completed their cutovers to
`AlgebraicGeometry.StabilityCondition.Families` and
`AlgebraicGeometry.StabilityCondition.FourierMukai`. No geometry-owned
declaration remains in the retired flattened categorical family namespace.
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
The categorical Fourier--Mukai bridge acting on Bridgeland stability
conditions has completed its cutover from the former sibling namespace to
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry`.
The associated slicing, pre-stability, and stability group actions have
completed their cutover to
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`.
Only `Compatibility/StabilityConditionGroupActionReview.lean` retains
deprecated aliases in the former sibling namespace so the immutable reviewed
statement payloads continue to elaborate; that bridge is not a second public
API and is removed after reviewer reconfirmation.
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
child, rejects restoration of the former sibling `StabilityCondition` path,
and verifies that neutral derived geometry does not return to the stability
subtree.

## AlgebraicGeometry sublayers

The top-level graph alone cannot distinguish a reusable moduli root from a
Bridgeland-family adapter because both collapse to `AlgebraicGeometry`. The
finer direction is:

```text
StabilityCondition/Families ─┬→ DerivedCategory/Families
                             └→ categorical stability families

StabilityCondition/FourierMukai → DerivedCategory/FourierMukai

Moduli / Stacks ─┬→ AlgebraicGeometry/DerivedCategory
                 └→ CategoryTheory/Sites
```

`CategoryTheory/Sites/StackInGroupoids.lean` is the canonical module for the
generic groupoid-valued stack extension. Its declarations use the matching
`CategoryTheory` namespace. The former `AlgebraicGeometry/Stacks/Basic.lean`
reexport has been retired; clients import the canonical module directly.
Scheme-specific representability and presentation data remain below
`AlgebraicGeometry/Stacks`.

Scheme-derived `Dqc`, derived pullback, and their preservation theorems now
live under `DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/`, including the
active surfaces for issues #721 and #554. Relative-perfect adapters that
intrinsically define a moduli problem live under `Moduli/PerfectComplex`, not
under `Dqc`.

The layering gate rejects imports from `Moduli` or `Stacks` into
`StabilityCondition/Families`. The former six-edge migration allowlist in
`scripts/layering_reverse_edges.txt` is now empty and must remain empty.

## Migration compatibility

The former CategoryTheory families umbrella mixed generic interfaces with
geometric realizations. It now exports only the generic interfaces. Neutral
declarations such as `TriangulatedFiberFamily`, `BoundednessProblem`, and
`UniversalBoundedness` live in `CategoryTheory.Triangulated.Families`.
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
`AlgebraicGeometry.DerivedCategory.FourierMukai`. Stability-family geometry and
stability-specific kernel actions now use
`AlgebraicGeometry.StabilityCondition.Families` and
`AlgebraicGeometry.StabilityCondition.FourierMukai`, respectively:

| Client need | Import |
| --- | --- |
| Fiber categories and pullbacks | `DerivedAlgGeo.CategoryTheory.Triangulated.Families` |
| Weak-stability family interfaces | `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families` |
| Ordinary Bridgeland family interfaces | `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families` |
| Scheme-derived categories and `Dqc` | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory` |
| Scheme-derived pullback | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families` |
| Geometric kernels and convolution | `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai` |
| Scheme semistability and relative HN | `DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families` |
| Stability-specific kernel actions | `DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.FourierMukai` |

The former combined
`DerivedAlgGeo.Compatibility.StabilityConditionFamilies` import has been
retired now that all repository consumers use their narrow owner imports. The
public `Compatibility` umbrella retains only the deprecated GroupAction aliases
needed to elaborate immutable human-review payloads; it is not a general
migration surface.
