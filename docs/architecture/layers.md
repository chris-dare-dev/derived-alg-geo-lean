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

- abstract fiber categories and pullback functors live in
  `DerivedAlgGeo.CategoryTheory.Triangulated.Families`;
- weak-family probes and weak stability data live in
  `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families`;
- ordinary Bridgeland family packages live in
  `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`;
- scheme, Dqc, pullback, finite-type, and kernel realizations live in
  `DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families`;
- `CategoryTheory` must not import either `DerivedAlgGeo.AlgebraicGeometry` or
  `Mathlib.AlgebraicGeometry`;
- `Compatibility` and `Development` are leaf layers and must never become
  dependencies of stable subject modules.

## Generic constructions and refinements

The source tree follows general constructions before concrete instances:

- derived categories are constructed once from an abelian category;
  `DerivedCategory (Coh X)` is an instance, not a geometric reimplementation;
- abstract pullback, pseudofunctor, and Fourier--Mukai interfaces are
  categorical, while scheme and sheaf realizations are explicit geometric
  instance leaves;
- weak stability is the dependency parent of ordinary Bridgeland stability,
  and the Lean structures must expose the corresponding projection or
  constructor.

The physical module tree records that refinement directly:

```text
CategoryTheory/Triangulated/Families
  └─→ abstract fiber categories and pullback functors

CategoryTheory/Triangulated/WeakStabilityCondition
  ├─→ Foundation, Families, HarderNarasimhan, Support, Tilting
  └─→ StabilityCondition
        ├─→ Foundation, Phase, Metric, Symmetry, Support, Walls
        ├─→ Families                         abstract categorical families
        └─→ WeakCompatibility                strong-to-weak adapters

AlgebraicGeometry/StabilityCondition
  ├─→ Families                              scheme and Dqc realizations
  └─→ future slope-to-Bridgeland instances  only under valid hypotheses
```

The weak umbrella is independently importable and the layering gate rejects
imports from that parent into the `StabilityCondition` child. Declaration
names remain in their established namespaces during this path cutover; module
ownership and declaration namespace are separate compatibility concerns.

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
and verifies that relocated geometric family modules do not return to their
former owner.

## AlgebraicGeometry sublayers

The top-level graph alone cannot distinguish a reusable moduli root from a
Bridgeland-family adapter because both collapse to `AlgebraicGeometry`. The
finer direction is:

```text
StabilityCondition/Families
  └→ Moduli / Stacks
       ├→ AlgebraicGeometry/DerivedCategory   planned neutral scheme seam
       └→ CategoryTheory/Sites               generic descent and stacks
```

`CategoryTheory/Sites/StackInGroupoids.lean` is the canonical module for the
generic groupoid-valued stack extension. Its declaration namespace remains
`AlgebraicGeometry` for source compatibility, and
`AlgebraicGeometry/Stacks/Basic.lean` reexports the new owner for clients of
the former import path. Scheme-specific representability and presentation
data remain below `AlgebraicGeometry/Stacks`.

Scheme-derived `Dqc`, derived pullback, and their preservation theorems
currently live below `StabilityCondition/Families` while issues #721 and #554
are active. Their intended neutral owner is
`DerivedAlgGeo/AlgebraicGeometry/DerivedCategory/`; this issue records that
direction without moving those active surfaces.

The layering gate rejects new imports from `Moduli` or `Stacks` into
`StabilityCondition/Families`. Six measured legacy imports are recorded as
exact source/module pairs in `scripts/layering_reverse_edges.txt`. The
allowlist is a burn-down list: removing an underlying import requires removing
its entry, and adding a new exception is not an accepted migration path.

## Migration compatibility

The former CategoryTheory families umbrella mixed generic interfaces with
geometric realizations. It now exports only the generic interfaces. Existing
declaration names remain in the
`CategoryTheory.Triangulated.StabilityCondition.Families` namespace, so clients
only need to migrate imports:

| Client need | Import |
| --- | --- |
| Fiber categories and pullbacks | `DerivedAlgGeo.CategoryTheory.Triangulated.Families` |
| Weak-stability family interfaces | `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families` |
| Ordinary Bridgeland family interfaces | `DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families` |
| Scheme-specific realizations | `DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families` |
| Former combined surface during migration | `DerivedAlgGeo.Compatibility.StabilityConditionFamilies` |

New library code should use the narrow owner import. The Compatibility import
is public but intentionally a leaf; it provides staged migration without
reintroducing a CategoryTheory-to-geometry edge.
