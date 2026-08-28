# Subject ownership and dependency direction

This document records the stable source-layer contract. An arrow `A → B`
means that modules owned by subject `A` may import modules owned by subject
`B`. The graph is intentionally acyclic:

```text
Development ─┬→ Compatibility ─┬→ AlgebraicGeometry ─┬→ CategoryTheory
             │                 │                     ├→ Algebra
             │                 │                     ├→ LinearAlgebra
             │                 │                     └→ Topology
             │                 └→ CategoryTheory
             ├→ AlgebraicGeometry
             └→ CategoryTheory

CategoryTheory → LinearAlgebra
```

The support subjects `Algebra`, `LinearAlgebra`, and `Topology` are lower
layers. `DerivedAlgGeo.lean` is a public aggregation root, not a subject owner,
so its imports do not add edges to this graph.

## Ownership rule

`CategoryTheory` owns interfaces whose statements are independent of a
geometric realization. `AlgebraicGeometry` owns declarations specialized to
schemes, sheaves, geometric fibers, `Dqc`, derived pullback, finite-type
morphisms, or Fourier--Mukai kernels—even when their proofs are primarily
category theoretic. Proof technique does not determine source ownership.

In particular:

- abstract stability-family data remain in
  `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families`;
- scheme, Dqc, pullback, finite-type, and kernel realizations live in
  `DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families`;
- `CategoryTheory` must not import either `DerivedAlgGeo.AlgebraicGeometry` or
  `Mathlib.AlgebraicGeometry`;
- `Compatibility` and `Development` are leaf layers and must never become
  dependencies of stable subject modules.

The source-layer gate in `scripts/check_layering.py` reconstructs the collapsed
graph from every tracked library import, rejects cycles and forbidden reverse
edges, and verifies that the relocated geometric family modules do not return
to their former owner.

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
| Generic family interfaces | `DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families` |
| Scheme-specific realizations | `DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families` |
| Former combined surface during migration | `DerivedAlgGeo.Compatibility.StabilityConditionFamilies` |

New library code should use the narrow owner import. The Compatibility import
is public but intentionally a leaf; it provides staged migration without
reintroducing a CategoryTheory-to-geometry edge.
