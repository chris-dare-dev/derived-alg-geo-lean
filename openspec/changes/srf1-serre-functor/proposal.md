# Proposal

## Why

Milestone SRF1 has three remaining open issues that complete the abstract and geometric consequences of the Serre duality core already in the repository. The issues depend on one another, and the repository’s completed linear Serre ownership cutover changes where part of the original issue path plan belongs.

## What Changes

- Complete #897 with Hom-finiteness-dependent full faithfulness and a separate co-Serre input for essential surjectivity.
- Complete #898 by deriving ordinary conjugation transport in the linear owner, then proving the shift, triangulated, and Euler-form consequences in the triangulated owner.
- Complete #899 with an explicitly supplied geometric Serre duality record and its one-way projections, without claiming the current sheaf data constructs it.
- Run the work as three dependency-ordered issue stages. The first manifest covers #897; later successor manifests will bind to the merged predecessor evidence and be refreshed against live issue state.

## Capabilities

### New Capabilities

- `serre-functor`: full faithfulness and equivalence inputs, conjugation and shift transport, Euler-form symmetry, and the supplied geometric bridge for Serre duality.

### Modified Capabilities

- None. The repository has no existing OpenSpec capability specs.

## Impact

The plan uses the existing roots `CategoryTheory/Linear/SerreFunctor/`, `CategoryTheory/Triangulated/SerreFunctor/`, and `AlgebraicGeometry/Duality/Serre/`. It consumes the existing `SerreFunctorData`, `HomFinite`, `SerreCategoryData`, `BilinearData`, canonical-sheaf input, and bounded coherent derived-category presentation. It adds declarations and audit records at those owners, with no second category carrier, global geometric instance, or unsupported reverse comparison. The geometric bridge remains supplied and uninhabited until its stated missing inputs exist.
