/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.AffineSpace.Linear

/-!
# Affine space over a base scheme

Extensions of Mathlib's affine space `𝔸(n; S)` over a scheme `S`, in its namespace
`AlgebraicGeometry.AffineSpace`.

## Main definitions

None: this umbrella re-exports its children, among them `AffineSpace.linearKernel`, the solution
scheme of a finite linear system.

## Main results

None; this module re-exports its children, among them `AffineSpace.linearKernel.homOverEquiv`,
the functor of points of the solution scheme.

## Implementation notes

The children extend `Mathlib/AlgebraicGeometry/AffineSpace.lean` and need Mathlib alone. Nothing
here imports moduli, stacks or stability.

## References

* [Stacks, Lemma 99.16.1 (Tag 0DLC)](https://stacks.math.columbia.edu/tag/0DLC).

## Tags

affine space, linear system
-/
