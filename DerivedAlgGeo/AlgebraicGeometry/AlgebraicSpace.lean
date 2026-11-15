/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.AlgebraicSpace.Basic
import DerivedAlgGeo.AlgebraicGeometry.AlgebraicSpace.FiberProduct

/-!
# Algebraic spaces

Algebraic spaces over a scheme `S` (Stacks 025Y): fppf sheaves on `Over S` with diagonal
representable by schemes and an étale surjective atlas by a scheme.

## Main definitions

None: this umbrella re-exports its children, among them `AlgebraicGeometry.isAlgebraicSpace` and
the category `AlgebraicGeometry.AlgebraicSpace`.

## Main results

None; this module re-exports its children, among them `AlgebraicGeometry.isAlgebraicSpace_yoneda`
(schemes are algebraic spaces, Stacks 025Z) and `AlgebraicGeometry.isAlgebraicSpace_pullback`
(fibre products, Stacks 04T9).

## Implementation notes

`AlgebraicSpace/Basic.lean` holds the definition, schemes as algebraic spaces, the underlying sheaf
and stack, and the universe conventions; `AlgebraicSpace/FiberProduct.lean` holds fibre products
and the terminal object. Nothing here imports algebraic stacks, moduli problems or stability
conditions.

## References

* [Stacks, Chapter 65 (Tag 025R)](https://stacks.math.columbia.edu/tag/025R)

## Tags

algebraic space
-/
