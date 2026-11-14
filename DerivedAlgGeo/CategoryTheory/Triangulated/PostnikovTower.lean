/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.

Portions adapted from mattrobball/BridgelandStability, revision 9e48f23
(Apache-2.0, Copyright (c) 2026 Mathlib Contributors); see LICENSE.md.
-/
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Postnikov towers

A `PostnikovTower C E` packages a finite filtration of `E` by distinguished
triangles. It is the foundation the slicings of Bridgeland stability are built
on, and depends only on Mathlib.

## Main definitions

* `CategoryTheory.Triangulated.PostnikovTower`: a finite chain from a zero
  object to `E` whose consecutive steps are completed to distinguished
  triangles.
* `CategoryTheory.Triangulated.PostnikovTower.length`,
  `CategoryTheory.Triangulated.PostnikovTower.factor` and
  `CategoryTheory.Triangulated.PostnikovTower.factors`: the number of factors
  and the factor objects.

## Main results

* `CategoryTheory.Triangulated.PostnikovTower.isZero_of_length_zero`: a tower
  with no factors filters only a zero object.

## Implementation notes

The triangles are related to the chain only up to isomorphism
(`triangle_obj₁`, `triangle_obj₂`), and the top of the chain to `E` only up to
isomorphism (`top_iso`), each as a `Nonempty` field, so a tower is not tied to
chosen representatives.

## References

Mathlib's `ComposableArrows` and `Pretriangulated.Triangle`.

## Tags

Postnikov tower, filtration, distinguished triangle, triangulated category
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A finite Postnikov tower of `E`. The `i`-th factor is the third object of
the distinguished triangle connecting consecutive objects in the chain. -/
structure PostnikovTower (E : C) where
  /-- The number of factors. -/
  n : ℕ
  /-- The filtered chain `A₀ ⟶ A₁ ⟶ ⋯ ⟶ Aₙ`. -/
  chain : ComposableArrows C n
  /-- The triangle connecting each consecutive pair. -/
  triangle : Fin n → Pretriangulated.Triangle C
  /-- Every connecting triangle is distinguished. -/
  triangle_dist : ∀ i, triangle i ∈ distTriang C
  /-- The first triangle object agrees with the lower chain object. -/
  triangle_obj₁ : ∀ i, Nonempty ((triangle i).obj₁ ≅ chain.obj' i.val (by lia))
  /-- The second triangle object agrees with the upper chain object. -/
  triangle_obj₂ : ∀ i, Nonempty ((triangle i).obj₂ ≅ chain.obj' (i.val + 1) (by lia))
  /-- The tower begins at a zero object. -/
  base_isZero : IsZero chain.left
  /-- The top of the tower is isomorphic to the filtered object. -/
  top_iso : Nonempty (chain.right ≅ E)

/-- The number of factors in a Postnikov tower. -/
def PostnikovTower.length {E : C} (P : PostnikovTower C E) : ℕ := P.n

variable {C} in
/-- **A tower with no factors filters only a zero object.**

This is a theorem rather than a structure field: a length-zero chain starts
and ends at the same object, so `base_isZero` transported across `top_iso`
proves it. -/
theorem PostnikovTower.isZero_of_length_zero {E : C} (P : PostnikovTower C E)
    (h : P.n = 0) : IsZero E := by
  have h0 : P.chain.right = P.chain.left :=
    congrArg P.chain.obj (Fin.ext (by simp [h]))
  exact (h0 ▸ P.base_isZero).of_iso P.top_iso.some.symm

variable {C} in
/-- The `i`-th factor of a Postnikov tower. -/
def PostnikovTower.factor {E : C} (P : PostnikovTower C E) (i : Fin P.n) : C :=
  (P.triangle i).obj₃

variable {C} in
/-- The family of all factor objects of a Postnikov tower. -/
def PostnikovTower.factors {E : C} (P : PostnikovTower C E) : Fin P.n → C :=
  P.factor

end CategoryTheory.Triangulated
