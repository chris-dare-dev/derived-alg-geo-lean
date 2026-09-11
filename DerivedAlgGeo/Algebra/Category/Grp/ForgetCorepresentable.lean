/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# Naturality of `AddCommGrpCat.uliftZMultiplesAddEquiv`

Mathlib's `uliftZMultiplesAddEquiv G : (of (ULift ℤ) ⟶ G) ≃+ G` is evaluation at `1`, so it
commutes with postcomposition. Mathlib states the equivalence but not this naturality, which
the degree-zero comparison between `Ext` and sheaf cohomology uses.
-/

universe u

open CategoryTheory

namespace AddCommGrpCat

/-- `uliftZMultiplesAddEquiv` is evaluation at `1`, so it is natural in the target. -/
lemma uliftZMultiplesAddEquiv_comp {G H : AddCommGrpCat.{u}} (φ : of (ULift.{u} ℤ) ⟶ G)
    (g : G ⟶ H) :
    uliftZMultiplesAddEquiv H (φ ≫ g) = g (uliftZMultiplesAddEquiv G φ) := rfl

end AddCommGrpCat
