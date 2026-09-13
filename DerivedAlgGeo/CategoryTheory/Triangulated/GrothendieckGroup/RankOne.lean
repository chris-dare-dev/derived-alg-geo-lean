/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial

/-!
# Rank-one maps on triangulated Grothendieck groups

An objectwise formula

`[F X] = χ([X]) • e`

is useful before a functor is known to be triangulated.  `K₀.IsRankOne` packages
that formula without asserting exactness.  Once the usual hypotheses for
`K₀.map` are available, the formula determines the induced homomorphism.

Here "rank one" means only that the displayed homomorphism factors through
`ℤ`; neither `χ` nor `e` is required to be nonzero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u' v'

namespace CategoryTheory.Triangulated

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The homomorphism `x ↦ χ(x) • e`, factored through `ℤ`. -/
def K₀.rankOne (χ : K₀ C →+ ℤ) (e : K₀ D) : K₀ C →+ K₀ D :=
  ((smulAddHom ℤ (K₀ D)).flip e).comp χ

@[simp]
theorem K₀.rankOne_apply (χ : K₀ C →+ ℤ) (e : K₀ D) (x : K₀ C) :
    K₀.rankOne χ e x = χ x • e :=
  rfl

/-- The object classes of `F` satisfy the rank-one formula determined by
`χ` and `e`.  This property does not assert that `F` is triangulated. -/
def K₀.IsRankOne (F : C ⥤ D) (χ : K₀ C →+ ℤ) (e : K₀ D) : Prop :=
  ∀ X : C, K₀.of D (F.obj X) = χ (K₀.of C X) • e

namespace K₀.IsRankOne

/-- The rank-one object formula is invariant under natural isomorphism. -/
theorem ofIso {F G : C ⥤ D} {χ : K₀ C →+ ℤ} {e : K₀ D}
    (hF : K₀.IsRankOne F χ e) (i : F ≅ G) : K₀.IsRankOne G χ e := by
  intro X
  rw [← K₀.of_iso D (i.app X)]
  exact hF X

/-- Under the hypotheses that make `K₀.map F` available, the objectwise
rank-one formula determines that homomorphism. -/
theorem map_eq_rankOne {F : C ⥤ D} {χ : K₀ C →+ ℤ} {e : K₀ D}
    (hF : K₀.IsRankOne F χ e) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] : K₀.map F = K₀.rankOne χ e := by
  ext X
  rw [K₀.map_of, K₀.rankOne_apply, hF X]

end K₀.IsRankOne

end CategoryTheory.Triangulated
