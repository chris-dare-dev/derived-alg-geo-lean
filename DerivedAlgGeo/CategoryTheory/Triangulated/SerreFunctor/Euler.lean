/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm

/-!
# Serre duality and the Hom-built Euler form

For a Hom-finite category, Serre duality identifies each summand of `χ(A, B)`
with the summand of `χ(B, S A)` in the opposite degree. Reindexing by negation
proves the identity, even though `finsum` is junk-total without finite support.
The bounded corollary supplies that support. This argument needs linearity of
every shift functor, but does not require the Serre functor to be an equivalence
or to commute with shifts.

## Main results

`SerreFunctorData.chiHom_eq_chiHom_swap_serre` states the twisted identity under
`HomFinite`. `SerreFunctorData.chiHom_eq_chiHom_swap_serre_of_bounded` supplies
the version with `HomFiniteBounded`, ensuring the Euler sums have finite support.
Shifting the second argument by `n` multiplies the Euler sum by `(-1)^n`.

* `SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_of_serre_shift` gives the
  pointwise formula for an arbitrary comparison object.
* `SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_of_serre_shift_of_bounded`
  makes it an equality of finite Euler sums.
* `SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_twist` specializes the
  comparison object to a functor's image of `A`.
* `SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_twist_of_bounded` gives
  that specialization with finite Hom support.
* `SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_twist_of_natIso` takes
  its pointwise comparison from a natural isomorphism.

Without `HomFiniteBounded`, the sums may still be junk-total.
-/

universe w v u

namespace CategoryTheory.SerreFunctor

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
  CategoryTheory.Pretriangulated Module

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
private theorem homFinite_of_bounded [HomFiniteBounded k C] : HomFinite k C := by
  refine ⟨fun A B => ?_⟩
  let e : (A ⟶ B⟦(0 : ℤ)⟧) ≃ₗ[k] (A ⟶ B) :=
    Linear.homCongr k (Iso.refl A) ((shiftFunctorZero C ℤ).app B)
  exact Module.Finite.equiv e

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
private theorem finrank_hom_shift_right (A B : C) (n i : ℤ) :
    finrank k (A ⟶ (B⟦n⟧)⟦i⟧) = finrank k (A ⟶ B⟦i + n⟧) := by
  have e : (A ⟶ B⟦n + i⟧) ≃ₗ[k] (A ⟶ (B⟦n⟧)⟦i⟧) :=
    Linear.homCongr k (Iso.refl A) ((shiftFunctorAdd C n i).app B)
  calc
    finrank k (A ⟶ (B⟦n⟧)⟦i⟧) = finrank k (A ⟶ B⟦n + i⟧) := e.finrank_eq.symm
    _ = finrank k (A ⟶ B⟦i + n⟧) := by rw [add_comm n i]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- Shifting the second argument of the Hom-built Euler sum by `n` multiplies
it by `(-1)^n`. This identity also holds for the junk-total sum; use
`HomFiniteBounded` when the sum must represent a finite Euler form. -/
private theorem chiHom_shift_right (A B : C) (n : ℤ) :
    chiHom k C A (B⟦n⟧) = (n.negOnePow : ℤ) * chiHom k C A B := by
  unfold chiHom
  rw [mul_finsum]
  apply finsum_eq_of_bijective (fun i : ℤ => i + n)
  · constructor
    · intro i j h
      exact add_right_cancel h
    · intro j
      exact ⟨j - n, by dsimp; omega⟩
  · intro i
    rw [finrank_hom_shift_right k C A B n i]
    simp only [Int.negOnePow_add, Units.val_mul]
    have hn : (n.negOnePow : ℤ) * (n.negOnePow : ℤ) = 1 := by
      calc
        _ = ((n.negOnePow * n.negOnePow : ℤˣ) : ℤ) := by simp
        _ = 1 := by rw [Int.units_mul_self]; rfl
    calc
      _ = ((n.negOnePow : ℤ) * (n.negOnePow : ℤ)) *
          ((i.negOnePow : ℤ) * (finrank k (A ⟶ B⟦i + n⟧) : ℤ)) := by rw [hn]; ring
      _ = _ := by ring

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
/-- The Hom-built Euler sum is invariant under an isomorphism of its second
argument. Without bounded Hom support, both sides may be junk-total. -/
private theorem chiHom_congr_right (A : C) {B B' : C} (e : B ≅ B') :
    chiHom k C A B = chiHom k C A B' := by
  unfold chiHom
  apply finsum_congr
  intro i
  have ei : (A ⟶ B⟦i⟧) ≃ₗ[k] (A ⟶ B'⟦i⟧) :=
    Linear.homCongr k (Iso.refl A) ((shiftFunctor C i).mapIso e)
  rw [ei.finrank_eq]

section HomFinite

variable [HomFinite k C]

omit [HasZeroObject C] [Pretriangulated C] in
private theorem finrank_hom_serre_shift (D : SerreFunctorData k C)
    (A B : C) (i : ℤ) :
    finrank k (A ⟶ B⟦i⟧) = finrank k (B ⟶ (D.S.obj A)⟦-i⟧) := by
  let eShift : (B⟦i⟧ ⟶ D.S.obj A) ≃ₗ[k]
      ((B⟦i⟧)⟦-i⟧ ⟶ (D.S.obj A)⟦-i⟧) :=
    homLinearEquivOfFullyFaithful (shiftFunctor C (-i))
      (shiftEquiv C (-i)).fullyFaithfulFunctor _ _
  let e : (B⟦i⟧ ⟶ D.S.obj A) ≃ₗ[k]
      (B ⟶ (D.S.obj A)⟦-i⟧) :=
    eShift.trans (Linear.homCongr k (shiftShiftNeg B i)
      (Iso.refl ((D.S.obj A)⟦-i⟧)))
  exact (D.finrank_hom_eq A (B⟦i⟧)).trans e.finrank_eq

omit [HasZeroObject C] [Pretriangulated C] in
/-- Serre duality gives `χ(A, B) = χ(B, S A)` for the Hom-built Euler form.
The sum can be junk-total without a finite-support witness; use the bounded
corollary for the mathematically meaningful Euler form. -/
theorem SerreFunctorData.chiHom_eq_chiHom_swap_serre
    (D : SerreFunctorData k C) (A B : C) :
    chiHom k C A B = chiHom k C B (D.S.obj A) := by
  unfold chiHom
  apply finsum_eq_of_bijective (fun i : ℤ => -i)
  · exact ⟨neg_injective, neg_surjective⟩
  · intro i
    rw [finrank_hom_serre_shift k C D A B i, Int.negOnePow_neg]

end HomFinite

omit [HasZeroObject C] [Pretriangulated C] in
/-- The twisted Euler identity with finite support of the Hom-built sums. -/
theorem SerreFunctorData.chiHom_eq_chiHom_swap_serre_of_bounded
    [HomFiniteBounded k C] (D : SerreFunctorData k C) (A B : C) :
    chiHom k C A B = chiHom k C B (D.S.obj A) := by
  letI : HomFinite k C := homFinite_of_bounded k C
  exact D.chiHom_eq_chiHom_swap_serre k C A B

section ShiftedSerreImage

variable (D : SerreFunctorData k C) (A B X : C) (n : ℤ)

omit [HasZeroObject C] [Pretriangulated C] in
/-- A pointwise identification of the Serre image of `A` with `X⟦n⟧`
gives the signed Euler identity. Without bounded Hom support, the Euler
sums may be junk-total. -/
theorem SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_of_serre_shift
    [HomFinite k C] (e : D.S.obj A ≅ X⟦n⟧) :
    chiHom k C A B = (n.negOnePow : ℤ) * chiHom k C B X := by
  rw [D.chiHom_eq_chiHom_swap_serre k C A B,
    chiHom_congr_right k C B e,
    chiHom_shift_right k C B X n]

omit [HasZeroObject C] [Pretriangulated C] in
/-- Bounded Hom support makes the signed pointwise identity an equality of
actual finite Euler sums. -/
theorem SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_of_serre_shift_of_bounded
    [HomFiniteBounded k C] (e : D.S.obj A ≅ X⟦n⟧) :
    chiHom k C A B = (n.negOnePow : ℤ) * chiHom k C B X := by
  letI : HomFinite k C := homFinite_of_bounded k C
  exact D.chiHom_eq_negOnePow_mul_chiHom_of_serre_shift k C A B X n e

end ShiftedSerreImage

section ShiftedTwist

variable (D : SerreFunctorData k C) (T : C ⥤ C) (A B : C) (n : ℤ)

omit [HasZeroObject C] [Pretriangulated C] in
/-- The pointwise signed Euler identity when the comparison object is the
image of `A` under a fixed twist functor. -/
theorem SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_twist [HomFinite k C]
    (e : D.S.obj A ≅ (T.obj A)⟦n⟧) :
    chiHom k C A B = (n.negOnePow : ℤ) * chiHom k C B (T.obj A) :=
  D.chiHom_eq_negOnePow_mul_chiHom_of_serre_shift k C A B (T.obj A) n e

omit [HasZeroObject C] [Pretriangulated C] in
/-- Bounded Hom support makes the twist formula an equality of finite
Euler sums, instead of potentially junk-total sums. -/
theorem SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_twist_of_bounded
    [HomFiniteBounded k C] (e : D.S.obj A ≅ (T.obj A)⟦n⟧) :
    chiHom k C A B = (n.negOnePow : ℤ) * chiHom k C B (T.obj A) :=
  D.chiHom_eq_negOnePow_mul_chiHom_of_serre_shift_of_bounded k C A B (T.obj A) n e

omit [HasZeroObject C] [Pretriangulated C] in
/-- A natural identification `S ≅ T ⋙ [n]` supplies the objectwise comparison
used in the bounded signed Euler identity. -/
theorem SerreFunctorData.chiHom_eq_negOnePow_mul_chiHom_twist_of_natIso
    [HomFiniteBounded k C] (e : D.S ≅ T ⋙ shiftFunctor C n) :
    chiHom k C A B = (n.negOnePow : ℤ) * chiHom k C B (T.obj A) :=
  D.chiHom_eq_negOnePow_mul_chiHom_twist_of_bounded k C T A B n (e.app A)

end ShiftedTwist

end CategoryTheory.SerreFunctor
