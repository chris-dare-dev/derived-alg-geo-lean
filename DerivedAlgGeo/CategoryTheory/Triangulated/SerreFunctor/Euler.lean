/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm

/-!
# Serre duality and the Hom-built Euler form

For a Hom-finite bounded category, Serre duality identifies each summand of
`χ(A, B)` with the summand of `χ(B, S A)` in the opposite degree.  Reindexing
by negation proves the Euler identity.  This argument needs linearity of every
shift functor, but does not require the Serre functor to be an equivalence or to
commute with shifts.
-/

universe w v u

namespace CategoryTheory.SerreFunctor

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
  CategoryTheory.Pretriangulated Module

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [∀ n : ℤ, (shiftFunctor C n).Linear k] [HomFiniteBounded k C]

omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [∀ n : ℤ, (shiftFunctor C n).Linear k] in
private theorem homFinite_of_bounded : HomFinite k C := by
  refine ⟨fun A B => ?_⟩
  let e : (A ⟶ B⟦(0 : ℤ)⟧) ≃ₗ[k] (A ⟶ B) :=
    Linear.homCongr k (Iso.refl A) ((shiftFunctorZero C ℤ).app B)
  exact Module.Finite.equiv e

omit [HasZeroObject C] [Pretriangulated C] in
private theorem finrank_hom_serre_shift (D : SerreFunctorData k C)
    (A B : C) (i : ℤ) :
    finrank k (A ⟶ B⟦i⟧) = finrank k (B ⟶ (D.S.obj A)⟦-i⟧) := by
  letI : HomFinite k C := homFinite_of_bounded k C
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
/-- Serre duality gives `χ(A, B) = χ(B, S A)` for the Hom-built Euler form. -/
theorem SerreFunctorData.chiHom_symm (D : SerreFunctorData k C) (A B : C) :
    chiHom k C A B = chiHom k C B (D.S.obj A) := by
  unfold chiHom
  apply finsum_eq_of_bijective (fun i : ℤ => -i)
  · exact ⟨neg_injective, neg_surjective⟩
  · intro i
    rw [finrank_hom_serre_shift k C D A B i, Int.negOnePow_neg]

end CategoryTheory.SerreFunctor
