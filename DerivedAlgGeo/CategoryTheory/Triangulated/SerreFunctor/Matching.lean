/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor.Transport
import Mathlib.Data.Fintype.EquivFin

/-!
# Matching classified objects across an equivalence

The refined Torelli arguments first recover the exceptional-block indices
from their residual projection objects.  Completeness says that the image of
each classified object is a shift of a target candidate; separation makes the
target index unique.  Applying the same argument to the inverse equivalence
proves that the resulting map is a bijection.

This file carries out that formal argument for both classification shapes used
by the Enriques papers.  For a mixed classification, positivity of the block
lengths is the only extra hypothesis needed to know that every candidate is
either spherical or pseudoprojective.  The result preserves the coarse block
kind (singleton versus longer); equality of the lengths of two longer blocks
requires the subsequent extension induction and is deliberately not asserted
here.
-/

universe w v v' u u' t t'

namespace CategoryTheory.SerreFunctor

open CategoryTheory

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasShift C ℤ]
variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear k D]
  [HasShift D ℤ]
variable {S_C : SerreFunctorData k C} {S_D : SerreFunctorData k D}

namespace SphericalClassificationData

variable {n : ℕ} {I : Type t} {J : Type t'}
variable (A : SphericalClassificationData S_C n I)
  (B : SphericalClassificationData S_D n J)
  (F : SerreCompatibleEquivalence S_C S_D)

/-- The target index represented by the image of a source candidate. -/
noncomputable def matchIndex (i : I) : J :=
  Classical.choose ((B.complete _).mp (F.mapSpherical (A.candidate_spherical i)))

/-- The image of a source candidate is a shift of its matched target
candidate. -/
theorem matchIndex_spec (i : I) :
    IsShiftOf (F.equiv.functor.obj (A.candidate i))
      (B.candidate (A.matchIndex B F i)) :=
  Classical.choose_spec
    ((B.complete _).mp (F.mapSpherical (A.candidate_spherical i)))

/-- Separation of the classified candidates makes the matching map
injective. -/
theorem matchIndex_injective : Function.Injective (A.matchIndex B F) := by
  intro i i' hii'
  by_contra hne
  apply A.candidate_not_isShiftOf hne
  apply F.isShiftOf_iff.mp
  exact (A.matchIndex_spec B F i).trans
    ((A.matchIndex_spec B F i').of_iso_right (by rw [hii'])).symm

/-- The inverse classification gives an injection in the opposite
direction. -/
theorem reverse_matchIndex_injective :
    Function.Injective (B.matchIndex A F.symm) :=
  B.matchIndex_injective A F.symm

section Finite

variable [Fintype I] [Fintype J]

/-- Classified spherical candidates are canonically reindexed by a
Serre-compatible equivalence. -/
noncomputable def matchingEquiv : I ≃ J :=
  Equiv.ofBijective (A.matchIndex B F) ⟨A.matchIndex_injective B F, by
    have hIJ : Fintype.card I ≤ Fintype.card J :=
      Fintype.card_le_of_injective _ (A.matchIndex_injective B F)
    have hJI : Fintype.card J ≤ Fintype.card I :=
      Fintype.card_le_of_injective _ (A.reverse_matchIndex_injective B F)
    exact ((Fintype.bijective_iff_injective_and_card
      (A.matchIndex B F)).2 ⟨A.matchIndex_injective B F,
        Nat.le_antisymm hIJ hJI⟩).2⟩

@[simp]
theorem matchingEquiv_apply (i : I) :
    A.matchingEquiv B F i = A.matchIndex B F i :=
  rfl

/-- The matching equivalence carries the candidate-shift comparison proved
by completeness. -/
theorem matchingEquiv_spec (i : I) :
    IsShiftOf (F.equiv.functor.obj (A.candidate i))
      (B.candidate (A.matchingEquiv B F i)) :=
  A.matchIndex_spec B F i

end Finite

end SphericalClassificationData

namespace MixedClassificationData

variable {n : ℕ} {I : Type t} {J : Type t'}
variable (A : MixedClassificationData S_C n I)
  (B : MixedClassificationData S_D n J)
  (F : SerreCompatibleEquivalence S_C S_D)
variable (hA : ∀ i, 0 < A.blockLength i)
  (hB : ∀ j, 0 < B.blockLength j)

/-- The target index represented by the image of a source candidate.  The
definition branches only on whether the source block is a singleton or a
longer block. -/
noncomputable def matchIndex (i : I) : J :=
  if hi : A.blockLength i = 1 then
    Classical.choose ((B.spherical_complete _).mp
      (F.mapSpherical (A.candidate_spherical (i := i) hi)))
  else
    Classical.choose ((B.pseudoprojective_complete _).mp
      (F.mapPseudoprojective
        (A.candidate_pseudoprojective (i := i) (by
          have := hA i
          omega))))

/-- Singleton source blocks match singleton target blocks. -/
theorem matchIndex_length_eq_one {i : I} (hi : A.blockLength i = 1) :
    B.blockLength (A.matchIndex B F hA i) = 1 := by
  rw [matchIndex, dif_pos hi]
  exact (Classical.choose_spec ((B.spherical_complete _).mp
      (F.mapSpherical (A.candidate_spherical (i := i) hi)))).1

/-- Longer source blocks match longer target blocks. -/
theorem matchIndex_length_two_le {i : I} (hi : 2 ≤ A.blockLength i) :
    2 ≤ B.blockLength (A.matchIndex B F hA i) := by
  rw [matchIndex, dif_neg (by omega)]
  exact (Classical.choose_spec ((B.pseudoprojective_complete _).mp
    (F.mapPseudoprojective
      (A.candidate_pseudoprojective (i := i) hi)))).1

/-- The image of every source candidate is a shift of its matched target
candidate. -/
theorem matchIndex_spec (i : I) :
    IsShiftOf (F.equiv.functor.obj (A.candidate i))
      (B.candidate (A.matchIndex B F hA i)) := by
  by_cases hi : A.blockLength i = 1
  · rw [matchIndex, dif_pos hi]
    exact (Classical.choose_spec ((B.spherical_complete _).mp
      (F.mapSpherical (A.candidate_spherical (i := i) hi)))).2
  · rw [matchIndex, dif_neg hi]
    exact (Classical.choose_spec ((B.pseudoprojective_complete _).mp
      (F.mapPseudoprojective
        (A.candidate_pseudoprojective (i := i) (by
          have := hA i
          omega))))).2

/-- Separation of spherical and pseudoprojective candidates makes the mixed
matching injective. -/
theorem matchIndex_injective : Function.Injective (A.matchIndex B F hA) := by
  intro i i' hii'
  have hshift : IsShiftOf (A.candidate i) (A.candidate i') := by
    apply F.isShiftOf_iff.mp
    exact (A.matchIndex_spec B F hA i).trans
      ((A.matchIndex_spec B F hA i').of_iso_right (by rw [hii'])).symm
  rcases lt_or_ge (A.blockLength i) 2 with hi | hi
  · have hi1 : A.blockLength i = 1 := by
      have := hA i
      omega
    have hj1 : B.blockLength (A.matchIndex B F hA i) = 1 :=
      A.matchIndex_length_eq_one B F hA hi1
    have hi'1 : A.blockLength i' = 1 := by
      by_contra h
      have hi'2 : 2 ≤ A.blockLength i' := by
        have := hA i'
        omega
      have hj2 : 2 ≤ B.blockLength (A.matchIndex B F hA i') :=
        A.matchIndex_length_two_le B F hA hi'2
      rw [← hii', hj1] at hj2
      omega
    by_contra hne
    exact A.spherical_candidate_not_isShiftOf hi1 hne hshift
  · have hj2 : 2 ≤ B.blockLength (A.matchIndex B F hA i) :=
      A.matchIndex_length_two_le B F hA hi
    have hi'2 : 2 ≤ A.blockLength i' := by
      by_contra h
      have hi'1 : A.blockLength i' = 1 := by
        have := hA i'
        omega
      have hj1 : B.blockLength (A.matchIndex B F hA i') = 1 :=
        A.matchIndex_length_eq_one B F hA hi'1
      rw [hii', hj1] at hj2
      omega
    by_contra hne
    exact A.pseudoprojective_candidate_not_isShiftOf hi hne hshift

section Finite

variable [Fintype I] [Fintype J]

/-- Mixed classified candidates are reindexed by a Serre-compatible
equivalence. -/
noncomputable def matchingEquiv : I ≃ J :=
  Equiv.ofBijective (A.matchIndex B F hA) ⟨A.matchIndex_injective B F hA, by
    have hIJ : Fintype.card I ≤ Fintype.card J :=
      Fintype.card_le_of_injective _ (A.matchIndex_injective B F hA)
    have hJI : Fintype.card J ≤ Fintype.card I :=
      Fintype.card_le_of_injective _
        (B.matchIndex_injective A F.symm hB)
    exact ((Fintype.bijective_iff_injective_and_card
      (A.matchIndex B F hA)).2 ⟨A.matchIndex_injective B F hA,
        Nat.le_antisymm hIJ hJI⟩).2⟩

@[simp]
theorem matchingEquiv_apply (i : I) :
    A.matchingEquiv B F hA hB i = A.matchIndex B F hA i :=
  rfl

/-- The matching equivalence preserves singleton blocks. -/
theorem matchingEquiv_length_eq_one_iff (i : I) :
    B.blockLength (A.matchingEquiv B F hA hB i) = 1 ↔
      A.blockLength i = 1 := by
  constructor
  · intro hj
    change B.blockLength (A.matchIndex B F hA i) = 1 at hj
    rcases lt_or_ge (A.blockLength i) 2 with hi | hi
    · have := hA i
      omega
    · have hlong := A.matchIndex_length_two_le B F hA hi
      omega
  · exact A.matchIndex_length_eq_one B F hA

/-- The matching equivalence preserves longer blocks. -/
theorem matchingEquiv_length_two_le_iff (i : I) :
    2 ≤ B.blockLength (A.matchingEquiv B F hA hB i) ↔
      2 ≤ A.blockLength i := by
  constructor
  · intro hj
    change 2 ≤ B.blockLength (A.matchIndex B F hA i) at hj
    rcases lt_or_ge (A.blockLength i) 2 with hi | hi
    · have hi1 : A.blockLength i = 1 := by
        have := hA i
        omega
      have hsingle := A.matchIndex_length_eq_one B F hA hi1
      omega
    · exact hi
  · exact A.matchIndex_length_two_le B F hA

/-- The image of every mixed candidate is a shift of the target candidate
selected by the matching equivalence. -/
theorem matchingEquiv_spec (i : I) :
    IsShiftOf (F.equiv.functor.obj (A.candidate i))
      (B.candidate (A.matchingEquiv B F hA hB i)) :=
  A.matchIndex_spec B F hA i

end Finite

end MixedClassificationData

end CategoryTheory.SerreFunctor
