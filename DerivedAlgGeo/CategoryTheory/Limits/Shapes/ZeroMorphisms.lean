/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite support in a supplied coproduct

For a particular coproduct whose summands vanish outside a finite set, the sum
of its canonical projection-inclusion endomorphisms is the identity. Thus
incoming maps are determined by those finitely many projections. The converse
identifies the exact support premise needed by this finite identity. No
ambient finite-coproduct assumption or replacement coproduct is introduced.
-/

open CategoryTheory Category
open scoped BigOperators

universe u v w

namespace CategoryTheory.Limits.Sigma

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {I : Type w} (f : I → C) [HasCoproduct f]

section ChosenDecidableEq
variable [DecidableEq I]

private lemma sum_π_ι_eq_id_of_isZero_chosen (s : Finset I)
    (hz : ∀ i, i ∉ s → IsZero (f i)) :
    ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f) := by
  apply Sigma.hom_ext
  intro j
  rw [Preadditive.comp_sum, comp_id]
  by_cases hj : j ∈ s
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      rw [← assoc, Sigma.ι_π_of_ne _ hbj.symm, zero_comp]
    · exact fun h => False.elim (h hj)
  · have hjzero := (hz j hj).eq_zero_of_src (Sigma.ι f j)
    simp [hjzero]

private lemma isZero_of_sum_π_ι_eq_id_chosen (s : Finset I)
    (hid : ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f))
    (j : I) (hj : j ∉ s) : IsZero (f j) := by
  have hι : Sigma.ι f j = 0 := by
    calc
      Sigma.ι f j = Sigma.ι f j ≫ ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i := by
        rw [hid, comp_id]
      _ = 0 := by
        rw [Preadditive.comp_sum]
        apply Finset.sum_eq_zero
        intro i hi
        rw [← assoc, Sigma.ι_π_of_ne _ (by aesop), zero_comp]
  rw [IsZero.iff_id_eq_zero, ← Sigma.ι_π_eq_id f j, hι, zero_comp]

/-- Compose with the finite projection-inclusion identity for the given
projection convention to compare incoming maps on their nonzero support. -/
lemma hom_ext_of_finiteSupport (s : Finset I)
    (hz : ∀ i, i ∉ s → IsZero (f i)) {A : C} {x y : A ⟶ ∐ f}
    (h : ∀ i ∈ s, x ≫ Sigma.π f i = y ≫ Sigma.π f i) : x = y := by
  calc
    x = x ≫ ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i := by
      rw [sum_π_ι_eq_id_of_isZero_chosen f s hz, comp_id]
    _ = y ≫ ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i := by
      rw [Preadditive.comp_sum, Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← assoc, h i hi, assoc]
    _ = y := by rw [sum_π_ι_eq_id_of_isZero_chosen f s hz, comp_id]

/-- An incoming map is zero once its projections to the finite nonzero
support vanish. The projection convention remains the caller's. -/
lemma hom_eq_zero_of_finiteSupport (s : Finset I)
    (hz : ∀ i, i ∉ s → IsZero (f i)) {A : C} (x : A ⟶ ∐ f)
    (h : ∀ i ∈ s, x ≫ Sigma.π f i = 0) : x = 0 := by
  apply hom_ext_of_finiteSupport f s hz
  intro i hi
  simpa using h i hi

end ChosenDecidableEq

section ClassicalProjection
/-- Choose classical equality only in the generic projection-law statements. -/
noncomputable local instance finiteSupportDecidableEq : DecidableEq I := Classical.decEq I

/-- Check the finite projection-inclusion sum after every coproduct inclusion.
An omitted summand has zero inclusion; orthogonality leaves only the matching
projection on the finite support. No caller decidability instance is needed. -/
lemma sum_π_ι_eq_id_of_isZero (s : Finset I)
    (hz : ∀ i, i ∉ s → IsZero (f i)) :
    ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f) :=
  sum_π_ι_eq_id_of_isZero_chosen f s hz

/-- Conversely, the finite identity forces an omitted summand to be zero:
its inclusion is zero and its projection is a left inverse. -/
lemma isZero_of_sum_π_ι_eq_id (s : Finset I)
    (hid : ∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f))
    (j : I) (hj : j ∉ s) : IsZero (f j) :=
  isZero_of_sum_π_ι_eq_id_chosen f s hid j hj

/-- The finite projection-inclusion sum is the identity exactly when every
summand outside the finite support is zero. -/
lemma sum_π_ι_eq_id_iff_isZero (s : Finset I) :
    (∑ i ∈ s, Sigma.π f i ≫ Sigma.ι f i = 𝟙 (∐ f)) ↔
      ∀ i, i ∉ s → IsZero (f i) :=
  ⟨fun hid i hi => isZero_of_sum_π_ι_eq_id f s hid i hi,
    sum_π_ι_eq_id_of_isZero f s⟩

end ClassicalProjection
end CategoryTheory.Limits.Sigma
