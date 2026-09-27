/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Inclusions between stupid truncations of cochain complexes

Mathlib's degree-at-least stupid truncation has a canonical inclusion into the
original complex. Nested truncations inherit compatible inclusions. These
constructions need zero morphisms and a zero object, independently of any
filtration, totalization, or spectral sequence.
-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

private noncomputable def geIndex (p i : ℤ) : ℕ := (i - p).toNat

private lemma geIndex_spec (p i : ℤ) (h : p ≤ i) :
    (ComplexShape.embeddingUpIntGE p).f (geIndex p i) = i := by
  change p + ((i - p).toNat : ℤ) = i
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- On retained degrees, the truncation differential is the original one
transported across the canonical degreewise isomorphisms. -/
lemma stupidTrunc_d_eq (K : HomologicalComplex C (ComplexShape.up ℤ)) (p : ℤ)
    {i j : ℤ} (hi : p ≤ i) (hj : p ≤ j) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).d i j =
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) (geIndex_spec p i hi)).hom ≫
        K.d i j ≫
        (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
          (geIndex_spec p j hj)).inv := by
  change (((K.restriction (ComplexShape.embeddingUpIntGE p)).extend
    (ComplexShape.embeddingUpIntGE p)).d i j) = _
  rw [(K.restriction (ComplexShape.embeddingUpIntGE p)).extend_d_eq
      (ComplexShape.embeddingUpIntGE p) (geIndex_spec p i hi) (geIndex_spec p j hj),
    K.restriction_d_eq (ComplexShape.embeddingUpIntGE p)
      (geIndex_spec p i hi) (geIndex_spec p j hj)]
  simp [stupidTruncXIso, restrictionXIso, Category.assoc]
  all_goals aesop

/-- The inclusion of the stupid truncation in degrees at least `p` into the original complex. -/
noncomputable def stupidTruncGEι (K : HomologicalComplex C (ComplexShape.up ℤ)) (p : ℤ) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE p) ⟶ K where
  f i := if hi : p ≤ i then
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) (geIndex_spec p i hi)).hom
    else 0
  comm' i j hij := by
    by_cases hi : p ≤ i
    · have hj : p ≤ j := by
        have hij' : i + 1 = j := by
          simpa only [ComplexShape.up_Rel] using hij
        omega
      rw [dif_pos hi, dif_pos hj, stupidTrunc_d_eq K p hi hj]
      simp
    · apply IsZero.eq_of_src
      apply isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega

noncomputable instance stupidTruncGEι_f_mono
    (K : HomologicalComplex C (ComplexShape.up ℤ)) (p i : ℤ) :
    Mono ((stupidTruncGEι K p).f i) := by
  dsimp [stupidTruncGEι]
  split_ifs with hi
  · infer_instance
  · apply IsZero.mono
    apply isZero_stupidTrunc_X
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega

noncomputable instance stupidTruncGEι_mono
    (K : HomologicalComplex C (ComplexShape.up ℤ)) (p : ℤ) :
    Mono (stupidTruncGEι K p) :=
  mono_of_mono_f _ (fun _ ↦ inferInstance)

/-- Inclusion between nested stupid truncations.  If `p ≤ q`, the terms in degrees at
least `q` form a subcomplex of the terms in degrees at least `p`. -/
noncomputable def stupidTruncGEMap (K : HomologicalComplex C (ComplexShape.up ℤ))
    (p q : ℤ) (hpq : p ≤ q) :
    K.stupidTrunc (ComplexShape.embeddingUpIntGE q) ⟶
      K.stupidTrunc (ComplexShape.embeddingUpIntGE p) where
  f i := if hi : q ≤ i then
      (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE q) (geIndex_spec q i hi)).hom ≫
        (K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
          (geIndex_spec p i (hpq.trans hi))).inv
    else 0
  comm' i j hij := by
    by_cases hi : q ≤ i
    · have hj : q ≤ j := by
        have hij' : i + 1 = j := by
          simpa only [ComplexShape.up_Rel] using hij
        omega
      rw [dif_pos hi, dif_pos hj, stupidTrunc_d_eq K q hi hj,
        stupidTrunc_d_eq K p (hpq.trans hi) (hpq.trans hj)]
      simp
    · apply IsZero.eq_of_src
      apply isZero_stupidTrunc_X
      rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
      omega

/-- Nested inclusion followed by inclusion into the original complex agrees
with direct inclusion of the smaller tail. -/
@[reassoc (attr := simp)]
lemma stupidTruncGEMap_comp_ι (K : HomologicalComplex C (ComplexShape.up ℤ))
    (p q : ℤ) (hpq : p ≤ q) :
    stupidTruncGEMap K p q hpq ≫ stupidTruncGEι K p = stupidTruncGEι K q := by
  ext i
  by_cases hi : q ≤ i
  · rw [comp_f]
    simp [stupidTruncGEMap, stupidTruncGEι, hi, hpq.trans hi]
  · apply IsZero.eq_of_src
    apply isZero_stupidTrunc_X
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega

/-- The nested inclusion at an unchanged bound is the identity, by monicity
of the truncation's inclusion into the original complex. -/
@[simp]
lemma stupidTruncGEMap_self (K : HomologicalComplex C (ComplexShape.up ℤ)) (p : ℤ) :
    stupidTruncGEMap K p p le_rfl = 𝟙 _ := by
  rw [← cancel_mono (stupidTruncGEι K p)]
  simp

/-- Inclusions between three nested tails compose to the direct inclusion. -/
@[reassoc (attr := simp)]
lemma stupidTruncGEMap_comp (K : HomologicalComplex C (ComplexShape.up ℤ))
    (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r) :
    stupidTruncGEMap K q r hqr ≫ stupidTruncGEMap K p q hpq =
      stupidTruncGEMap K p r (hpq.trans hqr) := by
  rw [← cancel_mono (stupidTruncGEι K p), Category.assoc]
  simp

end HomologicalComplex
