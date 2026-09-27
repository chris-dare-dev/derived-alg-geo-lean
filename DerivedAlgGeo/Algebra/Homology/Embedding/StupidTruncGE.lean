/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Inclusions between stupid truncations of cochain complexes

Mathlib's degree-at-least stupid truncation has a canonical inclusion into the
original complex. Nested truncations inherit compatible inclusions in any
category with zero morphisms and a zero object.

## Main definitions and results

* `HomologicalComplex.stupidTruncGEXIso` supplies a stable integer-indexed
  component comparison for Mathlib's natural-number-indexed tail embedding.
* `HomologicalComplex.stupidTruncGEι` includes a tail in its source complex.
* `HomologicalComplex.stupidTruncGEMap` includes a deeper tail in a shallower
  one; `stupidTruncGEMap_self` and `stupidTruncGEMap_comp` give its identity
  and composition laws.
* `HomologicalComplex.stupidTruncGEMap_naturality` commutes tail inclusion
  with a cochain map.

## Implementation notes

On retained degrees, the maps use Mathlib's canonical truncation isomorphism;
outside the tail they use zero morphisms. The tail inclusion is monic, so its
composition with the original-complex inclusion characterizes nested maps.

## References

The construction extends `HomologicalComplex.stupidTrunc` and
`HomologicalComplex.stupidTruncXIso` from Mathlib's
`Algebra/Homology/Embedding/StupidTrunc.lean`.
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

/-- Restrict the differential to the retained degrees, then extend it back
across the embedding. The two canonical term isomorphisms identify this
restriction-extension differential with the original differential. -/
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

/-- Mathlib indexes the degree-at-least embedding by natural numbers. The
canonical choice `(i - p).toNat` gives one integer-indexed component comparison
that subsequent adjacent-column formulas can reuse. -/
noncomputable def stupidTruncGEXIso
    (K : HomologicalComplex C (ComplexShape.up ℤ)) (p i : ℤ) (hi : p ≤ i) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X i ≅ K.X i :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p)
    (i := (i - p).toNat) (by
      change p + ((i - p).toNat : ℤ) = i
      rw [Int.toNat_of_nonneg (by omega)]
      omega)

/-- The embedding equation forces `k = (i - p).toNat`. Substituting that
unique index identifies Mathlib's component isomorphism with the normalized
one, independent of the caller's witness. -/
@[simp]
lemma stupidTruncXIso_eq_stupidTruncGEXIso
    (K : HomologicalComplex C (ComplexShape.up ℤ)) (p i : ℤ) (k : ℕ)
    (h : (ComplexShape.embeddingUpIntGE p).f k = i) :
    K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) h =
      stupidTruncGEXIso K p i (by
        change p + (k : ℤ) = i at h
        omega) := by
  have hk : k = (i - p).toNat := by
    change p + (k : ℤ) = i at h
    rw [show i - p = (k : ℤ) by omega]
    simp
  subst k
  rfl

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

/-- Include the `q`-tail into the `p`-tail when `p ≤ q`. Its components are
the supported-degree isomorphisms or zero; composing with the monic inclusion
of the `p`-tail into the original complex characterizes the map. -/
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

/-- Postcompose both candidate maps with the monic inclusion of the `p`-tail
into the original complex. Their composites coincide by the nested-tail
inclusion law, so the candidate maps are equal. -/
@[reassoc (attr := simp)]
lemma stupidTruncGEMap_comp (K : HomologicalComplex C (ComplexShape.up ℤ))
    (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r) :
    stupidTruncGEMap K q r hqr ≫ stupidTruncGEMap K p q hpq =
      stupidTruncGEMap K p r (hpq.trans hqr) := by
  rw [← cancel_mono (stupidTruncGEι K p), Category.assoc]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A cochain map commutes with nested-tail inclusion. On retained degrees,
both composites reduce to the same map after transporting through the
stupid-truncation degreewise isomorphisms; elsewhere the source is zero. -/
lemma stupidTruncGEMap_naturality
    {K L : HomologicalComplex C (ComplexShape.up ℤ)} (f : K ⟶ L)
    (p q : ℤ) (hpq : p ≤ q) :
    stupidTruncMap f (ComplexShape.embeddingUpIntGE q) ≫
        stupidTruncGEMap L p q hpq =
      stupidTruncGEMap K p q hpq ≫
        stupidTruncMap f (ComplexShape.embeddingUpIntGE p) := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : q ≤ i
  · dsimp [stupidTruncGEMap]
    rw [dif_pos hi, dif_pos hi]
    let eK₀ := stupidTruncGEXIso K q i hi
    let eK₁ := stupidTruncGEXIso K p i (hpq.trans hi)
    let eL₀ := stupidTruncGEXIso L q i hi
    let eL₁ := stupidTruncGEXIso L p i (hpq.trans hi)
    simp only [stupidTruncXIso_eq_stupidTruncGEXIso]
    rw [← cancel_mono eL₁.hom]
    simp only [Category.assoc, eL₁.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, ← Category.assoc]
    dsimp [eK₀, eK₁, eL₀, eL₁, stupidTruncGEXIso]
    rw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom]
    simp only [Category.assoc]
    rw [HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom]
    simp
  · apply IsZero.eq_of_src
    apply HomologicalComplex.isZero_stupidTrunc_X
    rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]
    omega

end HomologicalComplex
