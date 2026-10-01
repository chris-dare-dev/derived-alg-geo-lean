/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.Embedding.StupidTrunc
import Mathlib.Algebra.Homology.HomologicalBicomplex
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant

/-!
# Degree-at-least stupid truncations and retained components

Mathlib's degree-at-least stupid truncation has a canonical inclusion into
its source cochain complex. Nested truncations have compatible inclusion maps
in any category with zero morphisms and a zero object.

## Main definitions

* `HomologicalComplex.stupidTruncGEι` includes a tail in its source complex.
* `HomologicalComplex.stupidTruncGEMap` includes a deeper tail in a shallower one.
* `HomologicalComplex.stupidTruncGETower` and
  `HomologicalComplex.stupidTruncGETowerCocone` collect the nested tails.
* `HomologicalComplex.stupidTruncGEXIso` chooses one component isomorphism at
  every retained integer degree, with a bicomplex specialization at
  `HomologicalComplex₂.stupidTruncGEXIso`.

## Main results

* `HomologicalComplex.stupidTruncGEMap_self` and
  `HomologicalComplex.stupidTruncGEMap_comp` give the nested-tail laws.
* `HomologicalComplex.isColimitStupidTruncGETowerCocone` proves that the tower
  recovers the original complex as a colimit.
* `HomologicalComplex.stupidTrunc_d_eq` describes the retained differential.

## Implementation notes

On retained degrees, the maps use Mathlib's canonical truncation isomorphism;
outside the tail they use zero morphisms. The inclusion into the source is
monic, so it characterizes the nested maps and proves their laws.
At each fixed degree, the lower-tail tower eventually becomes constant;
Mathlib's degreewise colimit criterion assembles these into a complex colimit.

## References

This extends Mathlib's `HomologicalComplex.stupidTrunc` and
`HomologicalComplex.stupidTruncXIso` in
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

/-- The component of a degree-at-least stupid truncation at a retained integer degree.
This chooses the normalized index `(i - p).toNat` for Mathlib's
`HomologicalComplex.stupidTruncXIso`;
`HomologicalComplex.stupidTruncXIso_eq_stupidTruncGEXIso` identifies every
retained-index presentation with this one. -/
noncomputable def stupidTruncGEXIso
    (K : HomologicalComplex C (ComplexShape.up ℤ)) (p i : ℤ) (hi : p ≤ i) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X i ≅ K.X i :=
  K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) (geIndex_spec p i hi)

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

/-- On retained degrees this uses `HomologicalComplex.stupidTruncXIso`; below
`p` its source component is zero. The resulting map is monic without an
abelian-category assumption. -/
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

/-- Compatibility with the monic `HomologicalComplex.stupidTruncGEι` maps
characterizes this nested-tail inclusion; cancellation gives its identity and
composition laws. -/
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

@[simp]
lemma stupidTruncGEMap_self (K : HomologicalComplex C (ComplexShape.up ℤ)) (p : ℤ) :
    stupidTruncGEMap K p p le_rfl = 𝟙 _ := by
  rw [← cancel_mono (stupidTruncGEι K p)]
  simp

@[reassoc (attr := simp)]
lemma stupidTruncGEMap_comp (K : HomologicalComplex C (ComplexShape.up ℤ))
    (p q r : ℤ) (hpq : p ≤ q) (hqr : q ≤ r) :
    stupidTruncGEMap K q r hqr ≫ stupidTruncGEMap K p q hpq =
      stupidTruncGEMap K p r (hpq.trans hqr) := by
  rw [← cancel_mono (stupidTruncGEι K p), Category.assoc]
  simp

end HomologicalComplex


namespace HomologicalComplex

universe u v

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]

/-- Stage `n` has lower cutoff `c - n`. If the components of `K` vanish
above some degree, each stage has finite degree support. The colimit
construction needs no such bound. -/
noncomputable def stupidTruncGETower (K : CochainComplex C ℤ) (c : ℤ) :
    ℕ ⥤ CochainComplex C ℤ where
  obj n := K.stupidTrunc (ComplexShape.embeddingUpIntGE (c - n))
  map {n m} f := HomologicalComplex.stupidTruncGEMap K (c - m) (c - n) (by
    have := leOfHom f
    omega)
  map_id n := by simp
  map_comp {n m l} f g := by
    symm
    apply HomologicalComplex.stupidTruncGEMap_comp

/-- The stage inclusions commute with the transition maps, and the vertex
is definitionally `K`; this lets the degreewise colimit criterion apply directly. -/
noncomputable def stupidTruncGETowerCocone (K : CochainComplex C ℤ) (c : ℤ) :
    Cocone (stupidTruncGETower K c) where
  pt := K
  ι := {
    app n := HomologicalComplex.stupidTruncGEι K (c - n)
    naturality := by
      intro n m f
      change HomologicalComplex.stupidTruncGEMap K (c - m) (c - n)
        (by have := leOfHom f; omega) ≫
        HomologicalComplex.stupidTruncGEι K (c - m) =
        HomologicalComplex.stupidTruncGEι K (c - n) ≫ 𝟙 K
      simp
  }

private lemma stupidTruncGEι_component_isIso (K : CochainComplex C ℤ) (p i : ℤ) (hi : p ≤ i) :
    IsIso ((HomologicalComplex.stupidTruncGEι K p).f i) := by
  dsimp [HomologicalComplex.stupidTruncGEι]
  rw [dif_pos hi]
  infer_instance

private noncomputable def isColimitStupidTruncGETowerEval (K : CochainComplex C ℤ) (c i : ℤ) :
    IsColimit ((HomologicalComplex.eval C (ComplexShape.up ℤ) i).mapCocone
      (stupidTruncGETowerCocone K c)) := by
  let n : ℕ := (c - i).toNat
  have hi : c - (n : ℤ) ≤ i := by dsimp [n]; omega
  let F := stupidTruncGETower K c ⋙ HomologicalComplex.eval C (ComplexShape.up ℤ) i
  have hF : F.IsEventuallyConstantFrom n := by
    intro m f
    have hnm : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast leOfHom f
    haveI : IsIso ((HomologicalComplex.stupidTruncGEι K (c - n)).f i) :=
      stupidTruncGEι_component_isIso K (c - n) i hi
    haveI : IsIso ((HomologicalComplex.stupidTruncGEι K (c - m)).f i) :=
      stupidTruncGEι_component_isIso K (c - m) i (by omega)
    have heq := congrArg (fun z => z.f i)
      (HomologicalComplex.stupidTruncGEMap_comp_ι K (c - m) (c - n) (by omega))
    change IsIso
      ((HomologicalComplex.stupidTruncGEMap K (c - m) (c - n) (by omega)).f i)
    exact IsIso.of_isIso_fac_right heq
  let s := (HomologicalComplex.eval C (ComplexShape.up ℤ) i).mapCocone
    (stupidTruncGETowerCocone K c)
  haveI : IsIso (s.ι.app n) := stupidTruncGEι_component_isIso K (c - n) i hi
  exact hF.isColimitOfIsIso s

/-- The lower stupid truncations recover every complex: at each fixed degree,
the inclusions are eventually isomorphisms. No upper bound or ambient colimits
are required. -/
noncomputable def isColimitStupidTruncGETowerCocone (K : CochainComplex C ℤ) (c : ℤ) :
    IsColimit (stupidTruncGETowerCocone K c) :=
  HomologicalComplex.isColimitOfEval _ _ (isColimitStupidTruncGETowerEval K c)

end HomologicalComplex

namespace HomologicalComplex₂

universe w

variable {C : Type w} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]
  (K : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))

/-- The bicomplex specialization of the normalized retained component
`HomologicalComplex.stupidTruncGEXIso`. It is definitionally the same iso as
Mathlib's `HomologicalComplex.stupidTruncXIso` at index `(i - p).toNat`. -/
noncomputable def stupidTruncGEXIso (p i : ℤ) (hi : p ≤ i) :
    (K.stupidTrunc (ComplexShape.embeddingUpIntGE p)).X i ≅ K.X i :=
  HomologicalComplex.stupidTruncGEXIso K p i hi

@[simp]
lemma stupidTruncXIso_eq_stupidTruncGEXIso (p i : ℤ) (k : ℕ)
    (h : (ComplexShape.embeddingUpIntGE p).f k = i) :
    K.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) h =
      stupidTruncGEXIso K p i (by
        change p + (k : ℤ) = i at h
        omega) := by
  exact HomologicalComplex.stupidTruncXIso_eq_stupidTruncGEXIso K p i k h

@[reassoc (attr := simp)]
lemma stupidTruncGEXIso_inv_hom_f (p i j : ℤ) (hi hi' : p ≤ i) :
    (stupidTruncGEXIso K p i hi).inv.f j ≫
      (stupidTruncGEXIso K p i hi').hom.f j = 𝟙 _ := by
  have : hi = hi' := Subsingleton.elim _ _
  subst this
  rw [← HomologicalComplex.comp_f,
    (stupidTruncGEXIso K p i hi).inv_hom_id,
    HomologicalComplex.id_f]

@[reassoc (attr := simp)]
lemma stupidTruncGEXIso_hom_inv_f (p i j : ℤ) (hi hi' : p ≤ i) :
    (stupidTruncGEXIso K p i hi).hom.f j ≫
      (stupidTruncGEXIso K p i hi').inv.f j = 𝟙 _ := by
  have : hi = hi' := Subsingleton.elim _ _
  subst this
  rw [← HomologicalComplex.comp_f,
    (stupidTruncGEXIso K p i hi).hom_inv_id,
    HomologicalComplex.id_f]

end HomologicalComplex₂
