/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# The bounded homotopy category `Kᵇ(C)`

Mathlib has `HomotopyCategory.Plus C`, the triangulated full subcategory of
`HomotopyCategory C (.up ℤ)` on bounded-below cochain complexes, but no
bounded analogue. This file supplies it: `HomotopyCategory.Bounded C` is the
full subcategory on complexes that are strictly bounded on both sides, with
the same three subcategory instances (`ContainsZero`, `IsStableUnderShift`,
`IsTriangulated`) proved the same way, so Mathlib's generic machinery makes
it pretriangulated.

## ForMathlib

Everything here is stated for a general preadditive `C` with binary
biproducts and mirrors `Mathlib.Algebra.Homology.HomotopyCategory.Plus`
declaration by declaration; it is upstreamable as written. Filed in place,
following the repository's `ForMathlib` pattern.

The repository's use is as substrate for a `HomFiniteBounded` witness
(#543): `Kᵇ` of a Hom-finite linear category is Hom-finite with finite
Ext-amplitude by inspection of components, with no localization Homs to
compute. Nothing here mentions that; this file is category plumbing only.
-/

universe w v u

open CategoryTheory Limits ZeroObject Pretriangulated

variable (C : Type u) [Category.{v} C]

namespace CochainComplex

open HomologicalComplex

/-- A cochain complex is bounded when it is strictly bounded on both sides. -/
protected def bounded [HasZeroMorphisms C] : ObjectProperty (CochainComplex C ℤ) :=
  fun K ↦ (∃ n : ℤ, K.IsStrictlyGE n) ∧ ∃ n : ℤ, K.IsStrictlyLE n

variable {C}

lemma bounded_iff [HasZeroMorphisms C] (K : CochainComplex C ℤ) :
    CochainComplex.bounded C K ↔
      (∃ n : ℤ, K.IsStrictlyGE n) ∧ ∃ n : ℤ, K.IsStrictlyLE n := Iff.rfl

variable [Preadditive C] [HasBinaryBiproducts C]

/-- The mapping cone of a map of complexes that are strictly bounded above is
strictly bounded above; the companion of `isStrictlyGE_mappingCone`. -/
lemma isStrictlyLE_mappingCone {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n₁ n₂ n : ℤ) [K.IsStrictlyLE n₁] [L.IsStrictlyLE n₂] (hn₁ : n₁ ≤ n + 1 := by lia)
    (hn₂ : n₂ ≤ n := by lia) :
    (mappingCone f).IsStrictlyLE n := by
  rw [isStrictlyLE_iff]
  intro i hi
  simp only [mappingCone.isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyLE n₁ _ (by lia), L.isZero_of_isStrictlyLE n₂ _ (by lia)⟩

end CochainComplex

namespace HomotopyCategory

variable [Preadditive C]

/-- The property of objects in `HomotopyCategory C (.up ℤ)` whose underlying
cochain complex is bounded on both sides. (Like `HomotopyCategory.plus`, this
property of objects is not closed under isomorphisms.) -/
def bounded : ObjectProperty (HomotopyCategory C (.up ℤ)) :=
  (CochainComplex.bounded C).strictMap (quotient _ _)

variable {C} in
@[simp]
lemma bounded_quotient_obj_iff (K : CochainComplex C ℤ) :
    bounded C ((quotient _ _).obj K) ↔ CochainComplex.bounded C K := by
  refine ⟨?_, fun h ↦ ⟨_, h⟩⟩
  simp only [bounded, ObjectProperty.strictMap_iff]
  rintro ⟨L, h, hL⟩
  obtain rfl : L = K := congr_arg Quotient.as hL
  exact h

variable {C} in
/-- Unfold the `strictMap` inductive into the existential a consumer can
`obtain` from; dependent elimination on `strictMap` itself fails whenever the
index is not already a literal `(quotient _ _).obj K`. -/
lemma bounded_iff_exists (X : HomotopyCategory C (.up ℤ)) :
    bounded C X ↔ ∃ K : CochainComplex C ℤ,
      CochainComplex.bounded C K ∧ (quotient _ _).obj K = X :=
  ObjectProperty.strictMap_iff _ _ _

instance bounded_containsZero [HasZeroObject C] : (bounded C).ContainsZero where
  exists_zero :=
    ⟨(HomotopyCategory.quotient _ _).obj 0, Functor.map_isZero _ (isZero_zero _), by
      simp only [bounded_quotient_obj_iff]
      exact ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩⟩

instance bounded_isStableUnderShift : (bounded C).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift K hK := by
        obtain ⟨K : CochainComplex _ _, rfl⟩ := K.quotient_obj_surjective
        simp only [bounded_quotient_obj_iff] at hK
        obtain ⟨⟨g, _⟩, ⟨l, _⟩⟩ := hK
        rw [ObjectProperty.prop_shift_iff, shift_quotient_obj,
          bounded_quotient_obj_iff]
        exact ⟨⟨g - n, K.isStrictlyGE_shift g n (g - n) (by lia)⟩,
          ⟨l - n, K.isStrictlyLE_shift l n (l - n) (by lia)⟩⟩ }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance bounded_isTriangulatedClosed₃ [HasZeroObject C] [HasBinaryBiproducts C] :
    (bounded C).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ := by
    obtain ⟨⟨g₁, _⟩, ⟨l₁, _⟩⟩ : (CochainComplex.bounded C) T.obj₁.as := by
      rwa [← bounded_quotient_obj_iff]
    obtain ⟨⟨g₂, _⟩, ⟨l₂, _⟩⟩ : (CochainComplex.bounded C) T.obj₂.as := by
      rwa [← bounded_quotient_obj_iff]
    obtain ⟨f : T.obj₁.as ⟶ T.obj₂.as, hf⟩ := (quotient _ _).map_surjective T.mor₁
    refine ⟨_, ?_,
      ⟨Triangle.π₃.mapIso (isoTriangleOfIso₁₂ T _ hT (mappingCone_triangleh_distinguished f)
        (Iso.refl _) (Iso.refl _) ?_)⟩⟩
    · dsimp
      simp only [bounded_quotient_obj_iff]
      exact ⟨⟨min (g₁ - 1) g₂, CochainComplex.isStrictlyGE_mappingCone f g₁ g₂ _
          (by simp) (by simp)⟩,
        ⟨max (l₁ - 1) l₂, CochainComplex.isStrictlyLE_mappingCone f l₁ l₂
          (max (l₁ - 1) l₂) (by omega) (by omega)⟩⟩
    · simp [hf]

instance bounded_isTriangulated [HasZeroObject C] [HasBinaryBiproducts C] :
    (bounded C).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- The homotopy category of bounded cochain complexes. -/
abbrev Bounded := (bounded C).FullSubcategory

namespace Bounded

/-- The inclusion of the homotopy category of bounded cochain complexes in the
homotopy category of all cochain complexes. -/
abbrev ι : Bounded C ⥤ HomotopyCategory C (.up ℤ) := (bounded C).ι

/-- The inclusion `HomotopyCategory.Bounded.ι C` is fully faithful. -/
abbrev fullyFaithfulι : (ι C).FullyFaithful := ObjectProperty.fullyFaithfulι _

end Bounded

end HomotopyCategory
