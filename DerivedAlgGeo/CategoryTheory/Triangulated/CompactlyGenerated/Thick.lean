/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.FiniteSupport
import Mathlib.Algebra.FiveLemma
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.Triangulated.Generators

/-!
# Compact objects form a thick triangulated subcategory

`ObjectProperty.compactObjects.{0}` in a pretriangulated category is closed under
isomorphisms and shifts (`CompactObject.lean`, `FiniteSupport.lean`); this file adds
retracts, the zero object, and cones, so that it is a triangulated object property stable
under retracts, and every triangulated envelope of compact objects consists of compact
objects (`ObjectProperty.triangEnvelope_le_compactObjects`).

Everything is proved through the direct-sum comparison
`directSumToHom K X : ⨁ Hom(K, Xᵢ) → Hom(K, ∐ X)`, whose bijectivity for every
`Type`-indexed coproduct is compactness (`isCompactObject_iff_bijective_directSumToHom`).
Retracts are a two-out-of-three argument on that map; cones are the five lemma applied to
the rows `⨁ Hom(-, Xᵢ)` and `Hom(-, ∐ X)` along a distinguished triangle, both exact by
`Triangle.yoneda_exact₂` and `Triangle.yoneda_exact₃`, the first summandwise.

The geometric consumer is the compact/perfect comparison on `Dqc(X)` (#723): the perfect
locus is the essential image of the thick envelope of finite locally free sheaves, so it
consists of compact objects as soon as those sheaves are compact.

## Main results

* `IsCompactObject.of_retract`, `IsCompactObject.of_isZero`, `IsCompactObject.of_distTriang₃`.
* `directSumPrecomp_exact` — exactness of `⨁ Hom(-, Xᵢ)` from exactness of each `Hom(-, Xᵢ)`.
* the instances `IsStableUnderRetracts`, `ContainsZero`, `IsStableUnderShift ℤ`,
  `IsTriangulatedClosed₂`, `IsTriangulatedClosed₃`, `IsTriangulated` on
  `compactObjects.{0}`.
* `ObjectProperty.triangEnvelope_le_compactObjects`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped DirectSum ZeroObject

universe v u

namespace CategoryTheory

section Preadditive

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- A retract of a compact object is compact. -/
theorem IsCompactObject.of_retract {K L : C} (h : Retract K L) (hL : IsCompactObject.{0} L) :
    IsCompactObject.{0} K := by
  apply isCompactObject_of_bijective_directSumToHom
  intro ι _ X _
  have hφ := hL.bijective_directSumToHom X
  have hsplit : ∀ x : ⨁ i, (K ⟶ X i), directSumPrecomp X h.i (directSumPrecomp X h.r x) = x :=
    fun x ↦ by rw [directSumPrecomp_comp, h.retract, directSumPrecomp_id]
  constructor
  · intro x y hxy
    have h1 : directSumToHom L X (directSumPrecomp X h.r x) =
        directSumToHom L X (directSumPrecomp X h.r y) := by
      rw [directSumToHom_precomp, directSumToHom_precomp, hxy]
    rw [← hsplit x, ← hsplit y, hφ.1 h1]
  · intro f
    obtain ⟨z, hz⟩ := hφ.2 (h.r ≫ f)
    refine ⟨directSumPrecomp X h.i z, ?_⟩
    rw [directSumToHom_precomp, hz, ← Category.assoc, h.retract, Category.id_comp]

/-- A zero object is compact. -/
theorem IsCompactObject.of_isZero {K : C} (hK : IsZero K) : IsCompactObject.{0} K := by
  apply isCompactObject_of_bijective_directSumToHom
  intro ι _ X _
  refine ⟨fun x y _ ↦ ?_, fun _ ↦ ⟨0, hK.eq_of_src _ _⟩⟩
  ext i
  exact hK.eq_of_src _ _

instance ObjectProperty.compactObjects.isStableUnderRetracts :
    (ObjectProperty.compactObjects.{0} (C := C)).IsStableUnderRetracts where
  of_retract h hY := IsCompactObject.of_retract h hY

/-- Exactness of `⨁ Hom(-, Xᵢ)` at `B` along `A ⟶ B ⟶ Y` follows from exactness of each
`Hom(-, Xᵢ)`: a summandwise lift assembled on the finite support. -/
theorem directSumPrecomp_exact {ι : Type} [DecidableEq ι] (X : ι → C) {A B Y : C}
    (f : A ⟶ B) (g : B ⟶ Y) (hzero : f ≫ g = 0)
    (hex : ∀ (i : ι) (b : B ⟶ X i), f ≫ b = 0 → ∃ a : Y ⟶ X i, b = g ≫ a)
    (x : ⨁ i, (B ⟶ X i)) :
    directSumPrecomp X f x = 0 ↔ ∃ y : ⨁ i, (Y ⟶ X i), directSumPrecomp X g y = x := by
  classical
  constructor
  · intro hx
    have hx' : ∀ i, f ≫ x i = 0 := fun i ↦ by
      have := DFunLike.congr_fun hx i
      erw [directSumPrecomp_apply] at this
      exact this.trans (DFinsupp.zero_apply i)
    choose a ha using fun i ↦ hex i (x i) (hx' i)
    refine ⟨DirectSum.mk (fun i ↦ (Y ⟶ X i)) x.support (fun i ↦ a i.1), ?_⟩
    ext i
    rw [directSumPrecomp_apply]
    by_cases hi : i ∈ x.support
    · rw [DirectSum.mk_apply_of_mem hi]
      exact (ha i).symm
    · rw [DirectSum.mk_apply_of_notMem hi, Limits.comp_zero]
      exact (DFinsupp.notMem_support_iff.1 hi).symm
  · rintro ⟨y, rfl⟩
    ext i
    simp [reassoc_of% hzero]

end Preadditive

section Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Cone closure.** The third object of a distinguished triangle whose first two objects
are compact is compact: the five lemma for the rows `⨁ Hom(-, Xᵢ)` and `Hom(-, ∐ X)` along
the triangle and its rotation. -/
theorem IsCompactObject.of_distTriang₃ (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : IsCompactObject.{0} T.obj₁) (h₂ : IsCompactObject.{0} T.obj₂) :
    IsCompactObject.{0} T.obj₃ := by
  apply isCompactObject_of_bijective_directSumToHom
  intro ι _ X _
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (directSumPrecomp X (-(T.mor₁⟦(1 : ℤ)⟧'))) (directSumPrecomp X T.mor₃)
    (directSumPrecomp X T.mor₂) (directSumPrecomp X T.mor₁)
    (Preadditive.leftComp (∐ X) (-(T.mor₁⟦(1 : ℤ)⟧'))) (Preadditive.leftComp (∐ X) T.mor₃)
    (Preadditive.leftComp (∐ X) T.mor₂) (Preadditive.leftComp (∐ X) T.mor₁)
    (directSumToHom _ X) (directSumToHom _ X) (directSumToHom _ X) (directSumToHom _ X)
    (directSumToHom _ X) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ((h₂.shift 1).bijective_directSumToHom X).2 ((h₁.shift 1).bijective_directSumToHom X)
    (h₂.bijective_directSumToHom X) (h₁.bijective_directSumToHom X).1
  · refine AddMonoidHom.ext fun x ↦ ?_
    exact (directSumToHom_precomp X _ x).symm
  · refine AddMonoidHom.ext fun x ↦ ?_
    exact (directSumToHom_precomp X _ x).symm
  · refine AddMonoidHom.ext fun x ↦ ?_
    exact (directSumToHom_precomp X _ x).symm
  · refine AddMonoidHom.ext fun x ↦ ?_
    exact (directSumToHom_precomp X _ x).symm
  · exact fun x ↦ directSumPrecomp_exact X T.mor₃ (-(T.mor₁⟦(1 : ℤ)⟧'))
      (by simp [comp_distTriang_mor_zero₃₁ T hT])
      (fun i b hb ↦ Triangle.yoneda_exact₃ _ (rot_of_distTriang T hT) b hb) x
  · exact fun x ↦ directSumPrecomp_exact X T.mor₂ T.mor₃ (comp_distTriang_mor_zero₂₃ T hT)
      (fun i b hb ↦ Triangle.yoneda_exact₃ T hT b hb) x
  · exact fun x ↦ directSumPrecomp_exact X T.mor₁ T.mor₂ (comp_distTriang_mor_zero₁₂ T hT)
      (fun i b hb ↦ Triangle.yoneda_exact₂ T hT b hb) x
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang T hT) x hx
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, rfl⟩
      simp [Preadditive.leftComp, comp_distTriang_mor_zero₃₁_assoc T hT]
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Triangle.yoneda_exact₃ T hT x hx
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, rfl⟩
      simp [Preadditive.leftComp, comp_distTriang_mor_zero₂₃_assoc T hT]
  · intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ T hT x hx
      exact ⟨y, hy.symm⟩
    · rintro ⟨y, rfl⟩
      simp [Preadditive.leftComp, comp_distTriang_mor_zero₁₂_assoc T hT]

instance ObjectProperty.compactObjects.containsZero :
    (ObjectProperty.compactObjects.{0} (C := C)).ContainsZero :=
  ⟨⟨0, isZero_zero C, IsCompactObject.of_isZero (isZero_zero C)⟩⟩

instance ObjectProperty.compactObjects.isStableUnderShift :
    (ObjectProperty.compactObjects.{0} (C := C)).IsStableUnderShift ℤ where
  isStableUnderShiftBy n := ⟨fun _ hK ↦ hK.shift n⟩

instance ObjectProperty.compactObjects.isTriangulatedClosed₃ :
    (ObjectProperty.compactObjects.{0} (C := C)).IsTriangulatedClosed₃ where
  ext₃' T hT h₁ h₂ :=
    ObjectProperty.le_isoClosure _ _ (IsCompactObject.of_distTriang₃ T hT h₁ h₂)

instance ObjectProperty.compactObjects.isTriangulatedClosed₂ :
    (ObjectProperty.compactObjects.{0} (C := C)).IsTriangulatedClosed₂ :=
  ObjectProperty.IsTriangulatedClosed₂.of_isTriangulatedClosed₃

/-- **Compact objects form a triangulated subcategory.** -/
instance ObjectProperty.compactObjects.isTriangulated :
    (ObjectProperty.compactObjects.{0} (C := C)).IsTriangulated := {}

/-- **The triangulated envelope of compact objects is compact.** -/
theorem ObjectProperty.triangEnvelope_le_compactObjects
    {P : ObjectProperty C} (hP : P ≤ ObjectProperty.compactObjects.{0}) :
    P.triangEnvelope ≤ ObjectProperty.compactObjects.{0} :=
  (ObjectProperty.triangEnvelope_le_iff P).2 hP

end Pretriangulated

end CategoryTheory
