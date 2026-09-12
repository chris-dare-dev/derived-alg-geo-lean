/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Heart
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced

/-!
# The standard heart of the bounded derived category

The canonical t-structure on `DerivedCategory C` restricts to its bounded
subcategory.  This file identifies the heart of that restricted t-structure
with `C`, by lifting `singleFunctor C 0` through the bounded inclusion.

This is deliberately separate from `Heart.lean`: the latter concerns the
unbounded derived category, while stability conditions for varieties are
carried by `Dᵇ(Coh X)`.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated

namespace DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- `singleFunctor C 0`, lifted to the bounded derived category. -/
noncomputable def boundedSingleFunctor : C ⥤ Bounded C :=
  (TStructure.t (C := C)).bounded.lift (singleFunctor C 0) fun _ =>
    ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩

instance boundedSingleFunctor_additive : (boundedSingleFunctor C).Additive := by
  dsimp [boundedSingleFunctor]
  infer_instance

instance boundedSingleFunctor_full : (boundedSingleFunctor C).Full := by
  dsimp [boundedSingleFunctor]
  infer_instance

instance boundedSingleFunctor_faithful : (boundedSingleFunctor C).Faithful := by
  dsimp [boundedSingleFunctor]
  infer_instance

@[simp]
theorem boundedSingleFunctor_obj_obj (X : C) :
    ((boundedSingleFunctor C).obj X).obj = (singleFunctor C 0).obj X := rfl

/-- An object in the image of `boundedSingleFunctor` lies in the standard
heart of the bounded derived category. -/
theorem boundedHeart_singleFunctor_obj (X : C) :
    (TStructure.t (C := C)).onBounded.heart ((boundedSingleFunctor C).obj X) := by
  rw [TStructure.mem_heart_iff]
  have h := heart_singleFunctor_obj C X
  rw [TStructure.mem_heart_iff] at h
  constructor
  · rw [ObjectProperty.tStructure_isLE_iff
      (TStructure.t (C := C)).bounded (TStructure.t (C := C))]
    simpa using h.1
  · rw [ObjectProperty.tStructure_isGE_iff
      (TStructure.t (C := C)).bounded (TStructure.t (C := C))]
    simpa using h.2

/-- The essential image of `boundedSingleFunctor C` is exactly the standard
heart of `DerivedCategory.Bounded C`. -/
theorem essImage_boundedSingleFunctor_eq_boundedHeart :
    (boundedSingleFunctor C).essImage =
      (TStructure.t (C := C)).onBounded.heart := by
  ext X
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    exact (TStructure.t (C := C)).onBounded.heart.prop_of_iso e
      (boundedHeart_singleFunctor_obj C Y)
  · intro hX
    rw [TStructure.mem_heart_iff] at hX
    obtain ⟨hle, hge⟩ := hX
    have hle' : (TStructure.t (C := C)).IsLE X.obj 0 :=
      (ObjectProperty.tStructure_isLE_iff (TStructure.t (C := C)).bounded
        (TStructure.t (C := C)) X 0).mp hle
    have hge' : (TStructure.t (C := C)).IsGE X.obj 0 :=
      (ObjectProperty.tStructure_isGE_iff (TStructure.t (C := C)).bounded
        (TStructure.t (C := C)) X 0).mp hge
    letI := hle'
    letI := hge'
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE X.obj 0
    exact ⟨Y, ⟨Bounded.ι.preimageIso e.symm⟩⟩

/-- The original abelian category is the heart of the induced standard
t-structure on its bounded derived category. -/
noncomputable instance isBoundedHeart :
    (TStructure.t (C := C)).onBounded.Heart C where
  ι := boundedSingleFunctor C
  essImage_eq_heart := essImage_boundedSingleFunctor_eq_boundedHeart C

section Equivalence

/-- `C` lifted to the full subcategory underlying the bounded standard heart. -/
noncomputable def toBoundedHeart :
    C ⥤ (TStructure.t (C := C)).onBounded.heart.FullSubcategory :=
  ObjectProperty.lift _ (boundedSingleFunctor C) (boundedHeart_singleFunctor_obj C)

@[simp]
theorem toBoundedHeart_comp_ι :
    toBoundedHeart C ⋙ (TStructure.t (C := C)).onBounded.heart.ι =
      boundedSingleFunctor C := rfl

instance toBoundedHeart_full : (toBoundedHeart C).Full := by
  dsimp [toBoundedHeart]
  infer_instance

instance toBoundedHeart_faithful : (toBoundedHeart C).Faithful := by
  dsimp [toBoundedHeart]
  infer_instance

instance toBoundedHeart_essSurj : (toBoundedHeart C).EssSurj where
  mem_essImage := by
    rintro ⟨X, hX⟩
    rw [TStructure.mem_heart_iff] at hX
    obtain ⟨hle, hge⟩ := hX
    have hle' : (TStructure.t (C := C)).IsLE X.obj 0 :=
      (ObjectProperty.tStructure_isLE_iff (TStructure.t (C := C)).bounded
        (TStructure.t (C := C)) X 0).mp hle
    have hge' : (TStructure.t (C := C)).IsGE X.obj 0 :=
      (ObjectProperty.tStructure_isGE_iff (TStructure.t (C := C)).bounded
        (TStructure.t (C := C)) X 0).mp hge
    letI := hle'
    letI := hge'
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE X.obj 0
    exact ⟨Y, ⟨((TStructure.t (C := C)).onBounded.heart.ι).preimageIso
      (Bounded.ι.preimageIso e.symm)⟩⟩

instance toBoundedHeart_isEquivalence : (toBoundedHeart C).IsEquivalence where

/-- The equivalence from `C` to the standard heart of `Dᵇ(C)`. -/
noncomputable def boundedHeartEquivalence :
    C ≌ (TStructure.t (C := C)).onBounded.heart.FullSubcategory :=
  (toBoundedHeart C).asEquivalence

@[simp]
theorem boundedHeartEquivalence_functor :
    (boundedHeartEquivalence C).functor = toBoundedHeart C := rfl

@[simp]
theorem toBoundedHeart_obj_obj_obj (X : C) :
    (((toBoundedHeart C).obj X).obj).obj = (singleFunctor C 0).obj X := rfl

end Equivalence

end DerivedCategory
