/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Additivity of tensor products of module presheaves

The objectwise tensor product makes presheaves of modules monoidal preadditive. This is the
pointwise lift of the corresponding instance for `ModuleCat`.
-/

open CategoryTheory

universe v u

namespace PresheafOfModules

noncomputable instance monoidalPreadditive {C : Type v} [Category C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    MonoidalPreadditive (PresheafOfModules (R ⋙ forget₂ _ _)) where
  whiskerLeft_zero := by
    intro A B C
    ext U x
    change (MonoidalCategory.whiskerLeft
      (C := ModuleCat ((R ⋙ forget₂ _ RingCat).obj U)) (A.obj U)
        (0 : B.obj U ⟶ C.obj U)).hom x = 0
    simp
  zero_whiskerRight := by
    intro A B C
    ext U x
    change (MonoidalCategory.whiskerRight
      (C := ModuleCat ((R ⋙ forget₂ _ RingCat).obj U))
        (0 : B.obj U ⟶ C.obj U) (A.obj U)).hom x = 0
    simp
  whiskerLeft_add := by
    intro A B C f g
    ext U x
    change (MonoidalCategory.whiskerLeft
      (C := ModuleCat ((R ⋙ forget₂ _ RingCat).obj U)) (A.obj U)
        (f.app U + g.app U)).hom x =
      (MonoidalCategory.whiskerLeft
        (C := ModuleCat ((R ⋙ forget₂ _ RingCat).obj U)) (A.obj U) (f.app U)).hom x +
      (MonoidalCategory.whiskerLeft
        (C := ModuleCat ((R ⋙ forget₂ _ RingCat).obj U)) (A.obj U) (g.app U)).hom x
    simp
  add_whiskerRight := by
    intro A B C f g
    ext U x
    change (MonoidalCategory.whiskerRight
      (C := ModuleCat ((R ⋙ forget₂ _ RingCat).obj U))
        (f.app U + g.app U) (A.obj U)).hom x =
      (MonoidalCategory.whiskerRight
        (C := ModuleCat ((R ⋙ forget₂ _ RingCat).obj U)) (f.app U) (A.obj U)).hom x +
      (MonoidalCategory.whiskerRight
        (C := ModuleCat ((R ⋙ forget₂ _ RingCat).obj U)) (g.app U) (A.obj U)).hom x
    simp

end PresheafOfModules
