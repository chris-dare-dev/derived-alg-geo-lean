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
    MonoidalPreadditive (PresheafOfModulesOfCommRing R) where
  whiskerLeft_zero := by
    intro A B C
    ext1 U
    exact MonoidalPreadditive.whiskerLeft_zero (C := ModuleCat (R.obj U))
  zero_whiskerRight := by
    intro A B C
    ext1 U
    exact MonoidalPreadditive.zero_whiskerRight (C := ModuleCat (R.obj U))
  whiskerLeft_add := by
    intro A B C f g
    ext1 U
    exact MonoidalPreadditive.whiskerLeft_add (C := ModuleCat (R.obj U)) (f.app U) (g.app U)
  add_whiskerRight := by
    intro A B C f g
    ext1 U
    exact MonoidalPreadditive.add_whiskerRight (C := ModuleCat (R.obj U)) (f.app U) (g.app U)

end PresheafOfModules
