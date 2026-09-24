/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory

/-! Axiom audit and direct fixed-target client for categorical denominator clearing. -/

#print axioms CategoryTheory.Subobject.fixedTargetArrowExtension_of_localizedHom

noncomputable section CategoricalDenominatorClient

open CategoryTheory

universe w v₁ v₂ u₁ u₂

variable (R : Type w) [CommRing R] (S : Submonoid R)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C)

example
    (hObj : ∀ Z : D, ∃ Y : C, Nonempty (Z ≅ F.obj Y))
    (hHom : ∀ Y : C, IsLocalizedModule S (F.mapLinearMap R (X := Y) (Y := X)))
    (hIso : ∀ (Y : C) (s : S), IsIso ((s : R) • 𝟙 (F.obj Y)))
    {Z : D} (β : Z ⟶ F.obj X) :
    ∃ (Y : C) (f : Y ⟶ X) (e : Z ≅ F.obj Y), β = e.hom ≫ F.map f :=
  (Subobject.fixedTargetArrowExtension_of_localizedHom R S F X hObj hHom hIso) β

end CategoricalDenominatorClient
