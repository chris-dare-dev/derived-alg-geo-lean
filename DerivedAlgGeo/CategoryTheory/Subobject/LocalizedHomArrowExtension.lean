/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SubobjectEquivalence
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Fixed-target arrow extension by categorical denominator clearing

Suppose an `R`-linear functor has lifts of target objects, its map on Homs into a fixed
object is a localization, and each denominator acts invertibly on the image of a lifted
source object. A fraction representing a target arrow can then be cleared by changing
the *source isomorphism*. No full faithfulness, exactness, or geometric localization is
asserted here.
-/

universe w v₁ v₂ u₁ u₂

open CategoryTheory.Limits

namespace CategoryTheory.Subobject

variable (R : Type w) [CommRing R] (S : Submonoid R)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
  (F : C ⥤ D) [F.Additive] [F.Linear R] (X : C)

/-- Clear a denominator in a morphism into `F.obj X` by absorbing its action into
the isomorphism from a target source object to the image of a source object.
Only the Hom-localization maps with fixed codomain `X` are needed. -/
theorem fixedTargetArrowExtension_of_localizedHom
    (hObj : ∀ Z : D, ∃ Y : C, Nonempty (Z ≅ F.obj Y))
    (hHom : ∀ Y : C, IsLocalizedModule S (F.mapLinearMap R (X := Y) (Y := X)))
    (hIso : ∀ (Y : C) (s : S), IsIso ((s : R) • 𝟙 (F.obj Y))) :
    FixedTargetArrowExtension F X := by
  intro Z β
  obtain ⟨Y, ⟨e⟩⟩ := hObj Z
  let γ : F.obj Y ⟶ F.obj X := e.inv ≫ β
  letI : IsLocalizedModule S (F.mapLinearMap R (X := Y) (Y := X)) := hHom Y
  obtain ⟨⟨f, s⟩, hs⟩ := IsLocalizedModule.surj S (F.mapLinearMap R) γ
  letI : IsIso ((s : R) • 𝟙 (F.obj Y)) := hIso Y s
  let a : F.obj Y ≅ F.obj Y := asIso ((s : R) • 𝟙 (F.obj Y))
  have hs' : (s : R) • γ = F.map f := by
    change (s : R) • γ = (F.mapLinearMap R) f at hs
    rw [F.coe_mapLinearMap R] at hs
    exact hs
  have hγ : a.hom ≫ γ = F.map f := by
    simpa only [a, asIso_hom, Linear.smul_comp, Category.id_comp] using hs'
  refine ⟨Y, f, e ≪≫ a.symm, ?_⟩
  calc
    β = e.hom ≫ γ := by simp [γ]
    _ = e.hom ≫ (a.inv ≫ F.map f) := by rw [← hγ]; simp
    _ = (e ≪≫ a.symm).hom ≫ F.map f := by simp [Category.assoc]

end CategoryTheory.Subobject
