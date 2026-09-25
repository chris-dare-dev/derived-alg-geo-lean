/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLocalization

/-!
# Source naturality of derived-category Hom localization

The degreewise-localization map on derived-category Hom-sets commutes with
precomposition by an arbitrary cochain map. No K-projectivity or boundedness
is needed for this naturality square. It is shared by the degree-zero and
bounded-complex finite-module localization theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R] (S : Submonoid R)

private abbrev sourceDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

private abbrev targetDerivedCategory : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _

attribute [local instance] sourceDerivedCategory targetDerivedCategory

/-- Degreewise localization of derived-category Hom-sets commutes with
precomposition by a cochain map. The source change on the localized side is
the image of that map under degreewise localization. -/
theorem derivedHomLocalizedMap_precomp
    (X Y Q : CochainComplex (ModuleCat.{u} R) ℤ) (f : X ⟶ Y)
    (g : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj Y) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) :
    derivedHomLocalizedMap S X Q
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f) ≫ g) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).map f)) ≫
        derivedHomLocalizedMap S Y Q g := by
  let F := ModuleCat.localizedModuleFunctor.{u} S
  have hnat :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((F.mapHomologicalComplex (.up ℤ)).map f)) ≫
        (derivedLocalizationComparison S Y).inv =
      (derivedLocalizationComparison S X).inv ≫
        F.mapDerivedCategory.map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f)) := by
    simpa only [derivedLocalizationComparison, Iso.app_inv, Functor.comp_map,
      Functor.mapHomotopyCategory_map] using
      (F.mapDerivedCategoryFactorsh).inv.naturality
        ((HomotopyCategory.quotient _ (.up ℤ)).map f)
  change (derivedLocalizationComparison S X).inv ≫
      F.mapDerivedCategory.map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map f) ≫ g) ≫
      (derivedLocalizationComparison S Q).hom =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((F.mapHomologicalComplex (.up ℤ)).map f)) ≫
      (derivedLocalizationComparison S Y).inv ≫
        F.mapDerivedCategory.map g ≫ (derivedLocalizationComparison S Q).hom
  rw [Functor.map_comp]
  simp only [← Category.assoc]
  rw [← hnat]

end

end CochainComplex.HomComplex
