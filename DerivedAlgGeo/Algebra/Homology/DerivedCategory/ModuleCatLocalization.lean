/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Localization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Localization

/-!
# Exact derived comparison for canonical module localization

Scalar extension to `Localization S` and `ModuleCat.localizedModuleFunctor S`
are naturally isomorphic exact functors. This file lifts their comparison to
derived categories. It does not identify a geometric pullback or assert
localization of a derived-category Hom group.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

namespace ModuleCat

universe u

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- Exact derived scalar extension to the canonical localization. The
exactness and additivity witnesses remain local to this definition. -/
def extendScalarsLocalizationDerived :
    DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} (Localization S)) := by
  let T := ModuleCat.extendScalars (algebraMap R (Localization S))
  have hflat : (algebraMap R (Localization S)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S)
  haveI : PreservesFiniteLimits T :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits T := inferInstance
  haveI : T.Additive := Functor.additive_of_preserves_binary_products T
  exact T.mapDerivedCategory

/-- Exact derived functor of Mathlib's canonical localized-module functor. -/
def localizedModuleDerived :
    DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} (Localization S)) :=
  (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategory

/-- Derived natural isomorphism induced by the canonical ModuleCat comparison. -/
def extendScalarsLocalizationDerivedNatIso :
    extendScalarsLocalizationDerived S ≅ localizedModuleDerived S := by
  let T := ModuleCat.extendScalars (algebraMap R (Localization S))
  have hflat : (algebraMap R (Localization S)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S)
  haveI : PreservesFiniteLimits T :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits T := inferInstance
  haveI : T.Additive := Functor.additive_of_preserves_binary_products T
  change T.mapDerivedCategory ≅
    (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategory
  exact NatIso.mapDerivedCategory (extendScalarsLocalizationNatIso S)

/-- The comparison commutes with every arrow of the source derived category. -/
theorem extendScalarsLocalizationDerivedNatIso_naturality
    {X Y : DerivedCategory (ModuleCat.{u} R)} (f : X ⟶ Y) :
    (extendScalarsLocalizationDerived S).map f ≫
        (extendScalarsLocalizationDerivedNatIso S).hom.app Y =
      (extendScalarsLocalizationDerivedNatIso S).hom.app X ≫
        (localizedModuleDerived S).map f :=
  (extendScalarsLocalizationDerivedNatIso S).hom.naturality f

end ModuleCat

end
