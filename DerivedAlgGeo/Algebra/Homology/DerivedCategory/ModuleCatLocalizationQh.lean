/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ModuleCatLocalization

/-!
# The derived module-localization comparison on displayed complexes

The exact derived natural isomorphism between scalar extension and canonical
module localization agrees with the degreewise comparison after passage through
the homotopy and derived quotients. No Hom-set localization or geometric
pullback result is asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

noncomputable section

namespace ModuleCat

universe u

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- The `Qh` factorization of exact derived scalar extension on a displayed
cochain complex. The required exactness and additivity instances are local. -/
def extendScalarsLocalizationDerivedFactorsh
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extendScalarsLocalizationDerived S).obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≅
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
      (((ModuleCat.extendScalars (algebraMap R (Localization S))).mapHomologicalComplex
        (.up ℤ)).obj K)) := by
  let T := ModuleCat.extendScalars (algebraMap R (Localization S))
  have hflat : (algebraMap R (Localization S)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S)
  haveI : PreservesFiniteLimits T :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits T := inferInstance
  haveI : T.Additive := Functor.additive_of_preserves_binary_products T
  change T.mapDerivedCategory.obj
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≅
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((T.mapHomologicalComplex (.up ℤ)).obj K))
  exact T.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient _ (.up ℤ)).obj K)

/-- On a displayed complex, the `Qh` factorization reduces to the `Q`
factorization. The quotient comparisons are identity morphisms at this object. -/
private theorem mapDerivedCategoryFactorsh_hom_app_eq
    {A : Type u} [CommRing A] (F : ModuleCat.{u} R ⥤ ModuleCat.{u} A)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  dsimp [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors]
  change F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj K)) ≫
    F.mapDerivedCategoryFactors.hom.app K ≫
    𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) ≫
    DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K))) = _
  simp
  let Z := (HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj
    ((F.mapHomologicalComplex (.up ℤ)).obj K)
  have hQh : DerivedCategory.Qh.map (𝟙 Z) = 𝟙 _ :=
    DerivedCategory.Qh.map_id Z
  rw [hQh]
  change F.mapDerivedCategoryFactors.hom.app K ≫
      𝟙 ((F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q).obj K) =
    F.mapDerivedCategoryFactors.hom.app K
  exact Category.comp_id _

private def extendScalarsLocalizationDerivedFactors
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extendScalarsLocalizationDerived S).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj
        (((ModuleCat.extendScalars (algebraMap R (Localization S))).mapHomologicalComplex
          (.up ℤ)).obj K) := by
  let T := ModuleCat.extendScalars (algebraMap R (Localization S))
  have hflat : (algebraMap R (Localization S)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S)
  haveI : PreservesFiniteLimits T :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits T := inferInstance
  haveI : T.Additive := Functor.additive_of_preserves_binary_products T
  change T.mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅
    DerivedCategory.Q.obj ((T.mapHomologicalComplex (.up ℤ)).obj K)
  exact T.mapDerivedCategoryFactors.app K

private theorem extendScalarsLocalizationDerivedNatIso_Q
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extendScalarsLocalizationDerivedNatIso S).hom.app (DerivedCategory.Q.obj K) ≫
        (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategoryFactors.hom.app K =
      (extendScalarsLocalizationDerivedFactors S K).hom ≫
        DerivedCategory.Q.map ((extendScalarsLocalizationCochainNatIso S).hom.app K) := by
  let T := ModuleCat.extendScalars (algebraMap R (Localization S))
  have hflat : (algebraMap R (Localization S)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S)
  haveI : PreservesFiniteLimits T :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits T := inferInstance
  haveI : T.Additive := Functor.additive_of_preserves_binary_products T
  change (NatIso.mapDerivedCategory (extendScalarsLocalizationNatIso S)).hom.app
        (DerivedCategory.Q.obj K) ≫
        (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategoryFactors.hom.app K =
      T.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((extendScalarsLocalizationCochainNatIso S).hom.app K)
  simp only [NatIso.mapDerivedCategory, Localization.liftNatIso_hom,
    Localization.liftNatTrans_app]
  change (T.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((extendScalarsLocalizationCochainNatIso S).hom.app K) ≫
      (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategoryFactors.inv.app K) ≫
      (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategoryFactors.hom.app K = _
  let i := (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategoryFactors.app K
  change (T.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((extendScalarsLocalizationCochainNatIso S).hom.app K) ≫
        i.inv) ≫ i.hom = _
  cat_disch

/-- The derived scalar-extension/localization isomorphism agrees on a displayed
complex with the degreewise cochain comparison after `Qh` and the canonical
derived-functor factorizations. This has no boundedness or finiteness premise. -/
theorem extendScalarsLocalizationDerivedNatIso_Qh
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (extendScalarsLocalizationDerivedNatIso S).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
      (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
    (extendScalarsLocalizationDerivedFactorsh S K).hom ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((extendScalarsLocalizationCochainNatIso S).hom.app K)) := by
  let T := ModuleCat.extendScalars (algebraMap R (Localization S))
  have hflat : (algebraMap R (Localization S)).Flat :=
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization S) S)
  haveI : PreservesFiniteLimits T :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits T := inferInstance
  haveI : T.Additive := Functor.additive_of_preserves_binary_products T
  change (NatIso.mapDerivedCategory (extendScalarsLocalizationNatIso S)).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) ≫
      (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) =
    T.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((extendScalarsLocalizationCochainNatIso S).hom.app K))
  rw [mapDerivedCategoryFactorsh_hom_app_eq
      (ModuleCat.localizedModuleFunctor.{u} S) K,
    mapDerivedCategoryFactorsh_hom_app_eq T K]
  exact extendScalarsLocalizationDerivedNatIso_Q S K

end ModuleCat

end
