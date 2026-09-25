/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Affine.Localization
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.AffineLocalizationKFlatComparison
import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.Algebra.Category.FGModuleCat.Colimits

/-!
# Exact affine coherent localization comparison

On noetherian affine schemes, localization is flat, so coherent pullback and
finite-module extension of scalars are exact. This file derives the ordinary
affine sheafification/pullback natural isomorphism and records its naturality.
It does not assert localization of derived Hom groups, bounded-component
compatibility, or descent in a chosen heart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

noncomputable section

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

universe u

/-- Exact derived affine sheafification on finitely generated modules over a
noetherian ring. -/
def finiteAffineTildeDerived (B : CommRingCat.{u}) [IsNoetherianRing B] :
    _root_.DerivedCategory (FGModuleCat.{u} B) ⥤
      _root_.DerivedCategory (Coh (Spec B)) := by
  let F := FGModuleCat.affineTilde (R := B)
  haveI : PreservesFiniteLimits F := by
    change PreservesFiniteLimits (Coh.affineEquivalence (R := B)).inverse
    infer_instance
  haveI : PreservesFiniteColimits F := by
    change PreservesFiniteColimits (Coh.affineEquivalence (R := B)).inverse
    infer_instance
  haveI : F.Additive := Functor.additive_of_preserves_binary_products F
  exact F.mapDerivedCategory

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [IsNoetherianRing R]

private abbrev f : CommRingCat.of R ⟶ CommRingCat.of A :=
  CommRingCat.ofHom (algebraMap R A)

/-- Exact derived coherent pullback along an affine localization. The target
ring is noetherian because it is a localization of the noetherian source. -/
def coherentLocalizationDerivedPullback
    (S : Submonoid R) [IsLocalization S A] :
    letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
    _root_.DerivedCategory (Coh (Spec (CommRingCat.of R))) ⥤
      _root_.DerivedCategory (Coh (Spec (CommRingCat.of A))) := by
  letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
  let F := Coh.pullback (Spec.map (f (R := R) (A := A)))
  letI : PreservesFiniteLimits (Scheme.Modules.pullback
      (Spec.map (f (R := R) (A := A)))) :=
    specMapPullback_preservesFiniteLimits_of_flat (f (R := R) (A := A))
      (Dqc.affineLocalizationAlgebraMap_flat S)
  haveI : PreservesFiniteLimits F := inferInstance
  haveI : PreservesFiniteColimits F := inferInstance
  haveI : F.Additive := inferInstance
  exact F.mapDerivedCategory

/-- Exact derived extension of scalars on finite modules along an affine
localization. Finite terms remain finite under base change. -/
def finiteExtendScalarsDerived
    (S : Submonoid R) [IsLocalization S A] :
    letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
    _root_.DerivedCategory (FGModuleCat.{u} R) ⥤
      _root_.DerivedCategory (FGModuleCat.{u} A) := by
  letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
  let G := Coh.finiteExtendScalars (R := R) (A := A)
  let ιR := (ModuleCat.isFG R).ι
  let ιA := (ModuleCat.isFG A).ι
  let T := ModuleCat.extendScalars (algebraMap R A)
  haveI : PreservesFiniteLimits ιR := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat R) (ModuleCat.{u} R))
    infer_instance
  haveI : PreservesFiniteColimits ιR := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat R) (ModuleCat.{u} R))
    infer_instance
  haveI : PreservesFiniteLimits ιA := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat A) (ModuleCat.{u} A))
    infer_instance
  haveI : PreservesFiniteColimits ιA := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat A) (ModuleCat.{u} A))
    infer_instance
  haveI : PreservesFiniteLimits T :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (Dqc.affineLocalizationAlgebraMap_flat S)
  haveI : PreservesFiniteColimits T := inferInstance
  haveI : PreservesFiniteLimits G := by
    haveI : PreservesFiniteLimits (G ⋙ ιA) := by
      change PreservesFiniteLimits (ιR ⋙ T)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves G ιA
  haveI : PreservesFiniteColimits G := by
    haveI : PreservesFiniteColimits (G ⋙ ιA) := by
      change PreservesFiniteColimits (ιR ⋙ T)
      infer_instance
    exact preservesFiniteColimits_of_reflects_of_preserves G ιA
  haveI : G.Additive := Functor.additive_of_preserves_binary_products G
  exact G.mapDerivedCategory

/-- Derived affine sheafification identifies finite-module localization with
coherent derived pullback. The isomorphism is natural in the derived finite
module complex. -/
def affineCoherentLocalizationDerivedComparison
    (S : Submonoid R) [IsLocalization S A] :
    letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
    finiteAffineTildeDerived (CommRingCat.of R) ⋙
        coherentLocalizationDerivedPullback (R := R) (A := A) S ≅
      finiteExtendScalarsDerived (R := R) (A := A) S ⋙
        finiteAffineTildeDerived (CommRingCat.of A) := by
  letI : IsNoetherianRing A := IsLocalization.isNoetherianRing S A inferInstance
  let FR := FGModuleCat.affineTilde (R := CommRingCat.of R)
  let FA := FGModuleCat.affineTilde (R := CommRingCat.of A)
  let F := Coh.pullback (Spec.map (f (R := R) (A := A)))
  let G := Coh.finiteExtendScalars (R := R) (A := A)
  let ιR := (ModuleCat.isFG R).ι
  let ιA := (ModuleCat.isFG A).ι
  let T := ModuleCat.extendScalars (algebraMap R A)
  letI : PreservesFiniteLimits (Scheme.Modules.pullback
      (Spec.map (f (R := R) (A := A)))) :=
    specMapPullback_preservesFiniteLimits_of_flat (f (R := R) (A := A))
      (Dqc.affineLocalizationAlgebraMap_flat S)
  haveI : PreservesFiniteLimits F := inferInstance
  haveI : PreservesFiniteColimits F := inferInstance
  haveI : PreservesFiniteLimits FR := by
    change PreservesFiniteLimits (Coh.affineEquivalence (R := CommRingCat.of R)).inverse
    infer_instance
  haveI : PreservesFiniteColimits FR := by
    change PreservesFiniteColimits (Coh.affineEquivalence (R := CommRingCat.of R)).inverse
    infer_instance
  haveI : PreservesFiniteLimits FA := by
    change PreservesFiniteLimits (Coh.affineEquivalence (R := CommRingCat.of A)).inverse
    infer_instance
  haveI : PreservesFiniteColimits FA := by
    change PreservesFiniteColimits (Coh.affineEquivalence (R := CommRingCat.of A)).inverse
    infer_instance
  haveI : PreservesFiniteLimits ιR := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat R) (ModuleCat.{u} R))
    infer_instance
  haveI : PreservesFiniteColimits ιR := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat R) (ModuleCat.{u} R))
    infer_instance
  haveI : PreservesFiniteLimits ιA := by
    change PreservesFiniteLimits (forget₂ (FGModuleCat A) (ModuleCat.{u} A))
    infer_instance
  haveI : PreservesFiniteColimits ιA := by
    change PreservesFiniteColimits (forget₂ (FGModuleCat A) (ModuleCat.{u} A))
    infer_instance
  haveI : PreservesFiniteLimits T :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (Dqc.affineLocalizationAlgebraMap_flat S)
  haveI : PreservesFiniteColimits T := inferInstance
  haveI : PreservesFiniteLimits G := by
    haveI : PreservesFiniteLimits (G ⋙ ιA) := by
      change PreservesFiniteLimits (ιR ⋙ T)
      infer_instance
    exact preservesFiniteLimits_of_reflects_of_preserves G ιA
  haveI : PreservesFiniteColimits G := by
    haveI : PreservesFiniteColimits (G ⋙ ιA) := by
      change PreservesFiniteColimits (ιR ⋙ T)
      infer_instance
    exact preservesFiniteColimits_of_reflects_of_preserves G ιA
  haveI : FR.Additive := Functor.additive_of_preserves_binary_products FR
  haveI : FA.Additive := Functor.additive_of_preserves_binary_products FA
  haveI : F.Additive := inferInstance
  haveI : G.Additive := Functor.additive_of_preserves_binary_products G
  haveI : (FR ⋙ F).Additive := inferInstance
  haveI : (G ⋙ FA).Additive := inferInstance
  haveI : PreservesFiniteLimits (FR ⋙ F) := inferInstance
  haveI : PreservesFiniteColimits (FR ⋙ F) := inferInstance
  haveI : PreservesFiniteLimits (G ⋙ FA) := inferInstance
  haveI : PreservesFiniteColimits (G ⋙ FA) := inferInstance
  exact Functor.mapDerivedCategoryCompIso (Iso.refl (FR ⋙ F)) ≪≫
    NatIso.mapDerivedCategory (Coh.affineTildePullbackIso (R := R) (A := A)) ≪≫
      (Functor.mapDerivedCategoryCompIso (Iso.refl (G ⋙ FA))).symm

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
