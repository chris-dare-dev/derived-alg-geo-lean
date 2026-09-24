/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineLocalizationPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatPullback

/-!
# Affine localization and K-flat pullback comparison

For a flat affine map, the supplied K-flat derived pullback agrees with exact
pullback of all module sheaves, and hence with derived extension of scalars
after affine sheafification. The localization specialization compares this
with the affine localization functor. These ambient derived-category
comparisons assert neither bounded-coherent descent nor arrow extension in a
chosen t-heart.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

noncomputable section

universe u

/-- The affine spectrum map as a morphism to the identity base change. -/
def specMapToBase {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (Over.mk (Spec.map f) : SchemeBaseChange (Spec R)) ⟶
      (Over.mk (𝟙 (Spec R)) : SchemeBaseChange (Spec R)) :=
  Over.homMk (Spec.map f) (Category.comp_id _)

/-- Flatness of the ring map gives flatness of its spectrum base change. -/
theorem specMapToBase_flat_of_ringFlat
    {R A : CommRingCat.{u}} (f : R ⟶ A) (hf : f.hom.Flat) :
    Flat (specMapToBase f).left := by
  change Flat (Spec.map f)
  exact Flat.SpecMap_iff.mpr hf

/-- Flat affine pullback of all module sheaves preserves finite limits. -/
theorem specMapPullback_preservesFiniteLimits_of_flat
    {R A : CommRingCat.{u}} (f : R ⟶ A) (hf : f.hom.Flat) :
    PreservesFiniteLimits (Scheme.Modules.pullback (Spec.map f)) := by
  letI : Flat (specMapToBase f).left := specMapToBase_flat_of_ringFlat f hf
  change PreservesFiniteLimits (modulePullback (specMapToBase f))
  exact modulePullback_preservesFiniteLimits_of_flat (specMapToBase f)

/-- A supplied K-flat resolution computes the exact pullback along a flat
affine map, compatibly with extension of scalars and affine sheafification.
This is an ambient all-module-sheaf statement. -/
def kFlatAffineExactSchemeModuleComparison
    {R A : CommRingCat.{u}} (f : R ⟶ A)
    [Flat (specMapToBase f).left]
    [PreservesFiniteLimits (ModuleCat.extendScalars f.hom)]
    [PreservesFiniteLimits (Scheme.Modules.pullback (Spec.map f))]
    (K : SchemeKFlatResolution (Spec R)) :
    (tilde.functor R).mapDerivedCategory ⋙
        (kFlatLeftDerivedPullback K (specMapToBase f)
          (kFlatPullbackAcyclic_ofFlat K (specMapToBase f))).functor ≅
      (ModuleCat.extendScalars f.hom).mapDerivedCategory ⋙
        (tilde.functor A).mapDerivedCategory := by
  exact Functor.isoWhiskerLeft (tilde.functor R).mapDerivedCategory
    (kFlatFlatPullbackComparison K (specMapToBase f)) ≪≫
      Dqc.affineSchemeModuleExactDerivedPullbackComparison f

private instance tilde_additive_of_commRing
    {R : Type u} [CommRing R] :
    (tilde.functor (CommRingCat.of R)).Additive :=
  AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecOfFunctor

private instance tilde_preservesFiniteLimits_of_commRing
    {R : Type u} [CommRing R] :
    PreservesFiniteLimits (tilde.functor (CommRingCat.of R)) :=
  AlgebraicGeometry.tilde_preservesFiniteLimits

private instance tilde_isLeftAdjoint_of_commRing
    {R : Type u} [CommRing R] :
    (tilde.functor (CommRingCat.of R)).IsLeftAdjoint :=
  (AlgebraicGeometry.tilde.adjunction (R := CommRingCat.of R)).isLeftAdjoint

/-- For a localization, the K-flat affine pullback and derived localization
agree after affine sheafification, given an explicitly supplied K-flat
resolution. The explicit flatness and finite-limit instances follow from
`specMapToBase_flat_of_ringFlat` and
`specMapPullback_preservesFiniteLimits_of_flat` using
`Dqc.affineLocalizationAlgebraMap_flat`. No bounded-coherent or heart
comparison is inferred. -/
def kFlatAffineLocalizationComparison
    {R A : Type u} [CommRing R] [CommRing A]
    (M : Submonoid R) [Algebra R A] [IsLocalization M A]
    [Flat (specMapToBase (CommRingCat.ofHom (algebraMap R A))).left]
    [PreservesFiniteLimits
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A))))]
    (K : SchemeKFlatResolution (Spec (CommRingCat.of R))) :
    (tilde.functor (CommRingCat.of R)).mapDerivedCategory ⋙
        (kFlatLeftDerivedPullback K
          (specMapToBase (CommRingCat.ofHom (algebraMap R A)))
          (kFlatPullbackAcyclic_ofFlat K
            (specMapToBase (CommRingCat.ofHom (algebraMap R A))))).functor ≅
      Dqc.affineLocalizationDerivedPullback M ⋙
        (tilde.functor (CommRingCat.of A)).mapDerivedCategory := by
  let f : CommRingCat.of R ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (algebraMap R A)
  letI : PreservesFiniteLimits (ModuleCat.extendScalars f.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (Dqc.affineLocalizationAlgebraMap_flat M)
  exact kFlatAffineExactSchemeModuleComparison f K ≪≫
    Functor.isoWhiskerRight
      (Dqc.affineLocalizationDerivedPullbackComparison M).symm
      (tilde.functor (CommRingCat.of A)).mapDerivedCategory

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
