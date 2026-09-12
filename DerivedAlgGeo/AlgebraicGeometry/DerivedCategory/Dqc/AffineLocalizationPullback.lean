/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Localization.BaseChange
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Transport
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineDerivedEquivalence
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectivePullback

/-!
# Derived pullback along an affine localization

For a localization `R → A`, restriction of scalars followed by extension of
scalars is naturally isomorphic to the identity on `A`-modules.  Flatness of
localizations therefore lets this counit descend to derived categories and
exhibits derived extension of scalars as essentially surjective.

This is the algebraic affine-localization input for the essential-surjectivity
part of the base-change construction.  Identifying this functor with geometric
pullback on affine `Dqc` is a separate comparison step.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pseudofunctor
open scoped ChangeOfRings

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R A : Type u} [CommRing R] [CommRing A]
  (M : Submonoid R) [Algebra R A] [IsLocalization M A]

include M in
/-- For a localization `R → A`, the extension--restriction counit is an
isomorphism on every `A`-module. -/
theorem affineLocalizationExtendRestrictCounitApp_isIso
    (N : ModuleCat.{u} A) :
    IsIso ((ModuleCat.ExtendRestrictScalarsAdj.counit
      (algebraMap R A)).app N) := by
  letI : Module R N := Module.compHom N (algebraMap R A)
  letI : IsScalarTower R A
      ((ModuleCat.restrictScalars (algebraMap R A)).obj
        (ModuleCat.of A A)) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsScalarTower R A
      ((ModuleCat.restrictScalars (algebraMap R A)).obj N) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  letI : TensorProduct.CompatibleSMul R A
      ((ModuleCat.restrictScalars (algebraMap R A)).obj (ModuleCat.of A A))
      ((ModuleCat.restrictScalars (algebraMap R A)).obj N) :=
    IsLocalization.tensorProduct_compatibleSMul M A _ _
  letI : Module A
      ((ModuleCat.restrictScalars (algebraMap R A) ⋙
        ModuleCat.extendScalars (algebraMap R A)).obj N) :=
    ((ModuleCat.restrictScalars (algebraMap R A) ⋙
      ModuleCat.extendScalars (algebraMap R A)).obj N).isModule
  let inverse : N ⟶
      (ModuleCat.restrictScalars (algebraMap R A) ⋙
        ModuleCat.extendScalars (algebraMap R A)).obj N :=
    ModuleCat.ofHom
      { toFun := fun n ↦
          (show (ModuleCat.restrictScalars (algebraMap R A)).obj
              (ModuleCat.of A A) from (1 : A)) ⊗ₜ[R]
            (show (ModuleCat.restrictScalars (algebraMap R A)).obj N from n)
        map_add' := fun x y ↦
          TensorProduct.tmul_add
            (show (ModuleCat.restrictScalars (algebraMap R A)).obj
              (ModuleCat.of A A) from (1 : A))
            (show (ModuleCat.restrictScalars (algebraMap R A)).obj N from x)
            (show (ModuleCat.restrictScalars (algebraMap R A)).obj N from y)
        map_smul' := fun a n ↦ by
          let one : (ModuleCat.restrictScalars (algebraMap R A)).obj
              (ModuleCat.of A A) := (1 : A)
          let n' : (ModuleCat.restrictScalars (algebraMap R A)).obj N := n
          change one ⊗ₜ[R]
              (show (ModuleCat.restrictScalars (algebraMap R A)).obj N
                from a • n) =
            a • (one ⊗ₜ[R] n')
          erw [ModuleCat.ExtendScalars.smul_tmul]
          have ha : a • one =
              (show (ModuleCat.restrictScalars (algebraMap R A)).obj
                (ModuleCat.of A A) from a * (show A from one)) := by
            rfl
          exact (TensorProduct.smul_tmul (R := R) a one n').symm.trans
            (congrArg (fun x :
              (ModuleCat.restrictScalars (algebraMap R A)).obj
                (ModuleCat.of A A) ↦ x ⊗ₜ[R] n') ha) }
  refine ⟨⟨inverse, ?_, ?_⟩⟩
  · apply ModuleCat.ExtendScalars.hom_ext
    intro n
    change inverse
      (ModuleCat.ExtendRestrictScalarsAdj.Counit.map
        (Y := N) (algebraMap R A)
          ((1 : A) ⊗ₜ[R, algebraMap R A] n)) =
      (1 : A) ⊗ₜ[R, algebraMap R A] n
    erw [ModuleCat.ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul]
    rfl
  · ext n
    change ModuleCat.ExtendRestrictScalarsAdj.Counit.map
      (Y := N) (algebraMap R A) (inverse n) = n
    rw [show inverse n =
      (1 : A) ⊗ₜ[R, algebraMap R A] (show N from n) by rfl]
    exact ModuleCat.ExtendRestrictScalarsAdj.Counit.map_apply_one_tmul
      (algebraMap R A) (show N from n)

include M in
/-- The extension--restriction counit for a localization, bundled as a
natural isomorphism of module functors. -/
def affineLocalizationExtendRestrictCounitIso :
    ModuleCat.restrictScalars.{u, u, u} (algebraMap R A) ⋙
        ModuleCat.extendScalars.{u, u, u} (algebraMap R A) ≅
      𝟭 (ModuleCat.{u} A) := by
  letI (N : ModuleCat.{u} A) : IsIso
      ((ModuleCat.ExtendRestrictScalarsAdj.counit
        (algebraMap R A)).app N) :=
    affineLocalizationExtendRestrictCounitApp_isIso M N
  letI : IsIso (ModuleCat.ExtendRestrictScalarsAdj.counit
      (algebraMap R A)) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (ModuleCat.ExtendRestrictScalarsAdj.counit
    (algebraMap R A))

/-- Additivity data for extension of scalars, with universes fixed for the
localization-derived construction. -/
theorem affineLocalizationExtendScalars_additive :
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)).Additive :=
  affineExtendScalars_additive (CommRingCat.ofHom (algebraMap R A))

include M in
/-- Extension of scalars along a localization preserves finite limits. -/
theorem affineLocalizationExtendScalars_preservesFiniteLimits :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A M))

include M in
/-- Exact derived extension of scalars along a localization. -/
def affineLocalizationDerivedPullback :
    DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} A) := by
  letI := affineLocalizationExtendScalars_additive (R := R) (A := A)
  letI := affineLocalizationExtendScalars_preservesFiniteLimits
    (R := R) (A := A) M
  exact (ModuleCat.extendScalars.{u, u, u}
    (algebraMap R A)).mapDerivedCategory

/-- Exact derived restriction of scalars.  It supplies an explicit preimage
for essential surjectivity of localization pullback. -/
def affineLocalizationDerivedRestriction :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} R) :=
  (ModuleCat.restrictScalars.{u, u, u}
    (algebraMap R A)).mapDerivedCategory

/-- On derived module categories, restriction followed by localization
pullback is naturally isomorphic to the identity. -/
def affineLocalizationDerivedCounitIso :
    affineLocalizationDerivedRestriction (R := R) (A := A) ⋙
        affineLocalizationDerivedPullback (R := R) (A := A) M ≅
      𝟭 (DerivedCategory (ModuleCat.{u} A)) := by
  letI := affineLocalizationExtendScalars_additive (R := R) (A := A)
  letI := affineLocalizationExtendScalars_preservesFiniteLimits
    (R := R) (A := A) M
  exact Functor.mapDerivedCategoryCompIso
      (affineLocalizationExtendRestrictCounitIso M) ≪≫
    Functor.mapDerivedCategoryIdIso (ModuleCat.{u} A)

/-- Derived extension of scalars along a localization is essentially
surjective. -/
instance affineLocalizationDerivedPullback_essSurj :
    (affineLocalizationDerivedPullback (R := R) (A := A) M).EssSurj where
  mem_essImage E :=
    ⟨(affineLocalizationDerivedRestriction (R := R) (A := A)).obj E,
      ⟨(affineLocalizationDerivedCounitIso (R := R) (A := A) M).app E⟩⟩

/-- Transport localization pullback from derived module categories to the
genuine derived categories of quasi-coherent sheaves on affine spectra. -/
def affineQuasicoherentLocalizationPullback :
    AffineQuasicoherentDerivedCategory (CommRingCat.of R) ⥤
      AffineQuasicoherentDerivedCategory (CommRingCat.of A) :=
  equivalenceTransportFunctor
    (affineQuasicoherentDerivedEquivalence (CommRingCat.of R))
    (affineQuasicoherentDerivedEquivalence (CommRingCat.of A))
    (affineLocalizationDerivedPullback M)

/-- Transport restriction of scalars to affine quasi-coherent derived
categories. -/
def affineQuasicoherentLocalizationRestriction :
    AffineQuasicoherentDerivedCategory (CommRingCat.of A) ⥤
      AffineQuasicoherentDerivedCategory (CommRingCat.of R) :=
  equivalenceTransportFunctor
    (affineQuasicoherentDerivedEquivalence (CommRingCat.of A))
    (affineQuasicoherentDerivedEquivalence (CommRingCat.of R))
    (affineLocalizationDerivedRestriction (R := R) (A := A))

/-- On affine quasi-coherent derived categories, transported restriction
followed by localization pullback is naturally isomorphic to the identity. -/
def affineQuasicoherentLocalizationCounitIso :
    affineQuasicoherentLocalizationRestriction (R := R) (A := A) ⋙
        affineQuasicoherentLocalizationPullback (R := R) (A := A) M ≅
      𝟭 (AffineQuasicoherentDerivedCategory (CommRingCat.of A)) :=
  equivalenceTransportCompIso
      (affineQuasicoherentDerivedEquivalence (CommRingCat.of A))
      (affineQuasicoherentDerivedEquivalence (CommRingCat.of R))
      (affineQuasicoherentDerivedEquivalence (CommRingCat.of A))
      (affineLocalizationDerivedRestriction (R := R) (A := A))
      (affineLocalizationDerivedPullback M)
      (𝟭 (DerivedCategory (ModuleCat A)))
      (affineLocalizationDerivedCounitIso M) ≪≫
    equivalenceTransportIdIso
      (affineQuasicoherentDerivedEquivalence (CommRingCat.of A))
      (𝟭 (DerivedCategory (ModuleCat A)))
      (𝟭 (DerivedCategory (ModuleCat A)))
      (Iso.refl _) (Iso.refl _)

/-- Localization pullback is essentially surjective on the genuine affine
quasi-coherent derived categories. -/
instance affineQuasicoherentLocalizationPullback_essSurj :
    (affineQuasicoherentLocalizationPullback
      (R := R) (A := A) M).EssSurj where
  mem_essImage E :=
    ⟨(affineQuasicoherentLocalizationRestriction
        (R := R) (A := A)).obj E,
      ⟨(affineQuasicoherentLocalizationCounitIso
        (R := R) (A := A) M).app E⟩⟩

end

end AlgebraicGeometry.DerivedCategory.Dqc
