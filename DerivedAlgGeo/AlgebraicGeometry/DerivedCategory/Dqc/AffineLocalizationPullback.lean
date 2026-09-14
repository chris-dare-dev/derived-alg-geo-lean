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
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineRealization
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineQuasicoherentIdentification
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffinePullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffinePushforward

/-!
# Derived pullback along an affine localization

For a localization `R → A`, restriction of scalars followed by extension of
scalars is naturally isomorphic to the identity on `A`-modules.  Flatness of
localizations therefore lets this counit descend to derived categories and
exhibits derived extension of scalars as essentially surjective.

This is the algebraic affine-localization input for the essential-surjectivity
part of the base-change construction.  The module and quasi-coherent functors
are compared here with the general exact affine pullback, including the
pullback--restriction adjunction on unbounded and bounded derived categories.
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
/-- The algebra map of a localization is flat. -/
theorem affineLocalizationAlgebraMap_flat : (algebraMap R A).Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat A M)

include M in
/-- Extension of scalars along a localization preserves finite limits. -/
theorem affineLocalizationExtendScalars_preservesFiniteLimits :
    PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)) :=
  ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (affineLocalizationAlgebraMap_flat M)

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

include M in
/-- The localization-specific derived pullback is the general exact derived
extension-of-scalars functor specialized to the flat localization map. -/
def affineLocalizationDerivedPullbackComparison :
    affineLocalizationDerivedPullback (R := R) (A := A) M ≅
      affineExtendScalarsDerived
        (CommRingCat.ofHom (algebraMap R A))
        (affineLocalizationAlgebraMap_flat M) :=
  Iso.refl _

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

include M in
/-- Derived localization pullback preserves cohomologically bounded objects. -/
theorem affineLocalizationDerivedPullback_bounded
    (E : DerivedCategory (ModuleCat.{u} R))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).bounded E) :
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).bounded
      ((affineLocalizationDerivedPullback M).obj E) := by
  letI := affineLocalizationExtendScalars_additive (R := R) (A := A)
  letI := affineLocalizationExtendScalars_preservesFiniteLimits
    (R := R) (A := A) M
  exact mapDerivedCategory_bounded
    (ModuleCat.extendScalars.{u, u, u} (algebraMap R A)) E hE

/-- Derived restriction of scalars preserves cohomologically bounded
objects. -/
theorem affineLocalizationDerivedRestriction_bounded
    (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).bounded E) :
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).bounded
      ((affineLocalizationDerivedRestriction (R := R) (A := A)).obj E) :=
  mapDerivedCategory_bounded
    (ModuleCat.restrictScalars.{u, u, u} (algebraMap R A)) E hE

include M in
/-- Exact derived localization pullback restricted to cohomologically
bounded derived categories. -/
def affineLocalizationBoundedDerivedPullback :
    DerivedCategory.Bounded (ModuleCat.{u} R) ⥤
      DerivedCategory.Bounded (ModuleCat.{u} A) :=
  (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).bounded.lift
    (DerivedCategory.Bounded.ι ⋙ affineLocalizationDerivedPullback M)
    (fun E ↦ affineLocalizationDerivedPullback_bounded M E.obj E.property)

/-- Exact derived restriction of scalars restricted to cohomologically
bounded derived categories. -/
def affineLocalizationBoundedDerivedRestriction :
    DerivedCategory.Bounded (ModuleCat.{u} A) ⥤
      DerivedCategory.Bounded (ModuleCat.{u} R) :=
  (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).bounded.lift
    (DerivedCategory.Bounded.ι ⋙
      affineLocalizationDerivedRestriction (R := R) (A := A))
    (fun E ↦ affineLocalizationDerivedRestriction_bounded E.obj E.property)

include M in
/-- Forgetting boundedness recovers derived localization pullback. -/
def affineLocalizationBoundedDerivedPullbackCompInclusion :
    affineLocalizationBoundedDerivedPullback (R := R) (A := A) M ⋙
        DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ affineLocalizationDerivedPullback M :=
  (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).bounded.liftCompιIso
    (DerivedCategory.Bounded.ι ⋙ affineLocalizationDerivedPullback M)
    (fun E ↦ affineLocalizationDerivedPullback_bounded M E.obj E.property)

/-- Forgetting boundedness recovers derived restriction of scalars. -/
def affineLocalizationBoundedDerivedRestrictionCompInclusion :
    affineLocalizationBoundedDerivedRestriction (R := R) (A := A) ⋙
        DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙
        affineLocalizationDerivedRestriction (R := R) (A := A) :=
  (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).bounded.liftCompιIso
    (DerivedCategory.Bounded.ι ⋙
      affineLocalizationDerivedRestriction (R := R) (A := A))
    (fun E ↦ affineLocalizationDerivedRestriction_bounded E.obj E.property)

include M in
/-- On bounded derived module categories, restriction followed by localization
pullback is naturally isomorphic to the identity. -/
def affineLocalizationBoundedDerivedCounitIso :
    affineLocalizationBoundedDerivedRestriction (R := R) (A := A) ⋙
        affineLocalizationBoundedDerivedPullback (R := R) (A := A) M ≅
      Functor.id (DerivedCategory.Bounded (ModuleCat.{u} A)) :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Bounded.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (affineLocalizationBoundedDerivedRestriction (R := R) (A := A))
        (affineLocalizationBoundedDerivedPullbackCompInclusion M) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (affineLocalizationBoundedDerivedRestrictionCompInclusion
          (R := R) (A := A))
        (affineLocalizationDerivedPullback M) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Bounded.ι
        (affineLocalizationDerivedCounitIso M) ≪≫
      Functor.rightUnitor _ ≪≫
      (Functor.leftUnitor _).symm)

include M in
/-- Derived extension of scalars along a localization is essentially
surjective on cohomologically bounded derived categories. -/
instance affineLocalizationBoundedDerivedPullback_essSurj :
    (affineLocalizationBoundedDerivedPullback
      (R := R) (A := A) M).EssSurj where
  mem_essImage E :=
    ⟨(affineLocalizationBoundedDerivedRestriction
        (R := R) (A := A)).obj E,
      ⟨(affineLocalizationBoundedDerivedCounitIso
        (R := R) (A := A) M).app E⟩⟩

/-- Transport bounded localization pullback to the genuine bounded derived
categories of quasi-coherent sheaves on affine spectra. -/
def affineQuasicoherentBoundedLocalizationPullback :
    AffineQuasicoherentBoundedDerivedCategory (CommRingCat.of R) ⥤
      AffineQuasicoherentBoundedDerivedCategory (CommRingCat.of A) :=
  equivalenceTransportFunctor
    (affineQuasicoherentBoundedDerivedEquivalence (CommRingCat.of R))
    (affineQuasicoherentBoundedDerivedEquivalence (CommRingCat.of A))
    (affineLocalizationBoundedDerivedPullback M)

/-- Transport bounded restriction of scalars to the genuine bounded derived
categories of affine quasi-coherent sheaves. -/
def affineQuasicoherentBoundedLocalizationRestriction :
    AffineQuasicoherentBoundedDerivedCategory (CommRingCat.of A) ⥤
      AffineQuasicoherentBoundedDerivedCategory (CommRingCat.of R) :=
  equivalenceTransportFunctor
    (affineQuasicoherentBoundedDerivedEquivalence (CommRingCat.of A))
    (affineQuasicoherentBoundedDerivedEquivalence (CommRingCat.of R))
    (affineLocalizationBoundedDerivedRestriction (R := R) (A := A))

/-- On bounded affine quasi-coherent derived categories, transported
restriction followed by localization pullback is naturally isomorphic to the
identity. -/
def affineQuasicoherentBoundedLocalizationCounitIso :
    affineQuasicoherentBoundedLocalizationRestriction
        (R := R) (A := A) ⋙
      affineQuasicoherentBoundedLocalizationPullback
        (R := R) (A := A) M ≅
      Functor.id
        (AffineQuasicoherentBoundedDerivedCategory (CommRingCat.of A)) :=
  equivalenceTransportCompIso
      (affineQuasicoherentBoundedDerivedEquivalence (CommRingCat.of A))
      (affineQuasicoherentBoundedDerivedEquivalence (CommRingCat.of R))
      (affineQuasicoherentBoundedDerivedEquivalence (CommRingCat.of A))
      (affineLocalizationBoundedDerivedRestriction (R := R) (A := A))
      (affineLocalizationBoundedDerivedPullback M)
      (Functor.id (DerivedCategory.Bounded (ModuleCat A)))
      (affineLocalizationBoundedDerivedCounitIso M) ≪≫
    equivalenceTransportIdIso
      (affineQuasicoherentBoundedDerivedEquivalence (CommRingCat.of A))
      (Functor.id (DerivedCategory.Bounded (ModuleCat A)))
      (Functor.id (DerivedCategory.Bounded (ModuleCat A)))
      (Iso.refl _) (Iso.refl _)

/-- Localization pullback is essentially surjective on bounded affine
quasi-coherent derived categories. -/
instance affineQuasicoherentBoundedLocalizationPullback_essSurj :
    (affineQuasicoherentBoundedLocalizationPullback
      (R := R) (A := A) M).EssSurj where
  mem_essImage E :=
    ⟨(affineQuasicoherentBoundedLocalizationRestriction
        (R := R) (A := A)).obj E,
      ⟨(affineQuasicoherentBoundedLocalizationCounitIso
        (R := R) (A := A) M).app E⟩⟩

/-- Bounded affine localization pullback followed by realization into the
intrinsic bounded target `Dqc` category. -/
def affineQuasicoherentBoundedLocalizationPullbackToDqc :
    AffineQuasicoherentBoundedDerivedCategory (CommRingCat.of R) ⥤
      SchemeBoundedQuasicoherentDerivedCategory (Spec (CommRingCat.of A)) :=
  affineQuasicoherentBoundedLocalizationPullback M ⋙
    affineQuasicoherentBoundedDerivedToDqc (CommRingCat.of A)

include M in
/-- Bounded localization pullback reaches every object of the intrinsic bounded target
`Dqc` category. -/
instance affineQuasicoherentBoundedLocalizationPullbackToDqc_essSurj :
    (affineQuasicoherentBoundedLocalizationPullbackToDqc
      (R := R) (A := A) M).EssSurj := by
  letI : (affineQuasicoherentBoundedLocalizationPullback
      (R := R) (A := A) M).EssSurj :=
    affineQuasicoherentBoundedLocalizationPullback_essSurj
      (R := R) (A := A) M
  letI : (affineQuasicoherentBoundedDerivedToDqc
      (CommRingCat.of A)).EssSurj :=
    affineQuasicoherentBoundedDerivedToDqc_essSurj (CommRingCat.of A)
  change (affineQuasicoherentBoundedLocalizationPullback M ⋙
    affineQuasicoherentBoundedDerivedToDqc (CommRingCat.of A)).EssSurj
  infer_instance

/-- Bounded localization pullback and bounded affine realization have the same essential
image; both now reach the entire intrinsic bounded target `Dqc` category. -/
theorem affineQuasicoherentBoundedLocalizationPullbackToDqc_essImage :
    (affineQuasicoherentBoundedLocalizationPullbackToDqc M).essImage =
      (affineQuasicoherentBoundedDerivedToDqc
        (CommRingCat.of A)).essImage := by
  change (affineQuasicoherentBoundedLocalizationPullback M ⋙
    affineQuasicoherentBoundedDerivedToDqc
      (CommRingCat.of A)).essImage = _
  exact Functor.essImage_comp_of_essSurj

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

include M in
/-- The general geometric affine pullback specializes to the previously
constructed transported localization pullback. -/
def affineQuasicoherentLocalizationPullbackComparison :
    affineQuasicoherentDerivedPullback
        (CommRingCat.ofHom (algebraMap R A))
        (affineLocalizationAlgebraMap_flat M) ≅
      affineQuasicoherentLocalizationPullback (R := R) (A := A) M :=
  affineQuasicoherentDerivedPullbackComparison
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft
        (affineQuasicoherentDerivedEquivalence (CommRingCat.of R)).inverse
        (affineLocalizationDerivedPullbackComparison M).symm)
      (affineQuasicoherentDerivedEquivalence (CommRingCat.of A)).functor

/-- For the affine localization morphism, geometric derived pushforward is
the transported restriction-of-scalars functor. -/
def affineQuasicoherentLocalizationRestrictionComparison :
    affineQuasicoherentDerivedPushforward
        (CommRingCat.ofHom (algebraMap R A)) ≅
      affineQuasicoherentLocalizationRestriction (R := R) (A := A) :=
  affineQuasicoherentDerivedPushforwardComparison
    (CommRingCat.ofHom (algebraMap R A))

include M in
/-- The geometric affine pullback--pushforward adjunction specializes to the
transported localization pullback and restriction functors. -/
def affineQuasicoherentLocalizationPullbackRestrictionAdjunction :
    affineQuasicoherentLocalizationPullback (R := R) (A := A) M ⊣
      affineQuasicoherentLocalizationRestriction (R := R) (A := A) :=
  ((affineQuasicoherentDerivedPullbackPushforwardAdjunction
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M)).ofNatIsoLeft
        (affineQuasicoherentLocalizationPullbackComparison M)).ofNatIsoRight
    (affineQuasicoherentLocalizationRestrictionComparison (R := R) (A := A))

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

/-- Geometric affine pushforward followed by localization pullback is the
identity on the target affine quasi-coherent derived category. -/
def affineQuasicoherentLocalizationGeometricCounitIso :
    affineQuasicoherentDerivedPushforward
        (CommRingCat.ofHom (algebraMap R A)) ⋙
      affineQuasicoherentLocalizationPullback (R := R) (A := A) M ≅
      Functor.id
        (AffineQuasicoherentDerivedCategory (CommRingCat.of A)) :=
  Functor.isoWhiskerRight
      (affineQuasicoherentLocalizationRestrictionComparison
        (R := R) (A := A))
      (affineQuasicoherentLocalizationPullback M) ≪≫
    affineQuasicoherentLocalizationCounitIso M

/-- Forgetting boundedness recovers transported affine localization
pullback. -/
def affineQuasicoherentBoundedLocalizationPullbackCompInclusion :
    affineQuasicoherentBoundedLocalizationPullback
        (R := R) (A := A) M ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙
        affineQuasicoherentLocalizationPullback (R := R) (A := A) M :=
  Iso.refl _

/-- Forgetting boundedness recovers transported affine restriction of
scalars. -/
def affineQuasicoherentBoundedLocalizationRestrictionCompInclusion :
    affineQuasicoherentBoundedLocalizationRestriction
        (R := R) (A := A) ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙
        affineQuasicoherentLocalizationRestriction (R := R) (A := A) :=
  Iso.refl _

include M in
/-- The bounded general geometric affine pullback specializes to the bounded
transported localization pullback. -/
def affineQuasicoherentBoundedLocalizationPullbackComparison :
    affineQuasicoherentBoundedDerivedPullback
        (CommRingCat.ofHom (algebraMap R A))
        (affineLocalizationAlgebraMap_flat M) ≅
      affineQuasicoherentBoundedLocalizationPullback
        (R := R) (A := A) M :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Bounded.ι
    (affineQuasicoherentBoundedDerivedPullbackCompInclusion
        (CommRingCat.ofHom (algebraMap R A))
        (affineLocalizationAlgebraMap_flat M) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Bounded.ι
        (affineQuasicoherentLocalizationPullbackComparison M) ≪≫
      (affineQuasicoherentBoundedLocalizationPullbackCompInclusion M).symm)

include M in
/-- The canonical exact bounded affine pullback is essentially surjective
when the ring map is a localization. -/
instance affineQuasicoherentBoundedDerivedPullback_essSurj_of_isLocalization :
    (affineQuasicoherentBoundedDerivedPullback
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M)).EssSurj :=
  Functor.essSurj_of_iso
    (affineQuasicoherentBoundedLocalizationPullbackComparison M).symm

include M in
/-- The canonical exact bounded affine pullback along a localization reaches every object of
the intrinsic bounded target `Dqc` category. -/
instance affineQuasicoherentBoundedDerivedPullbackToDqc_essSurj_of_isLocalization :
    (affineQuasicoherentBoundedDerivedPullbackToDqc
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M)).EssSurj := by
  letI : (affineQuasicoherentBoundedDerivedPullback
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M)).EssSurj :=
    affineQuasicoherentBoundedDerivedPullback_essSurj_of_isLocalization
      (R := R) (A := A) M
  letI : (affineQuasicoherentBoundedDerivedToDqc
      (CommRingCat.of A)).EssSurj :=
    affineQuasicoherentBoundedDerivedToDqc_essSurj (CommRingCat.of A)
  change (affineQuasicoherentBoundedDerivedPullback
    (CommRingCat.ofHom (algebraMap R A))
    (affineLocalizationAlgebraMap_flat M) ⋙
      affineQuasicoherentBoundedDerivedToDqc (CommRingCat.of A)).EssSurj
  infer_instance

include M in
/-- The bounded affine-localization specialization of the essential-image conclusion; both
sides are the entire intrinsic bounded target `Dqc` category. -/
theorem affineQuasicoherentBoundedDerivedPullbackToDqc_essImage_of_isLocalization :
    (affineQuasicoherentBoundedDerivedPullbackToDqc
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M)).essImage =
        (affineQuasicoherentBoundedDerivedToDqc
          (CommRingCat.of A)).essImage := by
  change (affineQuasicoherentBoundedDerivedPullback
    (CommRingCat.ofHom (algebraMap R A))
    (affineLocalizationAlgebraMap_flat M) ⋙
      affineQuasicoherentBoundedDerivedToDqc
        (CommRingCat.of A)).essImage = _
  exact Functor.essImage_comp_of_essSurj

include M in
/-- Realizing the general bounded affine pullback along a localization agrees
with the earlier transported localization realization. -/
def affineQuasicoherentBoundedLocalizationPullbackToDqcComparison :
    affineQuasicoherentBoundedDerivedPullbackToDqc
        (CommRingCat.ofHom (algebraMap R A))
        (affineLocalizationAlgebraMap_flat M) ≅
      affineQuasicoherentBoundedLocalizationPullbackToDqc
        (R := R) (A := A) M :=
  Functor.isoWhiskerRight
    (affineQuasicoherentBoundedLocalizationPullbackComparison M)
    (affineQuasicoherentBoundedDerivedToDqc (CommRingCat.of A))

/-- For the affine localization morphism, bounded geometric derived
pushforward is the transported bounded restriction-of-scalars functor. -/
def affineQuasicoherentBoundedLocalizationRestrictionComparison :
    affineQuasicoherentBoundedDerivedPushforward
        (CommRingCat.ofHom (algebraMap R A)) ≅
      affineQuasicoherentBoundedLocalizationRestriction
        (R := R) (A := A) :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Bounded.ι
    (affineQuasicoherentBoundedDerivedPushforwardCompInclusion
        (CommRingCat.ofHom (algebraMap R A)) ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Bounded.ι
        (affineQuasicoherentLocalizationRestrictionComparison
          (R := R) (A := A)) ≪≫
      (affineQuasicoherentBoundedLocalizationRestrictionCompInclusion
        (R := R) (A := A)).symm)

include M in
/-- The bounded geometric affine pullback--pushforward adjunction specializes
to the bounded localization pullback and restriction functors. -/
def affineQuasicoherentBoundedLocalizationPullbackRestrictionAdjunction :
    affineQuasicoherentBoundedLocalizationPullback
        (R := R) (A := A) M ⊣
      affineQuasicoherentBoundedLocalizationRestriction
        (R := R) (A := A) :=
  ((affineQuasicoherentBoundedDerivedPullbackPushforwardAdjunction
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M)).ofNatIsoLeft
        (affineQuasicoherentBoundedLocalizationPullbackComparison M)).ofNatIsoRight
    (affineQuasicoherentBoundedLocalizationRestrictionComparison
      (R := R) (A := A))

/-- Bounded geometric affine pushforward followed by bounded localization
pullback is naturally isomorphic to the identity. -/
def affineQuasicoherentBoundedLocalizationGeometricCounitIso :
    affineQuasicoherentBoundedDerivedPushforward
        (CommRingCat.ofHom (algebraMap R A)) ⋙
      affineQuasicoherentBoundedLocalizationPullback
        (R := R) (A := A) M ≅
      Functor.id
        (AffineQuasicoherentBoundedDerivedCategory (CommRingCat.of A)) :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Bounded.ι
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (affineQuasicoherentBoundedDerivedPushforward
          (CommRingCat.ofHom (algebraMap R A)))
        (affineQuasicoherentBoundedLocalizationPullbackCompInclusion M) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (affineQuasicoherentBoundedDerivedPushforwardCompInclusion
          (CommRingCat.ofHom (algebraMap R A)))
        (affineQuasicoherentLocalizationPullback M) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft DerivedCategory.Bounded.ι
        (affineQuasicoherentLocalizationGeometricCounitIso M) ≪≫
      Functor.rightUnitor _ ≪≫
      (Functor.leftUnitor _).symm)

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

include M in
/-- The canonical exact affine pullback is essentially surjective when the
ring map is a localization. -/
instance affineQuasicoherentDerivedPullback_essSurj_of_isLocalization :
    (affineQuasicoherentDerivedPullback
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M)).EssSurj :=
  Functor.essSurj_of_iso
    (affineQuasicoherentLocalizationPullbackComparison M).symm

include M in
/-- The affine-localization specialization of the essential-image
conclusion: canonical exact pullback reaches every intrinsic target object
currently covered by affine realization. -/
theorem affineQuasicoherentDerivedPullbackToDqc_essImage_of_isLocalization :
    (affineQuasicoherentDerivedPullbackToDqc
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M)).essImage =
        (affineQuasicoherentDerivedToDqc
          (CommRingCat.of A)).essImage := by
  change (affineQuasicoherentDerivedPullback
    (CommRingCat.ofHom (algebraMap R A))
    (affineLocalizationAlgebraMap_flat M) ⋙
      affineQuasicoherentDerivedToDqc
        (CommRingCat.of A)).essImage = _
  exact Functor.essImage_comp_of_essSurj

/-- Affine localization pullback followed by the concrete realization into
the target `Dqc` category. -/
def affineQuasicoherentLocalizationPullbackToDqc :
    AffineQuasicoherentDerivedCategory (CommRingCat.of R) ⥤
      SchemeQuasicoherentDerivedCategory (Spec (CommRingCat.of A)) :=
  affineQuasicoherentLocalizationPullback M ⋙
    affineQuasicoherentDerivedToDqc (CommRingCat.of A)

include M in
/-- Realizing the general affine pullback along a localization agrees with
the earlier transported localization realization. -/
def affineQuasicoherentLocalizationPullbackToDqcComparison :
    affineQuasicoherentDerivedPullbackToDqc
        (CommRingCat.ofHom (algebraMap R A))
        (affineLocalizationAlgebraMap_flat M) ≅
      affineQuasicoherentLocalizationPullbackToDqc
        (R := R) (A := A) M :=
  Functor.isoWhiskerRight
    (affineQuasicoherentLocalizationPullbackComparison M)
    (affineQuasicoherentDerivedToDqc (CommRingCat.of A))

include M in
/-- If the unbounded affine `Dqc` identification is available for the target ring, then
localization pullback reaches every object of the unbounded intrinsic target `Dqc` category. -/
theorem affineQuasicoherentLocalizationPullbackToDqc_essSurj_of_identification
    (I : AffineQuasicoherentDqcIdentification (CommRingCat.of A)) :
    (affineQuasicoherentLocalizationPullbackToDqc
      (R := R) (A := A) M).EssSurj := by
  letI : (affineQuasicoherentLocalizationPullback
      (R := R) (A := A) M).EssSurj :=
    affineQuasicoherentLocalizationPullback_essSurj
      (R := R) (A := A) M
  letI : (affineQuasicoherentDerivedToDqc
      (CommRingCat.of A)).EssSurj :=
    affineQuasicoherentDerivedToDqc_essSurj_of_identification I
  change (affineQuasicoherentLocalizationPullback M ⋙
    affineQuasicoherentDerivedToDqc (CommRingCat.of A)).EssSurj
  infer_instance

include M in
/-- Under the target unbounded affine identification, the canonical exact affine pullback
along a localization reaches every object of the unbounded intrinsic target `Dqc` category. -/
theorem affineQuasicoherentDerivedPullbackToDqc_essSurj_of_isLocalization_of_identification
    (I : AffineQuasicoherentDqcIdentification (CommRingCat.of A)) :
    (affineQuasicoherentDerivedPullbackToDqc
      (CommRingCat.ofHom (algebraMap R A))
      (affineLocalizationAlgebraMap_flat M)).EssSurj := by
  letI : (affineQuasicoherentLocalizationPullbackToDqc
      (R := R) (A := A) M).EssSurj :=
    affineQuasicoherentLocalizationPullbackToDqc_essSurj_of_identification M I
  exact Functor.essSurj_of_iso
    (affineQuasicoherentLocalizationPullbackToDqcComparison M).symm

/-- Localization pullback reaches exactly all target `Dqc` objects covered
by the currently available affine realization.  Upgrading this equality to
essential surjectivity onto the full unbounded `Dqc` category is precisely
the missing affine-realization input. -/
theorem affineQuasicoherentLocalizationPullbackToDqc_essImage :
    (affineQuasicoherentLocalizationPullbackToDqc M).essImage =
      (affineQuasicoherentDerivedToDqc (CommRingCat.of A)).essImage := by
  change (affineQuasicoherentLocalizationPullback M ⋙
    affineQuasicoherentDerivedToDqc (CommRingCat.of A)).essImage = _
  exact Functor.essImage_comp_of_essSurj

end

end AlgebraicGeometry.DerivedCategory.Dqc
