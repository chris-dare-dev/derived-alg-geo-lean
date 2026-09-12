/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Adjunction.Restrict
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectivePullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffinePushforward

/-!
# Pullback on affine quasi-coherent sheaves

For a ring map `R → S`, extension of scalars transports through the affine
equivalences to a functor from quasi-coherent sheaves on `Spec R` to those on
`Spec S`. Its adjunction with the geometric affine pushforward identifies this
transported functor by the expected geometric universal property.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Affine quasi-coherent pullback, constructed by transporting extension of
scalars through the affine equivalences. -/
def affineQuasicoherentSheavesPullback
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    AffineQuasicoherentSheaves R ⥤ AffineQuasicoherentSheaves S :=
  equivalenceTransportFunctor
    (affineQuasicoherentSheavesEquiv R)
    (affineQuasicoherentSheavesEquiv S)
    (ModuleCat.extendScalars f.hom)

private def affineQuasicoherentSheavesPullbackLeftStageAdjunction
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (affineQuasicoherentSheavesEquiv R).inverse ⋙
        ModuleCat.extendScalars f.hom ⊣
      ModuleCat.restrictScalars f.hom ⋙
        (affineQuasicoherentSheavesEquiv R).functor :=
  (affineQuasicoherentSheavesEquiv R).symm.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj f.hom)

private def affineQuasicoherentSheavesTransportedAdjunction
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ((affineQuasicoherentSheavesEquiv R).inverse ⋙
        ModuleCat.extendScalars f.hom) ⋙
        (affineQuasicoherentSheavesEquiv S).functor ⊣
      (affineQuasicoherentSheavesEquiv S).inverse ⋙
        (ModuleCat.restrictScalars f.hom ⋙
          (affineQuasicoherentSheavesEquiv R).functor) :=
  (affineQuasicoherentSheavesPullbackLeftStageAdjunction f).comp
    (affineQuasicoherentSheavesEquiv S).toAdjunction

/-- Transported extension of scalars is left adjoint to geometric affine
quasi-coherent pushforward. -/
def affineQuasicoherentSheavesPullbackPushforwardAdjunction
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    affineQuasicoherentSheavesPullback f ⊣
      affineQuasicoherentSheavesPushforward f := by
  let transportedAdj : affineQuasicoherentSheavesPullback f ⊣
      equivalenceTransportFunctor
        (affineQuasicoherentSheavesEquiv S)
        (affineQuasicoherentSheavesEquiv R)
        (ModuleCat.restrictScalars f.hom) :=
    (affineQuasicoherentSheavesTransportedAdjunction f).ofNatIsoRight
      (Functor.associator _ _ _).symm
  exact transportedAdj.ofNatIsoRight
    (affineQuasicoherentSheavesPushforwardComparison f).symm

/-- Affine global sections identify quasi-coherent pullback with extension
of scalars. -/
def affineQuasicoherentSheavesPullbackGammaIso
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    affineQuasicoherentSheavesPullback f ⋙
        (affineQuasicoherentSheavesEquiv S).inverse ≅
      (affineQuasicoherentSheavesEquiv R).inverse ⋙
        ModuleCat.extendScalars f.hom :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((affineQuasicoherentSheavesEquiv R).inverse ⋙
        ModuleCat.extendScalars f.hom)
      (affineQuasicoherentSheavesEquiv S).unitIso.symm ≪≫
    Functor.rightUnitor _

/-- Affine quasi-coherent pullback is additive. -/
instance affineQuasicoherentSheavesPullback_additive
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (affineQuasicoherentSheavesPullback f).Additive := by
  letI := affineExtendScalars_additive f
  dsimp [affineQuasicoherentSheavesPullback,
    equivalenceTransportFunctor]
  infer_instance

/-- Affine quasi-coherent pullback preserves finite colimits. -/
instance affineQuasicoherentSheavesPullback_preservesFiniteColimits
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    PreservesFiniteColimits (affineQuasicoherentSheavesPullback f) := by
  haveI : PreservesColimitsOfSize
      (affineQuasicoherentSheavesPullback f) :=
    (affineQuasicoherentSheavesPullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  infer_instance

/-- Affine quasi-coherent pullback preserves finite limits when the ring map
is flat. -/
theorem affineQuasicoherentSheavesPullback_preservesFiniteLimits
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    PreservesFiniteLimits (affineQuasicoherentSheavesPullback f) := by
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} f.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  dsimp [affineQuasicoherentSheavesPullback,
    equivalenceTransportFunctor]
  infer_instance

/-- Exact affine quasi-coherent derived pullback along a flat ring map. -/
def affineQuasicoherentDerivedPullback
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    AffineQuasicoherentDerivedCategory R ⥤
      AffineQuasicoherentDerivedCategory S := by
  letI := affineQuasicoherentSheavesPullback_preservesFiniteLimits f hf
  exact (affineQuasicoherentSheavesPullback f).mapDerivedCategory

/-- Derived extension of scalars along a flat map, with exactness packaged
in the construction. -/
def affineExtendScalarsDerived
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    DerivedCategory (ModuleCat R) ⥤ DerivedCategory (ModuleCat S) := by
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} f.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  exact (ModuleCat.extendScalars f.hom).mapDerivedCategory

/-- On derived categories, affine global sections identify exact pullback
with derived extension of scalars. -/
def affineQuasicoherentDerivedPullbackGammaIso
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    affineQuasicoherentDerivedPullback f hf ⋙
        affineGammaDerivedFunctor S ≅
      affineGammaDerivedFunctor R ⋙
        affineExtendScalarsDerived f hf := by
  letI := affineQuasicoherentSheavesPullback_preservesFiniteLimits f hf
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} f.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let H := (affineQuasicoherentSheavesEquiv R).inverse ⋙
    ModuleCat.extendScalars f.hom
  letI : H.Additive := by dsimp [H]; infer_instance
  letI : PreservesFiniteLimits H := by
    dsimp [H]
    exact comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits H := by
    dsimp [H]
    exact comp_preservesFiniteColimits _ _
  exact Functor.mapDerivedCategoryCompIso
      (affineQuasicoherentSheavesPullbackGammaIso f) ≪≫
    (Functor.mapDerivedCategoryCompIso (Iso.refl H)).symm

/-- Exact affine derived pullback is extension of scalars transported
through the affine derived equivalences. -/
def affineQuasicoherentDerivedPullbackComparison
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    affineQuasicoherentDerivedPullback f hf ≅
      equivalenceTransportFunctor
        (affineQuasicoherentDerivedEquivalence R)
        (affineQuasicoherentDerivedEquivalence S)
        (affineExtendScalarsDerived f hf) := by
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, u} f.hom) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  let transported := equivalenceTransportFunctor
    (affineQuasicoherentDerivedEquivalence R)
    (affineQuasicoherentDerivedEquivalence S)
    (affineExtendScalarsDerived f hf)
  let cancel : transported ⋙ affineGammaDerivedFunctor S ≅
      affineGammaDerivedFunctor R ⋙
        affineExtendScalarsDerived f hf :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        ((affineQuasicoherentDerivedEquivalence R).inverse ⋙
          affineExtendScalarsDerived f hf)
        (affineQuasicoherentDerivedEquivalence S).unitIso.symm ≪≫
      Functor.rightUnitor _
  letI : (affineGammaDerivedFunctor S).Full :=
    (affineQuasicoherentDerivedEquivalence S).fullyFaithfulInverse.full
  letI : (affineGammaDerivedFunctor S).Faithful :=
    (affineQuasicoherentDerivedEquivalence S).fullyFaithfulInverse.faithful
  exact Functor.fullyFaithfulCancelRight (affineGammaDerivedFunctor S)
    (affineQuasicoherentDerivedPullbackGammaIso f hf ≪≫ cancel.symm)

/-- Exact affine derived pullback is left adjoint to exact affine derived
pushforward. -/
def affineQuasicoherentDerivedPullbackPushforwardAdjunction
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    affineQuasicoherentDerivedPullback f hf ⊣
      affineQuasicoherentDerivedPushforward f := by
  letI := affineQuasicoherentSheavesPullback_preservesFiniteLimits f hf
  exact (affineQuasicoherentSheavesPullbackPushforwardAdjunction f).mapDerivedCategory

/-- Flat affine quasi-coherent derived pullback preserves cohomologically
bounded objects. -/
theorem affineQuasicoherentDerivedPullback_bounded
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)
    (E : AffineQuasicoherentDerivedCategory R)
    (hE : (DerivedCategory.TStructure.t
      (C := AffineQuasicoherentSheaves R)).bounded E) :
    (DerivedCategory.TStructure.t
      (C := AffineQuasicoherentSheaves S)).bounded
        ((affineQuasicoherentDerivedPullback f hf).obj E) := by
  letI := affineQuasicoherentSheavesPullback_preservesFiniteLimits f hf
  exact mapDerivedCategory_bounded
    (affineQuasicoherentSheavesPullback f) E hE

/-- Flat affine quasi-coherent derived pullback restricted to bounded
objects. -/
def affineQuasicoherentBoundedDerivedPullback
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    AffineQuasicoherentBoundedDerivedCategory R ⥤
      AffineQuasicoherentBoundedDerivedCategory S :=
  (DerivedCategory.TStructure.t
    (C := AffineQuasicoherentSheaves S)).bounded.lift
      (DerivedCategory.Bounded.ι ⋙
        affineQuasicoherentDerivedPullback f hf)
      (fun E ↦ affineQuasicoherentDerivedPullback_bounded
        f hf E.obj E.property)

/-- Forgetting boundedness recovers flat affine quasi-coherent derived
pullback. -/
def affineQuasicoherentBoundedDerivedPullbackCompInclusion
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    affineQuasicoherentBoundedDerivedPullback f hf ⋙
        DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙
        affineQuasicoherentDerivedPullback f hf :=
  (DerivedCategory.TStructure.t
    (C := AffineQuasicoherentSheaves S)).bounded.liftCompιIso
      (DerivedCategory.Bounded.ι ⋙
        affineQuasicoherentDerivedPullback f hf)
      (fun E ↦ affineQuasicoherentDerivedPullback_bounded
        f hf E.obj E.property)

/-- The exact affine derived pullback--pushforward adjunction restricts to
cohomologically bounded objects. -/
def affineQuasicoherentBoundedDerivedPullbackPushforwardAdjunction
    {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat) :
    affineQuasicoherentBoundedDerivedPullback f hf ⊣
      affineQuasicoherentBoundedDerivedPushforward f :=
  (affineQuasicoherentDerivedPullbackPushforwardAdjunction f hf).restrictFullyFaithful
    (DerivedCategory.TStructure.t
      (C := AffineQuasicoherentSheaves R)).bounded.fullyFaithfulι
    (DerivedCategory.TStructure.t
      (C := AffineQuasicoherentSheaves S)).bounded.fullyFaithfulι
    (affineQuasicoherentBoundedDerivedPullbackCompInclusion f hf).symm
    (affineQuasicoherentBoundedDerivedPushforwardCompInclusion f).symm

end

end AlgebraicGeometry.DerivedCategory.Dqc
