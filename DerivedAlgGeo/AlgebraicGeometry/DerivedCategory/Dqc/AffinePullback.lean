/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Descent
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

end

end AlgebraicGeometry.DerivedCategory.Dqc
