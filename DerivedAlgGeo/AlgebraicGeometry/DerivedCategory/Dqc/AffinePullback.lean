/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffinePushforward

/-!
# Pullback on affine quasi-coherent sheaves

For a ring map `R → S`, extension of scalars transports through the affine
equivalences to a functor from quasi-coherent sheaves on `Spec R` to those on
`Spec S`. Its adjunction with the geometric affine pushforward identifies this
transported functor by the expected geometric universal property.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Pseudofunctor

noncomputable section

universe u

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

end

end AlgebraicGeometry.DerivedCategory.Dqc
