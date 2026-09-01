/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectivePullback

/-!
# Preservation of the affine bounded-above projective locus

Extension of scalars preserves projective modules, so the generic
bounded-above projective derived functor specializes to a composable affine
pullback without a flatness hypothesis.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Extension of scalars preserves projective modules. -/
instance affineExtendScalars_preservesProjectiveObjects
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (ModuleCat.extendScalars.{u, u, u} f.hom).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f.hom)

/-- Arbitrary affine extension of scalars acts on bounded-above projective
homotopy representatives. -/
def affineBoundedAboveProjectiveHomotopyPullback
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    BoundedAboveProjectiveHomotopyCategory (ModuleCat R) ⥤
      BoundedAboveProjectiveHomotopyCategory (ModuleCat A) :=
  mapBoundedAboveProjectiveHomotopy
    (ModuleCat.extendScalars.{u, u, u} f.hom)

/-- Affine extension of scalars composes on bounded-above projective
homotopy representatives. -/
def affineBoundedAboveProjectiveHomotopyPullbackCompIso
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) :
    affineBoundedAboveProjectiveHomotopyPullback f ⋙
        affineBoundedAboveProjectiveHomotopyPullback g ≅
      affineBoundedAboveProjectiveHomotopyPullback (f ≫ g) :=
  mapBoundedAboveProjectiveHomotopyCompIso
    (ModuleCat.extendScalars.{u, u, u} f.hom)
    (ModuleCat.extendScalars.{u, u, u} g.hom)
    (ModuleCat.extendScalars.{u, u, u} (f ≫ g).hom)
    (by simpa using (ModuleCat.extendScalarsComp f.hom g.hom).symm)

/-- Arbitrary affine derived pullback preserves the full derived locus
represented by bounded-above complexes of projective modules. -/
def affineBoundedAboveProjectiveDerivedPullback
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    BoundedAboveProjectiveDerivedCategory (ModuleCat R) ⥤
      BoundedAboveProjectiveDerivedCategory (ModuleCat A) :=
  boundedAboveProjectiveDerivedFunctor (ModuleCat.extendScalars f.hom)

/-- Arbitrary affine derived pullback composes on the bounded-above
projective derived loci. -/
def affineBoundedAboveProjectiveDerivedPullbackCompIso
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) :
    affineBoundedAboveProjectiveDerivedPullback f ⋙
        affineBoundedAboveProjectiveDerivedPullback g ≅
      affineBoundedAboveProjectiveDerivedPullback (f ≫ g) :=
  boundedAboveProjectiveDerivedFunctorCompIso
    (ModuleCat.extendScalars.{u, u, u} f.hom)
    (ModuleCat.extendScalars.{u, u, u} g.hom)
    (ModuleCat.extendScalars.{u, u, u} (f ≫ g).hom)
    (by simpa using (ModuleCat.extendScalarsComp f.hom g.hom).symm)

end

end AlgebraicGeometry.DerivedCategory.Dqc
