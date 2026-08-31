/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.BoundedAboveProjective.Unitality
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectiveCoherence

/-!
# Units for affine pullback on the bounded-above projective locus

This file specializes the generic identity comparison to extension of
scalars along the identity ring morphism.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc

open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Pullback along the identity ring morphism is the identity on the
bounded-above projective homotopy locus. -/
def affineBoundedAboveProjectiveHomotopyPullbackIdIso
    (R : CommRingCat.{u}) :
    affineBoundedAboveProjectiveHomotopyPullback (𝟙 R : R ⟶ R) ≅
      𝟭 (BoundedAboveProjectiveHomotopyCategory (ModuleCat R)) :=
  mapBoundedAboveProjectiveHomotopyIso
      (ModuleCat.extendScalars.{u, u, u} (𝟙 R : R ⟶ R).hom)
      (𝟭 (ModuleCat R))
      (by simpa using ModuleCat.extendScalarsId R) ≪≫
    mapBoundedAboveProjectiveHomotopyIdIso (ModuleCat R)

/-- Pullback along the identity ring morphism is the identity on the
bounded-above projective derived locus. -/
def affineBoundedAboveProjectiveDerivedPullbackIdIso
    (R : CommRingCat.{u}) :
    affineBoundedAboveProjectiveDerivedPullback (𝟙 R : R ⟶ R) ≅
      𝟭 (BoundedAboveProjectiveDerivedCategory (ModuleCat R)) :=
  boundedAboveProjectiveDerivedFunctorIso
      (ModuleCat.extendScalars.{u, u, u} (𝟙 R : R ⟶ R).hom)
      (𝟭 (ModuleCat R))
      (by simpa using ModuleCat.extendScalarsId R) ≪≫
    boundedAboveProjectiveDerivedFunctorIdIso (ModuleCat R)

end

end AlgebraicGeometry.DerivedCategory.Dqc
