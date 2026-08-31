/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectivePseudofunctor
import DerivedAlgGeo.CategoryTheory.Pseudofunctor.Transport

/-!
# Coherent affine pullback on the bounded-projective derived locus

The affine bounded-projective homotopy pseudofunctor is transported through
the localization equivalences onto its essential image in the derived
category.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Bicategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

private def affineHomotopyUnitComparison (R : CommRingCat.{u}) :
    affineBoundedAboveProjectiveHomotopyPullback (𝟙 R : R ⟶ R) ≅
      mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat R)) :=
  mapBoundedAboveProjectiveHomotopyIso
    (ModuleCat.extendScalars.{u, u, u} (𝟙 R : R ⟶ R).hom)
    (𝟭 (ModuleCat R))
    (by simpa using ModuleCat.extendScalarsId R)

private def affineHomotopyUnitIdComparison (R : CommRingCat.{u}) :
    mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat R)) ≅
      𝟭 (BoundedAboveProjectiveHomotopyCategory (ModuleCat R)) :=
  mapBoundedAboveProjectiveHomotopyIdIso (ModuleCat R)

private theorem affineDerivedPullback_eq_equivalenceTransport
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    affineBoundedAboveProjectiveDerivedPullback f =
      Pseudofunctor.equivalenceTransportFunctor
        (boundedAboveProjectiveQhEquivalence (ModuleCat R))
        (boundedAboveProjectiveQhEquivalence (ModuleCat A))
        (affineBoundedAboveProjectiveHomotopyPullback f) :=
  rfl

private theorem affineDerivedPullbackCompIso_eq_equivalenceTransport
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) :
    affineBoundedAboveProjectiveDerivedPullbackCompIso f g =
      Pseudofunctor.equivalenceTransportCompIso
        (boundedAboveProjectiveQhEquivalence (ModuleCat R))
        (boundedAboveProjectiveQhEquivalence (ModuleCat A))
        (boundedAboveProjectiveQhEquivalence (ModuleCat B))
        (affineBoundedAboveProjectiveHomotopyPullback f)
        (affineBoundedAboveProjectiveHomotopyPullback g)
        (affineBoundedAboveProjectiveHomotopyPullback (f ≫ g))
        (affineBoundedAboveProjectiveHomotopyPullbackCompIso f g) :=
  rfl

private theorem affineDerivedPullbackIdIso_eq_equivalenceTransport
    (R : CommRingCat.{u}) :
    affineBoundedAboveProjectiveDerivedPullbackIdIso R =
      Pseudofunctor.equivalenceTransportIdIso
        (boundedAboveProjectiveQhEquivalence (ModuleCat R))
        (affineBoundedAboveProjectiveHomotopyPullback (𝟙 R : R ⟶ R))
        (mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat R)))
        (affineHomotopyUnitComparison R)
        (affineHomotopyUnitIdComparison R) :=
  rfl

/-- The supported affine derived compositor satisfies the pentagon equation. -/
theorem affineBoundedAboveProjectiveDerivedPullback_associativity
    {R A B C : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) (h : B ⟶ C) :
    (affineBoundedAboveProjectiveDerivedPullbackCompIso (f ≫ g) h).symm.hom ≫
      Functor.whiskerRight
        (affineBoundedAboveProjectiveDerivedPullbackCompIso f g).symm.hom _ ≫
      (Functor.associator
        (affineBoundedAboveProjectiveDerivedPullback f)
        (affineBoundedAboveProjectiveDerivedPullback g)
        (affineBoundedAboveProjectiveDerivedPullback h)).hom ≫
      Functor.whiskerLeft (affineBoundedAboveProjectiveDerivedPullback f)
        (affineBoundedAboveProjectiveDerivedPullbackCompIso g h).hom ≫
      (affineBoundedAboveProjectiveDerivedPullbackCompIso f (g ≫ h)).hom =
        𝟙 _ := by
  exact Pseudofunctor.equivalenceTransport_associativity
      (boundedAboveProjectiveQhEquivalence (ModuleCat R))
      (boundedAboveProjectiveQhEquivalence (ModuleCat A))
      (boundedAboveProjectiveQhEquivalence (ModuleCat B))
      (boundedAboveProjectiveQhEquivalence (ModuleCat C))
      (affineBoundedAboveProjectiveHomotopyPullback f)
      (affineBoundedAboveProjectiveHomotopyPullback g)
      (affineBoundedAboveProjectiveHomotopyPullback h)
      (affineBoundedAboveProjectiveHomotopyPullback (f ≫ g))
      (affineBoundedAboveProjectiveHomotopyPullback (g ≫ h))
      (affineBoundedAboveProjectiveHomotopyPullback ((f ≫ g) ≫ h))
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso f g)
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso g h)
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso (f ≫ g) h)
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso f (g ≫ h))
      (affineBoundedAboveProjectiveHomotopyPullback_associativity f g h)

private theorem affineHomotopyPullback_leftUnitality_twoStage
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso (𝟙 R) f).symm.hom ≫
      Functor.whiskerRight
        ((affineHomotopyUnitComparison R ≪≫
            affineHomotopyUnitIdComparison R)).hom
        (affineBoundedAboveProjectiveHomotopyPullback f) ≫
      (Functor.leftUnitor
        (affineBoundedAboveProjectiveHomotopyPullback f)).hom = 𝟙 _ := by
  exact affineBoundedAboveProjectiveHomotopyPullback_leftUnitality f

private theorem affineHomotopyPullback_rightUnitality_twoStage
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso f (𝟙 A)).symm.hom ≫
      Functor.whiskerLeft
        (affineBoundedAboveProjectiveHomotopyPullback f)
        ((affineHomotopyUnitComparison A ≪≫
            affineHomotopyUnitIdComparison A)).hom ≫
      (Functor.rightUnitor
        (affineBoundedAboveProjectiveHomotopyPullback f)).hom = 𝟙 _ := by
  exact affineBoundedAboveProjectiveHomotopyPullback_rightUnitality f

set_option linter.defProp false in
private def affineQhTransport_leftUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :=
  Pseudofunctor.equivalenceTransport_leftUnitality
    (boundedAboveProjectiveQhEquivalence (ModuleCat R))
    (boundedAboveProjectiveQhEquivalence (ModuleCat A))
    (affineBoundedAboveProjectiveHomotopyPullback (𝟙 R : R ⟶ R))
    (mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat R)))
    (affineBoundedAboveProjectiveHomotopyPullback f)
    (affineHomotopyUnitComparison R)
    (affineHomotopyUnitIdComparison R)
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso (𝟙 R) f)
    (affineHomotopyPullback_leftUnitality_twoStage f)

/-- The supported affine derived compositor and unit satisfy the left
triangle equation. -/
theorem affineBoundedAboveProjectiveDerivedPullback_leftUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveDerivedPullbackCompIso (𝟙 R) f).symm.hom ≫
      Functor.whiskerRight
        (affineBoundedAboveProjectiveDerivedPullbackIdIso R).hom _ ≫
      (Functor.leftUnitor
        (affineBoundedAboveProjectiveDerivedPullback f)).hom = 𝟙 _ := by
  simp only [affineDerivedPullbackCompIso_eq_equivalenceTransport,
    affineDerivedPullbackIdIso_eq_equivalenceTransport,
    affineDerivedPullback_eq_equivalenceTransport]
  exact affineQhTransport_leftUnitality f

set_option linter.defProp false in
private def affineQhTransport_rightUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :=
  Pseudofunctor.equivalenceTransport_rightUnitality
    (boundedAboveProjectiveQhEquivalence (ModuleCat R))
    (boundedAboveProjectiveQhEquivalence (ModuleCat A))
    (affineBoundedAboveProjectiveHomotopyPullback f)
    (affineBoundedAboveProjectiveHomotopyPullback (𝟙 A : A ⟶ A))
    (mapBoundedAboveProjectiveHomotopy (𝟭 (ModuleCat A)))
    (affineHomotopyUnitComparison A)
    (affineHomotopyUnitIdComparison A)
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso f (𝟙 A))
    (affineHomotopyPullback_rightUnitality_twoStage f)

/-- The supported affine derived compositor and unit satisfy the right
triangle equation. -/
theorem affineBoundedAboveProjectiveDerivedPullback_rightUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveDerivedPullbackCompIso f (𝟙 A)).symm.hom ≫
      Functor.whiskerLeft (affineBoundedAboveProjectiveDerivedPullback f)
        (affineBoundedAboveProjectiveDerivedPullbackIdIso A).hom ≫
      (Functor.rightUnitor
        (affineBoundedAboveProjectiveDerivedPullback f)).hom = 𝟙 _ := by
  simp only [affineDerivedPullbackCompIso_eq_equivalenceTransport,
    affineDerivedPullbackIdIso_eq_equivalenceTransport,
    affineDerivedPullback_eq_equivalenceTransport]
  exact affineQhTransport_rightUnitality f

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary affine pullback on the bounded-above projective derived loci,
packaged with its transported unit, compositor, pentagon, and triangle
equations. -/
def affineBoundedAboveProjectiveDerivedPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u + 1, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of
      (BoundedAboveProjectiveDerivedCategory (ModuleCat.{u} R)))
    (fun f ↦ (affineBoundedAboveProjectiveDerivedPullback f).toCatHom)
    (fun R ↦ Cat.Hom.isoMk
      (affineBoundedAboveProjectiveDerivedPullbackIdIso R))
    (fun f g ↦ Cat.Hom.isoMk
      (affineBoundedAboveProjectiveDerivedPullbackCompIso f g).symm) ?_ ?_ ?_
  · intros R A B C f g h
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change BoundedAboveProjectiveDerivedCategory (ModuleCat.{u} R) at K
    exact NatTrans.congr_app
      (affineBoundedAboveProjectiveDerivedPullback_associativity f g h) K
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change BoundedAboveProjectiveDerivedCategory (ModuleCat.{u} R) at K
    exact NatTrans.congr_app
      (affineBoundedAboveProjectiveDerivedPullback_leftUnitality f) K
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change BoundedAboveProjectiveDerivedCategory (ModuleCat.{u} R) at K
    exact NatTrans.congr_app
      (affineBoundedAboveProjectiveDerivedPullback_rightUnitality f) K

end

end AlgebraicGeometry.DerivedCategory.Dqc
