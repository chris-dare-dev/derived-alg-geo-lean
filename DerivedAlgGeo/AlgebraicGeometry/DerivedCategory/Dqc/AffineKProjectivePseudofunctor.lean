/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectiveUnitality

/-!
# Coherence for the affine bounded-projective pullback lane

The extension-of-scalars pentagon is first transported to cochain complexes
and then through the homotopy quotient. This supplies the main higher
coherence equation needed to package the affine supported pullbacks as a
pseudofunctor.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Bicategory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- The extension-of-scalars pentagon transported degreewise to cochain
complexes. -/
theorem affineExtendScalarsComplex_associativity
    {R A B C : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) (h : B ⟶ C) :
    NatTrans.mapHomologicalComplex
      ((ModuleCat.extendScalarsComp (g.hom.comp f.hom) h.hom).hom ≫
        Functor.whiskerRight (ModuleCat.extendScalarsComp f.hom g.hom).hom _ ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (ModuleCat.extendScalarsComp g.hom h.hom).inv ≫
        (ModuleCat.extendScalarsComp f.hom (h.hom.comp g.hom)).inv)
      (ComplexShape.up ℤ) =
      NatTrans.mapHomologicalComplex (𝟙 _) (ComplexShape.up ℤ) :=
  congrArg (fun α ↦ NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
    (ModuleCat.extendScalars_assoc' f.hom g.hom h.hom)

/-- The left unit equation for extension of scalars transported degreewise
to cochain complexes. -/
theorem affineExtendScalarsComplex_leftUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    NatTrans.mapHomologicalComplex
      ((ModuleCat.extendScalarsComp (RingHom.id R) f.hom).hom ≫
        Functor.whiskerRight (ModuleCat.extendScalarsId R).hom _ ≫
        (Functor.leftUnitor _).hom)
      (ComplexShape.up ℤ) =
      NatTrans.mapHomologicalComplex (𝟙 _) (ComplexShape.up ℤ) :=
  congrArg (fun α ↦ NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
    (ModuleCat.extendScalars_id_comp (R₁ := R) (f₁₂ := f.hom))

/-- The right unit equation for extension of scalars transported degreewise
to cochain complexes. -/
theorem affineExtendScalarsComplex_rightUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    NatTrans.mapHomologicalComplex
      ((ModuleCat.extendScalarsComp f.hom (RingHom.id A)).hom ≫
        Functor.whiskerLeft _ (ModuleCat.extendScalarsId A).hom ≫
        (Functor.rightUnitor _).hom)
      (ComplexShape.up ℤ) =
      NatTrans.mapHomologicalComplex (𝟙 _) (ComplexShape.up ℤ) :=
  congrArg (fun α ↦ NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
    (ModuleCat.extendScalars_comp_id (R₂ := A) (f₁₂ := f.hom))

/-- The affine compositor on bounded-above projective homotopy
representatives satisfies the pentagon equation. -/
theorem affineBoundedAboveProjectiveHomotopyPullback_associativity
    {R A B C : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) (h : B ⟶ C) :
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso (f ≫ g) h).symm.hom ≫
      Functor.whiskerRight
        (affineBoundedAboveProjectiveHomotopyPullbackCompIso f g).symm.hom _ ≫
      (Functor.associator
        (affineBoundedAboveProjectiveHomotopyPullback f)
        (affineBoundedAboveProjectiveHomotopyPullback g)
        (affineBoundedAboveProjectiveHomotopyPullback h)).hom ≫
      Functor.whiskerLeft (affineBoundedAboveProjectiveHomotopyPullback f)
        (affineBoundedAboveProjectiveHomotopyPullbackCompIso g h).hom ≫
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso f (g ≫ h)).hom =
        𝟙 _ := by
  ext K
  rcases K with ⟨⟨K⟩, hK⟩
  have hComplex := NatTrans.congr_app
    (affineExtendScalarsComplex_associativity f g h) K
  have hQuotient := congrArg
    (fun k ↦ (HomotopyCategory.quotient (ModuleCat C)
      (ComplexShape.up ℤ)).map k) hComplex
  change
    (HomotopyCategory.quotient (ModuleCat C) (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex
        ((ModuleCat.extendScalarsComp (g.hom.comp f.hom) h.hom).hom ≫
          Functor.whiskerRight
            (ModuleCat.extendScalarsComp f.hom g.hom).hom _ ≫
          (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft _
            (ModuleCat.extendScalarsComp g.hom h.hom).inv ≫
          (ModuleCat.extendScalarsComp f.hom (h.hom.comp g.hom)).inv)
        (ComplexShape.up ℤ)).app K) =
    (HomotopyCategory.quotient (ModuleCat C) (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (𝟙 _) (ComplexShape.up ℤ)).app K)
  exact hQuotient

/-- The affine compositor and unit satisfy the left triangle equation on
bounded-above projective homotopy representatives. -/
theorem affineBoundedAboveProjectiveHomotopyPullback_leftUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso (𝟙 R) f).symm.hom ≫
      Functor.whiskerRight
        (affineBoundedAboveProjectiveHomotopyPullbackIdIso R).hom _ ≫
      (Functor.leftUnitor
        (affineBoundedAboveProjectiveHomotopyPullback f)).hom = 𝟙 _ := by
  ext K
  rcases K with ⟨⟨K⟩, hK⟩
  have hComplex := NatTrans.congr_app
    (affineExtendScalarsComplex_leftUnitality f) K
  have hQuotient := congrArg
    (fun k ↦ (HomotopyCategory.quotient (ModuleCat A)
      (ComplexShape.up ℤ)).map k) hComplex
  change
    (HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex
        ((ModuleCat.extendScalarsComp (RingHom.id R) f.hom).hom ≫
          Functor.whiskerRight (ModuleCat.extendScalarsId R).hom _ ≫
          (Functor.leftUnitor _).hom)
        (ComplexShape.up ℤ)).app K) =
    (HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (𝟙 _) (ComplexShape.up ℤ)).app K)
  exact hQuotient

/-- The affine compositor and unit satisfy the right triangle equation on
bounded-above projective homotopy representatives. -/
theorem affineBoundedAboveProjectiveHomotopyPullback_rightUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineBoundedAboveProjectiveHomotopyPullbackCompIso f (𝟙 A)).symm.hom ≫
      Functor.whiskerLeft (affineBoundedAboveProjectiveHomotopyPullback f)
        (affineBoundedAboveProjectiveHomotopyPullbackIdIso A).hom ≫
      (Functor.rightUnitor
        (affineBoundedAboveProjectiveHomotopyPullback f)).hom = 𝟙 _ := by
  ext K
  rcases K with ⟨⟨K⟩, hK⟩
  have hComplex := NatTrans.congr_app
    (affineExtendScalarsComplex_rightUnitality f) K
  have hQuotient := congrArg
    (fun k ↦ (HomotopyCategory.quotient (ModuleCat A)
      (ComplexShape.up ℤ)).map k) hComplex
  change
    (HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex
        ((ModuleCat.extendScalarsComp f.hom (RingHom.id A)).hom ≫
          Functor.whiskerLeft _ (ModuleCat.extendScalarsId A).hom ≫
          (Functor.rightUnitor _).hom)
        (ComplexShape.up ℤ)).app K) =
    (HomotopyCategory.quotient (ModuleCat A) (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (𝟙 _) (ComplexShape.up ℤ)).app K)
  exact hQuotient

set_option backward.isDefEq.respectTransparency false in
/-- Arbitrary affine extension of scalars on bounded-above projective
homotopy representatives, packaged with its proved unit, compositor,
pentagon, and triangle equations. -/
def affineBoundedAboveProjectiveHomotopyPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of
      (BoundedAboveProjectiveHomotopyCategory (ModuleCat.{u} R)))
    (fun f ↦ (affineBoundedAboveProjectiveHomotopyPullback f).toCatHom)
    (fun R ↦ Cat.Hom.isoMk
      (affineBoundedAboveProjectiveHomotopyPullbackIdIso R))
    (fun f g ↦ Cat.Hom.isoMk
      (affineBoundedAboveProjectiveHomotopyPullbackCompIso f g).symm) ?_ ?_ ?_
  · intros R A B C f g h
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change BoundedAboveProjectiveHomotopyCategory (ModuleCat.{u} R) at K
    exact NatTrans.congr_app
      (affineBoundedAboveProjectiveHomotopyPullback_associativity f g h) K
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change BoundedAboveProjectiveHomotopyCategory (ModuleCat.{u} R) at K
    exact NatTrans.congr_app
      (affineBoundedAboveProjectiveHomotopyPullback_leftUnitality f) K
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change BoundedAboveProjectiveHomotopyCategory (ModuleCat.{u} R) at K
    exact NatTrans.congr_app
      (affineBoundedAboveProjectiveHomotopyPullback_rightUnitality f) K

end

end CategoryTheory.Triangulated.StabilityCondition.Families
