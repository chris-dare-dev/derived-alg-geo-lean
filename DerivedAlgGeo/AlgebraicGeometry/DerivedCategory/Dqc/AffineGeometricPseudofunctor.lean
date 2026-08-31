/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Pseudofunctor.Transport
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectiveDerivedPseudofunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineRealization

/-!
# The geometric affine bounded-projective pseudofunctor

The bounded-above projective derived locus was initially constructed in the
derived category of modules over the coordinate ring.  This file realizes
that locus as a genuine full subcategory of the derived category of
quasi-coherent sheaves on the affine spectrum.  The module-side pullback
pseudofunctor is then transported across the resulting objectwise
equivalences.

Finally, the geometric locus is mapped into the honest `Dqc(Spec R)` category
by the exact affine realization functor.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry
open CategoryTheory.Pseudofunctor

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Realize the module-side bounded-above projective derived locus in the
derived category of quasi-coherent sheaves on the affine spectrum. -/
noncomputable def affineBoundedAboveProjectiveQuasicoherentRealization
    (R : CommRingCat.{u}) :
    BoundedAboveProjectiveDerivedCategory (ModuleCat R) ⥤
      AffineQuasicoherentDerivedCategory R :=
  ObjectProperty.ι (boundedAboveProjectiveQh (ModuleCat R)).essImage ⋙
    (affineQuasicoherentDerivedEquivalence R).functor

instance affineBoundedAboveProjectiveQuasicoherentRealization_full
    (R : CommRingCat.{u}) :
    (affineBoundedAboveProjectiveQuasicoherentRealization R).Full := by
  letI : (affineQuasicoherentDerivedEquivalence R).functor.Full :=
    inferInstance
  exact Functor.Full.comp _ _

instance affineBoundedAboveProjectiveQuasicoherentRealization_faithful
    (R : CommRingCat.{u}) :
    (affineBoundedAboveProjectiveQuasicoherentRealization R).Faithful := by
  letI : (affineQuasicoherentDerivedEquivalence R).functor.Faithful :=
    inferInstance
  exact Functor.Faithful.comp _ _

/-- The full geometric affine derived locus represented by bounded-above
complexes of projective coordinate-ring modules. -/
abbrev AffineBoundedAboveProjectiveQuasicoherentDerivedCategory
    (R : CommRingCat.{u}) :=
  (affineBoundedAboveProjectiveQuasicoherentRealization R).EssImageSubcategory

/-- The module-side bounded-above projective locus is equivalent to its
geometric realization in affine quasi-coherent complexes. -/
noncomputable def affineBoundedAboveProjectiveQuasicoherentEquivalence
    (R : CommRingCat.{u}) :
    BoundedAboveProjectiveDerivedCategory (ModuleCat R) ≌
      AffineBoundedAboveProjectiveQuasicoherentDerivedCategory R := by
  letI :
      (affineBoundedAboveProjectiveQuasicoherentRealization R).toEssImage.IsEquivalence := {
    faithful := inferInstance
    full := inferInstance
    essSurj := inferInstance }
  exact
    (affineBoundedAboveProjectiveQuasicoherentRealization R).toEssImage.asEquivalence

/-- Arbitrary affine pullback on the geometric bounded-above projective
derived loci. -/
noncomputable def affineGeometricBoundedAboveProjectiveDerivedPullback
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    AffineBoundedAboveProjectiveQuasicoherentDerivedCategory R ⥤
      AffineBoundedAboveProjectiveQuasicoherentDerivedCategory A :=
  equivalenceTransportFunctor
    (affineBoundedAboveProjectiveQuasicoherentEquivalence R)
    (affineBoundedAboveProjectiveQuasicoherentEquivalence A)
    (affineBoundedAboveProjectiveDerivedPullback f)

/-- The compositor for geometric affine bounded-above projective pullback. -/
noncomputable def affineGeometricBoundedAboveProjectiveDerivedPullbackCompIso
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) :
    affineGeometricBoundedAboveProjectiveDerivedPullback f ⋙
        affineGeometricBoundedAboveProjectiveDerivedPullback g ≅
      affineGeometricBoundedAboveProjectiveDerivedPullback (f ≫ g) :=
  equivalenceTransportCompIso
    (affineBoundedAboveProjectiveQuasicoherentEquivalence R)
    (affineBoundedAboveProjectiveQuasicoherentEquivalence A)
    (affineBoundedAboveProjectiveQuasicoherentEquivalence B)
    (affineBoundedAboveProjectiveDerivedPullback f)
    (affineBoundedAboveProjectiveDerivedPullback g)
    (affineBoundedAboveProjectiveDerivedPullback (f ≫ g))
    (affineBoundedAboveProjectiveDerivedPullbackCompIso f g)

/-- The unit comparison for geometric affine bounded-above projective
pullback. -/
noncomputable def affineGeometricBoundedAboveProjectiveDerivedPullbackIdIso
    (R : CommRingCat.{u}) :
    affineGeometricBoundedAboveProjectiveDerivedPullback (𝟙 R : R ⟶ R) ≅
      𝟭 (AffineBoundedAboveProjectiveQuasicoherentDerivedCategory R) :=
  equivalenceTransportIdIso
    (affineBoundedAboveProjectiveQuasicoherentEquivalence R)
    (affineBoundedAboveProjectiveDerivedPullback (𝟙 R : R ⟶ R))
    (𝟭 (BoundedAboveProjectiveDerivedCategory (ModuleCat R)))
    (affineBoundedAboveProjectiveDerivedPullbackIdIso R)
    (Iso.refl _)

/-- The geometric affine compositors satisfy the pentagon equation. -/
theorem affineGeometricBoundedAboveProjectiveDerivedPullback_associativity
    {R A B C : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) (h : B ⟶ C) :
    (affineGeometricBoundedAboveProjectiveDerivedPullbackCompIso
        (f ≫ g) h).symm.hom ≫
      Functor.whiskerRight
        (affineGeometricBoundedAboveProjectiveDerivedPullbackCompIso
          f g).symm.hom _ ≫
      (Functor.associator
        (affineGeometricBoundedAboveProjectiveDerivedPullback f)
        (affineGeometricBoundedAboveProjectiveDerivedPullback g)
        (affineGeometricBoundedAboveProjectiveDerivedPullback h)).hom ≫
      Functor.whiskerLeft
        (affineGeometricBoundedAboveProjectiveDerivedPullback f)
        (affineGeometricBoundedAboveProjectiveDerivedPullbackCompIso g h).hom ≫
      (affineGeometricBoundedAboveProjectiveDerivedPullbackCompIso
        f (g ≫ h)).hom = 𝟙 _ := by
  exact equivalenceTransport_associativity
    (affineBoundedAboveProjectiveQuasicoherentEquivalence R)
    (affineBoundedAboveProjectiveQuasicoherentEquivalence A)
    (affineBoundedAboveProjectiveQuasicoherentEquivalence B)
    (affineBoundedAboveProjectiveQuasicoherentEquivalence C)
    (affineBoundedAboveProjectiveDerivedPullback f)
    (affineBoundedAboveProjectiveDerivedPullback g)
    (affineBoundedAboveProjectiveDerivedPullback h)
    (affineBoundedAboveProjectiveDerivedPullback (f ≫ g))
    (affineBoundedAboveProjectiveDerivedPullback (g ≫ h))
    (affineBoundedAboveProjectiveDerivedPullback ((f ≫ g) ≫ h))
    (affineBoundedAboveProjectiveDerivedPullbackCompIso f g)
    (affineBoundedAboveProjectiveDerivedPullbackCompIso g h)
    (affineBoundedAboveProjectiveDerivedPullbackCompIso (f ≫ g) h)
    (affineBoundedAboveProjectiveDerivedPullbackCompIso f (g ≫ h))
    (affineBoundedAboveProjectiveDerivedPullback_associativity f g h)

/-- The unit compatibility required to package the transported pullbacks as a
pseudofunctor, obtained from the module-side left triangle. -/
theorem affineGeometricBoundedAboveProjectiveDerivedPullback_leftUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineGeometricBoundedAboveProjectiveDerivedPullbackCompIso
        (𝟙 R) f).symm.hom ≫
      Functor.whiskerRight
        (affineGeometricBoundedAboveProjectiveDerivedPullbackIdIso R).hom _ ≫
      (Functor.leftUnitor
        (affineGeometricBoundedAboveProjectiveDerivedPullback f)).hom =
        𝟙 _ := by
  apply equivalenceTransport_leftUnitality
    (affineBoundedAboveProjectiveQuasicoherentEquivalence R)
    (affineBoundedAboveProjectiveQuasicoherentEquivalence A)
    (affineBoundedAboveProjectiveDerivedPullback (𝟙 R : R ⟶ R))
    (𝟭 (BoundedAboveProjectiveDerivedCategory (ModuleCat R)))
    (affineBoundedAboveProjectiveDerivedPullback f)
    (affineBoundedAboveProjectiveDerivedPullbackIdIso R)
    (Iso.refl _)
    (affineBoundedAboveProjectiveDerivedPullbackCompIso (𝟙 R) f)
  have hrefl :
      (affineBoundedAboveProjectiveDerivedPullbackIdIso R ≪≫
        Iso.refl _).hom =
        (affineBoundedAboveProjectiveDerivedPullbackIdIso R).hom := by
    simp
  rw [hrefl]
  exact affineBoundedAboveProjectiveDerivedPullback_leftUnitality f

/-- The second unit compatibility required to package the transported
pullbacks as a pseudofunctor, obtained from the module-side right triangle. -/
theorem affineGeometricBoundedAboveProjectiveDerivedPullback_rightUnitality
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    (affineGeometricBoundedAboveProjectiveDerivedPullbackCompIso
        f (𝟙 A)).symm.hom ≫
      Functor.whiskerLeft
        (affineGeometricBoundedAboveProjectiveDerivedPullback f)
        (affineGeometricBoundedAboveProjectiveDerivedPullbackIdIso A).hom ≫
      (Functor.rightUnitor
        (affineGeometricBoundedAboveProjectiveDerivedPullback f)).hom =
        𝟙 _ := by
  apply equivalenceTransport_rightUnitality
    (affineBoundedAboveProjectiveQuasicoherentEquivalence R)
    (affineBoundedAboveProjectiveQuasicoherentEquivalence A)
    (affineBoundedAboveProjectiveDerivedPullback f)
    (affineBoundedAboveProjectiveDerivedPullback (𝟙 A : A ⟶ A))
    (𝟭 (BoundedAboveProjectiveDerivedCategory (ModuleCat A)))
    (affineBoundedAboveProjectiveDerivedPullbackIdIso A)
    (Iso.refl _)
    (affineBoundedAboveProjectiveDerivedPullbackCompIso f (𝟙 A))
  have hrefl :
      (affineBoundedAboveProjectiveDerivedPullbackIdIso A ≪≫
        Iso.refl _).hom =
        (affineBoundedAboveProjectiveDerivedPullbackIdIso A).hom := by
    simp
  rw [hrefl]
  exact affineBoundedAboveProjectiveDerivedPullback_rightUnitality f

set_option backward.isDefEq.respectTransparency false in
/-- The genuine geometric affine bounded-above projective loci and their
arbitrary pullbacks, packaged as a pseudofunctor. -/
noncomputable def affineGeometricBoundedAboveProjectiveDerivedPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u + 1, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of
      (AffineBoundedAboveProjectiveQuasicoherentDerivedCategory R))
    (fun f ↦
      (affineGeometricBoundedAboveProjectiveDerivedPullback f).toCatHom)
    (fun R ↦ Cat.Hom.isoMk
      (affineGeometricBoundedAboveProjectiveDerivedPullbackIdIso R))
    (fun f g ↦ Cat.Hom.isoMk
      (affineGeometricBoundedAboveProjectiveDerivedPullbackCompIso f g).symm)
    ?_ ?_ ?_
  · intros R A B C f g h
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change AffineBoundedAboveProjectiveQuasicoherentDerivedCategory R at K
    exact NatTrans.congr_app
      (affineGeometricBoundedAboveProjectiveDerivedPullback_associativity
        f g h) K
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change AffineBoundedAboveProjectiveQuasicoherentDerivedCategory R at K
    exact NatTrans.congr_app
      (affineGeometricBoundedAboveProjectiveDerivedPullback_leftUnitality f) K
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    change AffineBoundedAboveProjectiveQuasicoherentDerivedCategory R at K
    exact NatTrans.congr_app
      (affineGeometricBoundedAboveProjectiveDerivedPullback_rightUnitality f) K

/-- Realization of the geometric bounded-above projective affine locus in the
honest quasi-coherent-cohomology category `Dqc(Spec R)`. -/
noncomputable def affineGeometricBoundedAboveProjectiveDerivedToDqc
    (R : CommRingCat.{u}) :
    AffineBoundedAboveProjectiveQuasicoherentDerivedCategory R ⥤
      SchemeQuasicoherentDerivedCategory (Spec R) :=
  ObjectProperty.ι
      (affineBoundedAboveProjectiveQuasicoherentRealization R).essImage ⋙
    affineQuasicoherentDerivedToDqc R

/-- The geometric realization agrees with the module-side realization after
passing through the objectwise equivalence. -/
noncomputable def
    affineBoundedAboveProjectiveQuasicoherentEquivalenceCompToDqc
    (R : CommRingCat.{u}) :
    (affineBoundedAboveProjectiveQuasicoherentEquivalence R).functor ⋙
        affineGeometricBoundedAboveProjectiveDerivedToDqc R ≅
      affineBoundedAboveProjectiveQuasicoherentRealization R ⋙
        affineQuasicoherentDerivedToDqc R :=
  (Functor.associator
      (affineBoundedAboveProjectiveQuasicoherentEquivalence R).functor
      (ObjectProperty.ι
        (affineBoundedAboveProjectiveQuasicoherentRealization R).essImage)
      (affineQuasicoherentDerivedToDqc R)).symm ≪≫
    Functor.isoWhiskerRight
      ((affineBoundedAboveProjectiveQuasicoherentRealization R).toEssImageCompι)
      (affineQuasicoherentDerivedToDqc R)

end

end AlgebraicGeometry.DerivedCategory.Dqc
