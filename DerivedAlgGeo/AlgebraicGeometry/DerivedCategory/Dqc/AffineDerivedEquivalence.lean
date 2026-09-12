/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Localization.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.Affine

/-!
# The affine quasi-coherent derived equivalence

The affine tilde equivalence is exact, so its functor and inverse preserve
quasi-isomorphisms of cochain complexes.  The resulting functors on derived
categories are quasi-inverse.  This identifies the genuine derived category
of quasi-coherent sheaves on `Spec R` with the derived category of `R`-modules.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

private abbrev affineTildeComplexFunctor (R : CommRingCat.{u}) :=
  (affineQuasicoherentSheavesEquiv R).functor.mapHomologicalComplex
    (ComplexShape.up ℤ)

private abbrev affineGammaComplexFunctor (R : CommRingCat.{u}) :=
  (affineQuasicoherentSheavesEquiv R).inverse.mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- On localized cochain complexes, derived tilde followed by derived global
sections is canonically the identity. -/
private def affineDerivedUnitComparison (R : CommRingCat.{u}) :
    (affineTildeComplexFunctor R ⋙
        DerivedCategory.Q (C := AffineQuasicoherentSheaves R)) ⋙
        affineGammaDerivedFunctor R ≅
      DerivedCategory.Q (C := ModuleCat R) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (affineTildeComplexFunctor R)
      ((affineQuasicoherentSheavesEquiv R).inverse.mapDerivedCategoryFactors) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (affineQuasicoherentSheavesEquiv R).unitIso.symm
        (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := ModuleCat R)) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso (ModuleCat R) (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := ModuleCat R)) ≪≫
    Functor.leftUnitor _

/-- On localized cochain complexes, derived global sections followed by
derived tilde is canonically the identity. -/
private def affineDerivedCounitComparison (R : CommRingCat.{u}) :
    (affineGammaComplexFunctor R ⋙
        DerivedCategory.Q (C := ModuleCat R)) ⋙
        affineTildeDerivedFunctor R ≅
      DerivedCategory.Q (C := AffineQuasicoherentSheaves R) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (affineGammaComplexFunctor R)
      ((affineQuasicoherentSheavesEquiv R).functor.mapDerivedCategoryFactors) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexCompIso
        (affineQuasicoherentSheavesEquiv R).counitIso
        (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := AffineQuasicoherentSheaves R)) ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomologicalComplexIdIso
        (AffineQuasicoherentSheaves R) (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := AffineQuasicoherentSheaves R)) ≪≫
    Functor.leftUnitor _

/-- The derived tilde functor is an equivalence between the derived category
of coordinate-ring modules and the genuine derived category of
quasi-coherent sheaves on the affine spectrum. -/
noncomputable def affineQuasicoherentDerivedEquivalence
    (R : CommRingCat.{u}) :
    DerivedCategory (ModuleCat R) ≌ AffineQuasicoherentDerivedCategory R := by
  letI : Localization.Lifting
      (DerivedCategory.Q (C := ModuleCat R))
      (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ))
      (affineTildeComplexFunctor R ⋙
        DerivedCategory.Q (C := AffineQuasicoherentSheaves R))
      (affineTildeDerivedFunctor R) :=
    ⟨(affineQuasicoherentSheavesEquiv R).functor.mapDerivedCategoryFactors⟩
  letI : Localization.Lifting
      (DerivedCategory.Q (C := AffineQuasicoherentSheaves R))
      (HomologicalComplex.quasiIso
        (AffineQuasicoherentSheaves R) (ComplexShape.up ℤ))
      (affineGammaComplexFunctor R ⋙
        DerivedCategory.Q (C := ModuleCat R))
      (affineGammaDerivedFunctor R) :=
    ⟨(affineQuasicoherentSheavesEquiv R).inverse.mapDerivedCategoryFactors⟩
  exact Localization.equivalence
    (DerivedCategory.Q (C := ModuleCat R))
    (HomologicalComplex.quasiIso (ModuleCat R) (ComplexShape.up ℤ))
    (DerivedCategory.Q (C := AffineQuasicoherentSheaves R))
    (HomologicalComplex.quasiIso
      (AffineQuasicoherentSheaves R) (ComplexShape.up ℤ))
    (affineTildeComplexFunctor R ⋙
      DerivedCategory.Q (C := AffineQuasicoherentSheaves R))
    (affineTildeDerivedFunctor R)
    (affineGammaComplexFunctor R ⋙
      DerivedCategory.Q (C := ModuleCat R))
    (affineGammaDerivedFunctor R)
    (affineDerivedUnitComparison R)
    (affineDerivedCounitComparison R)

@[simp]
theorem affineQuasicoherentDerivedEquivalence_functor
    (R : CommRingCat.{u}) :
    (affineQuasicoherentDerivedEquivalence R).functor =
      affineTildeDerivedFunctor R :=
  rfl

@[simp]
theorem affineQuasicoherentDerivedEquivalence_inverse
    (R : CommRingCat.{u}) :
    (affineQuasicoherentDerivedEquivalence R).inverse =
      affineGammaDerivedFunctor R :=
  rfl

/-- The cohomologically bounded derived category of genuine quasi-coherent
sheaves on an affine spectrum. -/
abbrev AffineQuasicoherentBoundedDerivedCategory (R : CommRingCat.{u}) :=
  DerivedCategory.Bounded (AffineQuasicoherentSheaves R)

/-- The affine derived tilde equivalence detects cohomological boundedness.
Both directions follow from exactness of the abelian tilde equivalence. -/
theorem affineQuasicoherentDerivedEquivalence_bounded_inverseImage
    (R : CommRingCat.{u}) :
    (DerivedCategory.TStructure.t
        (C := AffineQuasicoherentSheaves R)).bounded.inverseImage
        (affineQuasicoherentDerivedEquivalence R).functor =
      (DerivedCategory.TStructure.t (C := ModuleCat R)).bounded := by
  ext E
  constructor
  · intro hE
    change (DerivedCategory.TStructure.t
      (C := AffineQuasicoherentSheaves R)).bounded
        (((affineQuasicoherentSheavesEquiv R).functor.mapDerivedCategory).obj E) at hE
    have hE' := mapDerivedCategory_bounded
      (affineQuasicoherentSheavesEquiv R).inverse _ hE
    exact (DerivedCategory.TStructure.t (C := ModuleCat R)).bounded.prop_of_iso
      ((affineQuasicoherentDerivedEquivalence R).unitIso.app E).symm hE'
  · intro hE
    change (DerivedCategory.TStructure.t
      (C := AffineQuasicoherentSheaves R)).bounded
        (((affineQuasicoherentSheavesEquiv R).functor.mapDerivedCategory).obj E)
    exact mapDerivedCategory_bounded
      (affineQuasicoherentSheavesEquiv R).functor E hE

/-- The affine quasi-coherent derived equivalence restricted to
cohomologically bounded objects. -/
def affineQuasicoherentBoundedDerivedEquivalence (R : CommRingCat.{u}) :
    DerivedCategory.Bounded (ModuleCat R) ≌
      AffineQuasicoherentBoundedDerivedCategory R :=
  (affineQuasicoherentDerivedEquivalence R).congrFullSubcategory
    (affineQuasicoherentDerivedEquivalence_bounded_inverseImage R)

end

end AlgebraicGeometry.DerivedCategory.Dqc
