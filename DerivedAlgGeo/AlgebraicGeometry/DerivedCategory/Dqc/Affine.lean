/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.CategoryTheory.Abelian.Transfer
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc

/-!
# The affine quasi-coherent derived category

On an affine scheme, Mathlib proves that quasi-coherent module sheaves are
equivalent to modules over the coordinate ring.  This file uses that theorem
to put the genuine full category of quasi-coherent sheaves on `Spec R` in the
abelian setting and then forms its derived category.

This is a concrete prerequisite for the general `Dqc` realization.  It does
not identify this derived category with the quasi-coherent-cohomology locus in
the derived category of all sheaves: that unbounded derived essential
surjectivity theorem is not currently available in Mathlib.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/-- The actual category of quasi-coherent module sheaves on `Spec R`. -/
abbrev AffineQuasicoherentSheaves (R : CommRingCat.{u}) :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).FullSubcategory

/-- Finite products on affine quasi-coherent sheaves are transported across
the tilde equivalence, rather than postulated on the full subcategory. -/
noncomputable instance affineQuasicoherentSheavesHasFiniteProducts
    (R : CommRingCat.{u}) : HasFiniteProducts (AffineQuasicoherentSheaves R) :=
  ⟨fun _ ↦ Adjunction.hasLimitsOfShape_of_equivalence
    (tildeEquiv (R := R)).inverse⟩

/-- On an affine scheme, quasi-coherent sheaves form an abelian category by
the proved tilde equivalence with modules over the coordinate ring. -/
noncomputable instance affineQuasicoherentSheavesAbelian
    (R : CommRingCat.{u}) : Abelian (AffineQuasicoherentSheaves R) :=
  abelianOfEquivalence (tildeEquiv (R := R)).inverse

attribute [local instance] HasDerivedCategory.standard

/-- The derived category of the genuine abelian category of quasi-coherent
sheaves on an affine scheme. -/
abbrev AffineQuasicoherentDerivedCategory (R : CommRingCat.{u}) :=
  DerivedCategory (AffineQuasicoherentSheaves R)

/-- The affine quasi-coherent derived category is genuinely triangulated. -/
theorem affineQuasicoherentDerivedCategory_isTriangulated
    (R : CommRingCat.{u}) :
    IsTriangulated (AffineQuasicoherentDerivedCategory R) :=
  inferInstance

/-- The tilde equivalence is the concrete affine realization of
quasi-coherent sheaves; no all-sheaf category occurs in this equivalence. -/
def affineQuasicoherentSheavesEquiv (R : CommRingCat.{u}) :
    ModuleCat R ≌ AffineQuasicoherentSheaves R :=
  tildeEquiv (R := R)

noncomputable instance affineQuasicoherentSheavesEquiv_functor_additive
    (R : CommRingCat.{u}) :
    (affineQuasicoherentSheavesEquiv R).functor.Additive where
  map_add {X Y} f g := by
    apply ObjectProperty.hom_ext
    exact (tilde.functor R).map_add

noncomputable instance affineQuasicoherentSheavesEquiv_inverse_additive
    (R : CommRingCat.{u}) :
    (affineQuasicoherentSheavesEquiv R).inverse.Additive :=
  inferInstance

/-- The derived tilde functor from complexes of coordinate-ring modules to
the derived category of genuine quasi-coherent sheaves. -/
noncomputable def affineTildeDerivedFunctor (R : CommRingCat.{u}) :
    DerivedCategory (ModuleCat R) ⥤
      AffineQuasicoherentDerivedCategory R :=
  (affineQuasicoherentSheavesEquiv R).functor.mapDerivedCategory

/-- The derived global-sections functor in the opposite direction.  The
quasi-inverse theorem is proved in `Dqc.AffineDerivedEquivalence`. -/
noncomputable def affineGammaDerivedFunctor (R : CommRingCat.{u}) :
    AffineQuasicoherentDerivedCategory R ⥤
      DerivedCategory (ModuleCat R) :=
  (affineQuasicoherentSheavesEquiv R).inverse.mapDerivedCategory

/-- Derived tilde commutes with every canonical cohomology functor. -/
noncomputable def affineTildeDerivedHomologyIso
    (R : CommRingCat.{u}) (E : DerivedCategory (ModuleCat R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (AffineQuasicoherentSheaves R) n).obj
        ((affineTildeDerivedFunctor R).obj E) ≅
      (affineQuasicoherentSheavesEquiv R).functor.obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj E) :=
  by
    change
      (DerivedCategory.homologyFunctor (AffineQuasicoherentSheaves R) n).obj
          ((affineQuasicoherentSheavesEquiv R).functor.mapDerivedCategory.obj E) ≅
        (affineQuasicoherentSheavesEquiv R).functor.obj
          ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj E)
    exact mapDerivedCategoryHomologyIso
      (affineQuasicoherentSheavesEquiv R).functor
      (by infer_instance) (by infer_instance) (by infer_instance) E n

/-- Derived global sections commutes with every canonical cohomology
functor. -/
noncomputable def affineGammaDerivedHomologyIso
    (R : CommRingCat.{u}) (E : AffineQuasicoherentDerivedCategory R) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) n).obj
        ((affineGammaDerivedFunctor R).obj E) ≅
      (affineQuasicoherentSheavesEquiv R).inverse.obj
        ((DerivedCategory.homologyFunctor (AffineQuasicoherentSheaves R) n).obj E) :=
  by
    change
      (DerivedCategory.homologyFunctor (ModuleCat R) n).obj
          ((affineQuasicoherentSheavesEquiv R).inverse.mapDerivedCategory.obj E) ≅
        (affineQuasicoherentSheavesEquiv R).inverse.obj
          ((DerivedCategory.homologyFunctor (AffineQuasicoherentSheaves R) n).obj E)
    exact mapDerivedCategoryHomologyIso
      (affineQuasicoherentSheavesEquiv R).inverse
      (by infer_instance) (by infer_instance) (by infer_instance) E n

end

end AlgebraicGeometry.DerivedCategory.Dqc
