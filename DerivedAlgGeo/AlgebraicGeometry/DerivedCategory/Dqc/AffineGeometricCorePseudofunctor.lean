/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Core
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineGeometricPseudofunctor

/-!
# The groupoid-valued affine geometric pullback pseudofunctor

This file takes the maximal subgroupoid of the geometric affine
bounded-above projective derived locus.  Objects remain genuine
quasi-coherent complexes on affine schemes, while morphisms are restricted
to isomorphisms as required by a moduli problem.

The transition functors, unit, and compositor are induced from the geometric
affine pseudofunctor.  Their coherence is proved from the corresponding
derived-category pentagon and triangle identities.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Bicategory AlgebraicGeometry

noncomputable section

universe u v w

@[simp]
private theorem coreToCatHom_obj_of
    {C D : Type w} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (X : Core C) :
    ((F.core.toCatHom).toFunctor.obj X).of = F.obj X.of :=
  rfl

@[simp]
private theorem coreToCatHom_map_iso_hom
    {C D : Type w} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {X Y : Core C} (f : X ⟶ Y) :
    (((F.core.toCatHom).toFunctor.map f).iso.hom) = F.map f.iso.hom :=
  rfl

/-- The groupoid of geometric affine bounded-above projective derived
objects over `Spec R`. -/
abbrev AffineBoundedAboveProjectiveModuliFiber (R : CommRingCat.{u}) :=
  Core (AffineBoundedAboveProjectiveQuasicoherentDerivedCategory R)

/-- Arbitrary affine pullback on the maximal subgroupoids of the geometric
bounded-above projective loci. -/
noncomputable def affineGeometricBoundedAboveProjectiveCorePullback
    {R A : CommRingCat.{u}} (f : R ⟶ A) :
    AffineBoundedAboveProjectiveModuliFiber R ⥤
      AffineBoundedAboveProjectiveModuliFiber A :=
  (affineGeometricBoundedAboveProjectiveDerivedPullback f).core

/-- The unit comparison after passing geometric affine pullback to maximal
subgroupoids. -/
noncomputable def affineGeometricBoundedAboveProjectiveCorePullbackIdIso
    (R : CommRingCat.{u}) :
    affineGeometricBoundedAboveProjectiveCorePullback (𝟙 R : R ⟶ R) ≅
      𝟭 (AffineBoundedAboveProjectiveModuliFiber R) :=
  (affineGeometricBoundedAboveProjectiveDerivedPullbackIdIso R).core

/-- The compositor after passing geometric affine pullback to maximal
subgroupoids, oriented as required by `LocallyDiscrete.mkPseudofunctor`. -/
noncomputable def affineGeometricBoundedAboveProjectiveCorePullbackCompIso
    {R A B : CommRingCat.{u}} (f : R ⟶ A) (g : A ⟶ B) :
    affineGeometricBoundedAboveProjectiveCorePullback (f ≫ g) ≅
      affineGeometricBoundedAboveProjectiveCorePullback f ⋙
        affineGeometricBoundedAboveProjectiveCorePullback g :=
  (affineGeometricBoundedAboveProjectiveDerivedPullbackCompIso f g).symm.core

set_option backward.isDefEq.respectTransparency false in
/-- The genuine geometric affine bounded-above projective moduli groupoids
and their arbitrary pullbacks, packaged as a Cat-valued pseudofunctor. -/
noncomputable def affineGeometricBoundedAboveProjectiveCorePseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u + 1, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of (AffineBoundedAboveProjectiveModuliFiber R))
    (fun f ↦
      (affineGeometricBoundedAboveProjectiveCorePullback f).toCatHom)
    (fun R ↦ Cat.Hom.isoMk
      (affineGeometricBoundedAboveProjectiveCorePullbackIdIso R))
    (fun f g ↦ Cat.Hom.isoMk
      (affineGeometricBoundedAboveProjectiveCorePullbackCompIso f g))
    ?_ ?_ ?_
  · intros R A B C f g h
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    apply Core.hom_ext
    simpa [affineGeometricBoundedAboveProjectiveCorePullbackCompIso,
      affineGeometricBoundedAboveProjectiveCorePullback,
      Cat.Hom.isoMk, Iso.core_hom_app_iso_hom,
      Iso.core_inv_app_iso_hom, Functor.core_obj_of,
      Functor.core_map_iso_hom, Functor.coreComp_hom_app_iso_hom,
      Functor.coreComp_inv_app_iso_hom, Functor.map_id,
      Category.id_comp, Category.comp_id, Category.assoc] using
      NatTrans.congr_app
        (affineGeometricBoundedAboveProjectiveDerivedPullback_associativity
          f g h) K.of
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    apply Core.hom_ext
    simpa [affineGeometricBoundedAboveProjectiveCorePullbackCompIso,
      affineGeometricBoundedAboveProjectiveCorePullbackIdIso,
      affineGeometricBoundedAboveProjectiveCorePullback,
      Cat.Hom.isoMk, Iso.core_hom_app_iso_hom,
      Iso.core_inv_app_iso_hom, Functor.core_obj_of,
      Functor.core_map_iso_hom, Functor.coreComp_hom_app_iso_hom,
      Functor.coreComp_inv_app_iso_hom,
      Functor.coreId_hom_app_iso_hom,
      Functor.coreId_inv_app_iso_hom, Functor.map_id,
      Category.id_comp, Category.comp_id, Category.assoc] using
      NatTrans.congr_app
        (affineGeometricBoundedAboveProjectiveDerivedPullback_leftUnitality f)
        K.of
  · intros R A f
    apply Cat.Hom₂.ext
    dsimp [Cat.Hom.isoMk]
    apply NatTrans.ext
    funext K
    apply Core.hom_ext
    simpa [affineGeometricBoundedAboveProjectiveCorePullbackCompIso,
      affineGeometricBoundedAboveProjectiveCorePullbackIdIso,
      affineGeometricBoundedAboveProjectiveCorePullback,
      Cat.Hom.isoMk, Iso.core_hom_app_iso_hom,
      Iso.core_inv_app_iso_hom, Functor.core_obj_of,
      Functor.core_map_iso_hom, Functor.coreComp_hom_app_iso_hom,
      Functor.coreComp_inv_app_iso_hom,
      Functor.coreId_hom_app_iso_hom,
      Functor.coreId_inv_app_iso_hom, Functor.map_id,
      Category.id_comp, Category.comp_id, Category.assoc] using
      NatTrans.congr_app
        (affineGeometricBoundedAboveProjectiveDerivedPullback_rightUnitality f)
        K.of

/-- Forgetting the affine moduli groupoid to the honest geometric derived
locus. -/
noncomputable def affineBoundedAboveProjectiveModuliForget
    (R : CommRingCat.{u}) :
    AffineBoundedAboveProjectiveModuliFiber R ⥤
      SchemeQuasicoherentDerivedCategory (Spec R) :=
  Core.inclusion _ ⋙ affineGeometricBoundedAboveProjectiveDerivedToDqc R

end

end CategoryTheory.Triangulated.StabilityCondition.Families
