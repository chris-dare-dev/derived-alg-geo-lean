/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.LeftResolution
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.AcyclicGenerators
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor.Bounded
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineVanishing
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.UnitExt
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineRealization

/-!
# The bounded affine quasi-coherent identification

This file proves the affine comparison between the derived category of
quasi-coherent sheaves and the intrinsic bounded `Dqc` locus.  The first
ingredient is an arbitrary-rank free-generator package for
`AffineQuasicoherentSheaves R`.

The unbounded equivalence remains a separate problem: the bounded cone
argument used below requires finite cohomological amplitude.
-/

namespace AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.hasExt_of_hasDerivedCategory
attribute [local instance] affineQuasicoherentSheavesInclusion_additive
  affineQuasicoherentSheavesInclusion_preservesFiniteLimits
  affineQuasicoherentSheavesInclusion_preservesFiniteColimits

local instance affineQuasicoherentSheavesInclusion_full
    (R : CommRingCat.{u}) : (affineQuasicoherentSheavesInclusion R).Full :=
  (SheafOfModules.isQuasicoherent
    (Spec R).ringCatSheaf).fullyFaithfulι.full

local instance affineQuasicoherentSheavesInclusion_faithful
    (R : CommRingCat.{u}) : (affineQuasicoherentSheavesInclusion R).Faithful :=
  (SheafOfModules.isQuasicoherent
    (Spec R).ringCatSheaf).fullyFaithfulι.faithful

/-- The arbitrary-rank free object in affine quasi-coherent sheaves,
transported from the usual free module through the tilde equivalence. -/
noncomputable def affineQuasicoherentFree (R : CommRingCat.{u}) (I : Type u) :
    AffineQuasicoherentSheaves R :=
  (affineQuasicoherentSheavesEquiv R).functor.obj
    ((ModuleCat.free R).obj I)

/-- Arbitrary-rank affine quasi-coherent free sheaves are projective. -/
theorem affineQuasicoherentFree_projective (R : CommRingCat.{u}) (I : Type u) :
    Projective (affineQuasicoherentFree R I) :=
  ((affineQuasicoherentSheavesEquiv R).map_projective_iff
    ((ModuleCat.free R).obj I)).2 inferInstance

/-- The class of arbitrary-rank free affine quasi-coherent sheaves. -/
def affineQuasicoherentFreeObjects (R : CommRingCat.{u}) :
    ObjectProperty (AffineQuasicoherentSheaves R) :=
  fun P ↦ ∃ I : Type u, P = affineQuasicoherentFree R I

/-- Every affine quasi-coherent sheaf is an epimorphic image of an
arbitrary-rank free one. -/
theorem exists_affineQuasicoherentFree_epi (R : CommRingCat.{u})
    (X : AffineQuasicoherentSheaves R) :
    ∃ (P : AffineQuasicoherentSheaves R) (p : P ⟶ X),
      affineQuasicoherentFreeObjects R P ∧ Epi p := by
  let M := (affineQuasicoherentSheavesEquiv R).inverse.obj X
  let I : Type u := M
  let q : (ModuleCat.free R).obj I ⟶ M :=
    (ModuleCat.adj R).counit.app M
  let p : affineQuasicoherentFree R I ⟶ X :=
    (affineQuasicoherentSheavesEquiv R).functor.map q ≫
      (affineQuasicoherentSheavesEquiv R).counitIso.hom.app X
  refine ⟨affineQuasicoherentFree R I, p, ⟨I, rfl⟩, ?_⟩
  dsimp only [p]
  haveI : Epi q := by
    change Epi ((ModuleCat.projectiveResolution R).π.app M)
    infer_instance
  letI : (affineQuasicoherentSheavesEquiv R).functor.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (affineQuasicoherentSheavesEquiv R).toAdjunction
  exact epi_comp'
    (Functor.PreservesEpimorphisms.preserves q)
    (inferInstance : Epi ((affineQuasicoherentSheavesEquiv R).counitIso.hom.app X))

/-- Forgetting an affine quasi-coherent free object identifies it with the
usual free sheaf of modules. -/
noncomputable def affineQuasicoherentFreeInclusionIso
    (R : CommRingCat.{u}) (I : Type u) :
    (affineQuasicoherentSheavesInclusion R).obj
        (affineQuasicoherentFree R I) ≅
      SheafOfModules.free.{u} I :=
  tildeFinsupp I

/-- Higher `Ext` from an arbitrary-rank affine quasi-coherent free sheaf vanishes after
forgetting to all module sheaves.  The free sheaf is a coproduct of copies of the structure
sheaf, whose `Ext` computes affine quasi-coherent cohomology. -/
theorem subsingleton_ext_affineQuasicoherentFree_inclusion
    (R : CommRingCat.{u}) (I : Type u) (Y : AffineQuasicoherentSheaves R) (n : ℕ) :
    Subsingleton (Ext.{u + 1}
      ((affineQuasicoherentSheavesInclusion R).obj (affineQuasicoherentFree R I))
      ((affineQuasicoherentSheavesInclusion R).obj Y) (n + 1)) := by
  apply Ext.subsingleton_of_iso_left
    (affineQuasicoherentFreeInclusionIso R I) (n + 1)
  apply Ext.subsingleton_coproduct_left
  intro i
  haveI := Cohomology.modules_H_subsingleton_of_isQuasicoherent
    Y.obj (n + 1) (Nat.succ_pos n)
  exact (Scheme.Modules.extUnitAddEquivDerivedH Y.obj (n + 1)).toEquiv.subsingleton

/-- Higher `Ext` from an arbitrary-rank free object vanishes inside affine
quasi-coherent sheaves because that object is projective. -/
theorem subsingleton_ext_affineQuasicoherentFree
    (R : CommRingCat.{u}) (I : Type u) (Y : AffineQuasicoherentSheaves R) (n : ℕ) :
    Subsingleton (Ext.{u + 1} (affineQuasicoherentFree R I) Y (n + 1)) := by
  haveI := affineQuasicoherentFree_projective R I
  exact subsingleton_of_forall_eq 0 fun e ↦ Ext.eq_zero_of_projective e

/-- The exact affine quasi-coherent inclusion induces bijections on all `Ext` groups. -/
def AffineQuasicoherentExtComparison (R : CommRingCat.{u}) : Prop :=
  ∀ (F G : AffineQuasicoherentSheaves R) (n : ℕ),
    Function.Bijective
      ((affineQuasicoherentSheavesInclusion R).mapExtAddHom F G n)

/-- **Affine quasi-coherent `Ext` comparison.**  The arbitrary-rank free objects form
projective generators on the source and remain acyclic against quasi-coherent targets after
inclusion into all module sheaves. -/
theorem affineQuasicoherentExtComparison (R : CommRingCat.{u}) :
    AffineQuasicoherentExtComparison R := fun F G n ↦
  (affineQuasicoherentSheavesInclusion R).bijective_mapExtAddHom_of_generators
    (affineQuasicoherentFreeObjects R)
    (exists_affineQuasicoherentFree_epi R)
    (fun P hP Y n ↦ by
      obtain ⟨I, rfl⟩ := hP
      exact subsingleton_ext_affineQuasicoherentFree R I Y n)
    (fun P hP Y n ↦ by
      obtain ⟨I, rfl⟩ := hP
      exact subsingleton_ext_affineQuasicoherentFree_inclusion R I Y n)
    (fun X Y ↦
      (affineQuasicoherentSheavesInclusion R).bijective_mapExtAddHom_zero X Y)
    n F G

/-- The bounded affine derived inclusion is bijective on each hom-set. -/
theorem affineQuasicoherentBoundedDerivedInclusion_map_bijective
    (R : CommRingCat.{u})
    (E E' : AffineQuasicoherentBoundedDerivedCategory R) :
    Function.Bijective
      ((DerivedCategory.Bounded.ι ⋙ affineQuasicoherentDerivedInclusion R).map :
        (E ⟶ E') → _) := by
  have hι : Function.Bijective
      ((DerivedCategory.Bounded.ι
        (C := AffineQuasicoherentSheaves R)).map : (E ⟶ E') → _) :=
    ⟨DerivedCategory.Bounded.ι.map_injective,
      DerivedCategory.Bounded.ι.map_surjective⟩
  exact ((affineQuasicoherentSheavesInclusion R).mapDerivedCategory_map_bijective_of_bounded
      (affineQuasicoherentExtComparison R) E.property E'.property).comp hι

/-- The bounded affine realization into `Dqc` is full before restricting the target to
bounded objects. -/
theorem affineQuasicoherentBoundedToDqc_full (R : CommRingCat.{u}) :
    (DerivedCategory.Bounded.ι ⋙ affineQuasicoherentDerivedToDqc R).Full := by
  haveI : (DerivedCategory.Bounded.ι ⋙
      affineQuasicoherentDerivedInclusion R).Full :=
    ⟨fun g ↦
      (affineQuasicoherentBoundedDerivedInclusion_map_bijective R _ _).2 g⟩
  exact Functor.Full.of_comp_faithful_iso
    (G := SchemeQuasicoherentDerivedCategory.ι (Spec R))
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (affineQuasicoherentDerivedToDqcCompInclusion R))

/-- The bounded affine realization into `Dqc` is faithful before restricting the target to
bounded objects. -/
theorem affineQuasicoherentBoundedToDqc_faithful (R : CommRingCat.{u}) :
    (DerivedCategory.Bounded.ι ⋙ affineQuasicoherentDerivedToDqc R).Faithful := by
  haveI : (DerivedCategory.Bounded.ι ⋙
      affineQuasicoherentDerivedInclusion R).Faithful :=
    ⟨fun hfg ↦
      (affineQuasicoherentBoundedDerivedInclusion_map_bijective R _ _).1 hfg⟩
  exact Functor.Faithful.of_comp_iso
    (G := SchemeQuasicoherentDerivedCategory.ι (Spec R))
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (affineQuasicoherentDerivedToDqcCompInclusion R))

/-- The concrete bounded affine realization is full. -/
theorem affineQuasicoherentBoundedDerivedToDqc_full (R : CommRingCat.{u}) :
    (affineQuasicoherentBoundedDerivedToDqc R).Full := by
  haveI := affineQuasicoherentBoundedToDqc_full R
  change ((schemeBoundedQuasicoherent (Spec R)).lift
    (DerivedCategory.Bounded.ι ⋙ affineQuasicoherentDerivedToDqc R) _).Full
  infer_instance

/-- The concrete bounded affine realization is faithful. -/
theorem affineQuasicoherentBoundedDerivedToDqc_faithful (R : CommRingCat.{u}) :
    (affineQuasicoherentBoundedDerivedToDqc R).Faithful := by
  haveI := affineQuasicoherentBoundedToDqc_faithful R
  change ((schemeBoundedQuasicoherent (Spec R)).lift
    (DerivedCategory.Bounded.ι ⋙ affineQuasicoherentDerivedToDqc R) _).Faithful
  infer_instance

/-- Every intrinsically bounded object of `Dqc(Spec R)` is represented by a bounded
complex of affine quasi-coherent sheaves. -/
theorem affineQuasicoherentBoundedDerivedToDqc_essSurj (R : CommRingCat.{u}) :
    (affineQuasicoherentBoundedDerivedToDqc R).EssSurj where
  mem_essImage E := by
    obtain ⟨K, hK, ⟨e⟩⟩ :=
      (affineQuasicoherentSheavesInclusion R).exists_bounded_iso_mapDerivedCategory_obj
          (affineQuasicoherentExtComparison R) E.property
          (fun n ↦ ⟨⟨_, E.obj.property n⟩, ⟨Iso.refl _⟩⟩)
    exact ⟨⟨K, hK⟩,
      ⟨ObjectProperty.isoMk _ (ObjectProperty.isoMk _ e)⟩⟩

/-- **Bounded affine `Dqc` identification.**  The concrete realization functor is an
equivalence between the bounded derived category of affine quasi-coherent sheaves and the
intrinsic bounded quasi-coherent-cohomology locus. -/
noncomputable def affineQuasicoherentBoundedDqcEquivalence (R : CommRingCat.{u}) :
    AffineQuasicoherentBoundedDerivedCategory R ≌
      SchemeBoundedQuasicoherentDerivedCategory (Spec R) := by
  letI := affineQuasicoherentBoundedDerivedToDqc_full R
  letI := affineQuasicoherentBoundedDerivedToDqc_faithful R
  letI := affineQuasicoherentBoundedDerivedToDqc_essSurj R
  letI : (affineQuasicoherentBoundedDerivedToDqc R).IsEquivalence := {}
  exact (affineQuasicoherentBoundedDerivedToDqc R).asEquivalence

@[simp]
theorem affineQuasicoherentBoundedDqcEquivalence_functor (R : CommRingCat.{u}) :
    (affineQuasicoherentBoundedDqcEquivalence R).functor =
      affineQuasicoherentBoundedDerivedToDqc R :=
  rfl

end

end AlgebraicGeometry.DerivedCategory.Dqc
