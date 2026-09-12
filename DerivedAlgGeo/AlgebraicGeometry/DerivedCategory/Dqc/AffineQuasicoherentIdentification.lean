/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.LeftResolution
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext.AcyclicGenerators
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

end

end AlgebraicGeometry.DerivedCategory.Dqc
