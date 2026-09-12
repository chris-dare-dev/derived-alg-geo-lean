/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.DirectSum.Basic

/-!
# Finite support for maps out of compact objects

This file turns the additive-group formulation of compactness into the
finite-support statement used by Brown's mapping-telescope construction.  A
morphism from a compact object into a coproduct is a finite sum of component
morphisms followed by the coproduct injections.

The proof identifies a coproduct of additive commutative groups with the
concrete direct sum.  This bridge is kept private: the exported theorem is
stated entirely in the ambient preadditive category.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe v u

namespace AddCommGrpCat

variable {ι : Type} [DecidableEq ι]
  (A : ι → AddCommGrpCat.{v})

private def directSumCocone : Cofan A :=
  Cofan.mk (AddCommGrpCat.of (⨁ i, A i)) fun i =>
    AddCommGrpCat.ofHom (DirectSum.of (fun i => A i) i)

private def directSumCoconeIsColimit : IsColimit (directSumCocone A) where
  desc s := by
    classical
    let φ : ∀ i, A i →+ s.pt := fun i => (s.ι.app ⟨i⟩).hom
    exact AddCommGrpCat.ofHom (DirectSum.toAddMonoid φ)
  fac := by
    classical
    rintro s ⟨i⟩
    ext x
    change A i at x
    let φ : ∀ j, A j →+ s.pt := fun j => (s.ι.app ⟨j⟩).hom
    change (DirectSum.toAddMonoid φ) (DirectSum.of (fun i => A i) i x) = _
    exact DirectSum.toAddMonoid_of φ i x
  uniq := by
    classical
    rintro s f h
    ext : 1
    apply DirectSum.addHom_ext'
    intro i
    ext x
    have hx := CategoryTheory.congr_fun (h ⟨i⟩) x
    change f.hom (DirectSum.of (fun i => A i) i x) =
      (s.ι.app ⟨i⟩).hom x at hx
    change f.hom (DirectSum.of (fun i => A i) i x) =
      (DirectSum.toAddMonoid (fun j => (s.ι.app ⟨j⟩).hom))
        (DirectSum.of (fun i => A i) i x)
    rw [DirectSum.toAddMonoid_of]
    exact hx

variable [HasCoproduct A]

private def coproductIsoDirectSum :
    ∐ A ≅ AddCommGrpCat.of (⨁ i, A i) :=
  colimit.isoColimitCocone
    ⟨directSumCocone A, directSumCoconeIsColimit A⟩

@[reassoc (attr := simp)]
private theorem ι_coproductIsoDirectSum_hom (i : ι) :
    Sigma.ι A i ≫ (coproductIsoDirectSum A).hom =
      AddCommGrpCat.ofHom (DirectSum.of (fun i => A i) i) :=
  colimit.isoColimitCocone_ι_hom _ _

end AddCommGrpCat

namespace CategoryTheory.IsCompactObject

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {K : C} (hK : IsCompactObject.{0} K)

include hK

/-- A morphism from a compact object into a coproduct is a finite sum of
morphisms into individual summands followed by the coproduct injections. -/
theorem exists_finite_sum {ι : Type} (X : ι → C)
    [HasCoproduct X] (f : K ⟶ ∐ X) :
    ∃ (s : Finset ι) (g : ∀ i, K ⟶ X i),
      f = ∑ i ∈ s, g i ≫ Sigma.ι X i := by
  classical
  let H : ι → AddCommGrpCat.{v} := fun i =>
    (preadditiveCoyoneda.obj (Opposite.op K)).obj (X i)
  letI : HasCoproduct H := inferInstance
  let e :
      Discrete.functor X ⋙ preadditiveCoyoneda.obj (Opposite.op K) ≅
        Discrete.functor H :=
    Discrete.compNatIsoDiscrete X
      (preadditiveCoyoneda.obj (Opposite.op K))
  let totalIso :=
    hK.coproductComparisonIso X ≪≫
      HasColimit.isoOfNatIso e ≪≫
        AddCommGrpCat.coproductIsoDirectSum H
  let y : ⨁ i, H i := totalIso.hom f
  let g : ∀ i, K ⟶ X i := fun i => y i
  have totalIso_ι (i : ι) :
      (preadditiveCoyoneda.obj (Opposite.op K)).map (Sigma.ι X i) ≫
          totalIso.hom =
        AddCommGrpCat.ofHom (DirectSum.of (fun i => H i) i) := by
    dsimp [totalIso]
    simp only [Iso.trans_hom]
    rw [map_ι_coproductComparisonIso_hom_assoc]
    have he := HasColimit.isoOfNatIso_ι_hom_assoc e ⟨i⟩
      (AddCommGrpCat.coproductIsoDirectSum H).hom
    refine he.trans ?_
    simp [e, H]
    exact Category.id_comp _
  have totalIso_hom_comp_ι (i : ι) (a : K ⟶ X i) :
      totalIso.hom (a ≫ Sigma.ι X i) =
        DirectSum.of (fun i => H i) i a := by
    have h := CategoryTheory.congr_fun (totalIso_ι i) a
    change totalIso.hom
      ((preadditiveCoyoneda.obj (Opposite.op K)).map (Sigma.ι X i) a) = _
    exact h
  refine ⟨y.support, g, ?_⟩
  apply totalIso.addCommGroupIsoToAddEquiv.injective
  change y = totalIso.hom (∑ i ∈ y.support, g i ≫ Sigma.ι X i)
  rw [map_sum]
  simp only [totalIso_hom_comp_ι, g]
  exact (DirectSum.sum_support_of (β := fun i => H i) y).symm

end CategoryTheory.IsCompactObject
