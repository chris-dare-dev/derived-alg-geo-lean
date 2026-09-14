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

namespace CategoryTheory

section DirectSumComparison

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K : C) {ι : Type} [DecidableEq ι] (X : ι → C) [HasCoproduct X]

/-- The comparison map from the direct sum of the Hom groups into the summands to the Hom
group into the coproduct: `(aᵢ) ↦ ∑ aᵢ ≫ ιᵢ`. Compactness of `K` in the indexing universe
`Type` is bijectivity of this map for every coproduct, see
`isCompactObject_iff_bijective_directSumToHom`. -/
noncomputable def directSumToHom : (⨁ i, (K ⟶ X i)) →+ (K ⟶ ∐ X) :=
  DirectSum.toAddMonoid fun i ↦ Preadditive.rightComp K (Sigma.ι X i)

@[simp]
theorem directSumToHom_of (i : ι) (a : K ⟶ X i) :
    directSumToHom K X (DirectSum.of (fun i ↦ (K ⟶ X i)) i a) = a ≫ Sigma.ι X i := by
  unfold directSumToHom
  rw [DirectSum.toAddMonoid_of]
  rfl

variable {K}

/-- Precomposition with `f` on every summand of the direct sum of Hom groups. -/
noncomputable def directSumPrecomp {L : C} (f : K ⟶ L) :
    (⨁ i, (L ⟶ X i)) →+ ⨁ i, (K ⟶ X i) :=
  DirectSum.map fun i ↦ Preadditive.leftComp (X i) f

omit [DecidableEq ι] [HasCoproduct X] in
@[simp]
theorem directSumPrecomp_apply {L : C} (f : K ⟶ L) (x : ⨁ i, (L ⟶ X i)) (i : ι) :
    directSumPrecomp X f x i = f ≫ x i :=
  DirectSum.map_apply _ _ _

omit [DecidableEq ι] [HasCoproduct X] in
theorem directSumPrecomp_comp {L M : C} (f : K ⟶ L) (g : L ⟶ M) (x : ⨁ i, (M ⟶ X i)) :
    directSumPrecomp X f (directSumPrecomp X g x) = directSumPrecomp X (f ≫ g) x := by
  ext i
  simp

omit [DecidableEq ι] [HasCoproduct X] in
theorem directSumPrecomp_id (x : ⨁ i, (K ⟶ X i)) : directSumPrecomp X (𝟙 K) x = x := by
  ext i
  simp

/-- The comparison map is natural in the source object. -/
theorem directSumToHom_precomp {L : C} (f : K ⟶ L) (x : ⨁ i, (L ⟶ X i)) :
    directSumToHom K X (directSumPrecomp X f x) = f ≫ directSumToHom L X x := by
  refine DirectSum.induction_on x (by simp) (fun i a ↦ ?_) (fun a b ha hb ↦ ?_)
  · simp [directSumPrecomp, Preadditive.leftComp]
  · simp only [map_add, ha, hb, Preadditive.comp_add]

/-- **Compact objects have bijective comparison maps.** -/
theorem IsCompactObject.bijective_directSumToHom (hK : IsCompactObject.{0} K) :
    Function.Bijective (directSumToHom K X) := by
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
  have key (i : ι) (a : K ⟶ X i) :
      totalIso.hom (a ≫ Sigma.ι X i) = DirectSum.of (fun i => H i) i a := by
    have h := CategoryTheory.congr_fun (totalIso_ι i) a
    change totalIso.hom
      ((preadditiveCoyoneda.obj (Opposite.op K)).map (Sigma.ι X i) a) = _
    exact h
  have hcomp' : (ConcreteCategory.hom totalIso.hom).comp (directSumToHom K X) =
      AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext'
    intro i
    refine AddMonoidHom.ext fun a ↦ ?_
    show totalIso.hom (directSumToHom K X (DirectSum.of (fun i ↦ (K ⟶ X i)) i a)) =
      DirectSum.of (fun i ↦ (K ⟶ X i)) i a
    erw [directSumToHom_of]
    exact key i a
  have hcomp : ∀ x : ⨁ i, (K ⟶ X i), totalIso.hom (directSumToHom K X x) = x :=
    fun x ↦ DFunLike.congr_fun hcomp' x
  have hinj : Function.Injective totalIso.hom :=
    Function.LeftInverse.injective (g := totalIso.inv) fun x ↦ by
      rw [← ConcreteCategory.comp_apply, totalIso.hom_inv_id, ConcreteCategory.id_apply]
  constructor
  · intro x y hxy
    rw [← hcomp x, ← hcomp y, hxy]
  · intro f
    exact ⟨totalIso.hom f, hinj (hcomp _)⟩

/-- **Bijective comparison maps give compactness.** -/
theorem isCompactObject_of_bijective_directSumToHom
    (h : ∀ (ι : Type) [DecidableEq ι] (X : ι → C) [HasCoproduct X],
      Function.Bijective (directSumToHom K X)) :
    IsCompactObject.{0} K := by
  intro ι
  classical
  haveI : ∀ (X : ι → C),
      PreservesColimit (Discrete.functor X) (preadditiveCoyoneda.obj (Opposite.op K)) := by
    intro X
    by_cases hX : HasCoproduct X
    · obtain ⟨φ, hφ⟩ : ∃ φ : AddCommGrpCat.of (⨁ i, (K ⟶ X i)) ≅ AddCommGrpCat.of (K ⟶ ∐ X),
          φ.hom = AddCommGrpCat.ofHom (directSumToHom K X) :=
        ⟨(AddEquiv.ofBijective (directSumToHom K X) (h ι X)).toAddCommGrpIso, by ext; rfl⟩
      have hcomp : sigmaComparison (preadditiveCoyoneda.obj (Opposite.op K)) X =
          (AddCommGrpCat.coproductIsoDirectSum
            (fun i ↦ (preadditiveCoyoneda.obj (Opposite.op K)).obj (X i)) ≪≫ φ).hom := by
        rw [Iso.trans_hom]
        apply Sigma.hom_ext
        intro i
        rw [ι_comp_sigmaComparison]
        erw [AddCommGrpCat.ι_coproductIsoDirectSum_hom_assoc]
        rw [hφ]
        ext a
        change a ≫ Sigma.ι X i = directSumToHom K X (DirectSum.of (fun i ↦ (K ⟶ X i)) i a)
        rw [directSumToHom_of]
      haveI : IsIso (sigmaComparison (preadditiveCoyoneda.obj (Opposite.op K)) X) := by
        rw [hcomp]
        infer_instance
      exact PreservesCoproduct.of_iso_comparison _ _
    · exact ⟨fun hc ↦ (hX ⟨⟨_, hc⟩⟩).elim⟩
  exact preservesColimitsOfShape_of_discrete _

/-- Compactness in the indexing universe `Type` is bijectivity of the direct-sum
comparison map for every `Type`-indexed coproduct. -/
theorem isCompactObject_iff_bijective_directSumToHom :
    IsCompactObject.{0} K ↔
      ∀ (ι : Type) [DecidableEq ι] (X : ι → C) [HasCoproduct X],
        Function.Bijective (directSumToHom K X) :=
  ⟨fun hK _ _ X _ ↦ hK.bijective_directSumToHom X,
    isCompactObject_of_bijective_directSumToHom⟩

end DirectSumComparison

end CategoryTheory

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
