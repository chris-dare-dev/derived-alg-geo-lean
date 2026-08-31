/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Forgetting module-valued Čech complexes

The Čech complex of the underlying additive-group-valued presheaf is
canonically the result of forgetting the module-valued Čech complex.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Evaluation on a formal coproduct commutes with forgetting a module to its underlying
additive group. The components are the canonical product-comparison isomorphisms. -/
noncomputable def evalOpForget₂AddCommGrpIso
    {C : Type u} [Category C] [HasFiniteProducts C]
    {R : CommRingCat.{u}} (P : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    (Limits.FormalCoproduct.evalOp C (ModuleCat R)).obj P ⋙
        forget₂ (ModuleCat R) AddCommGrpCat.{u} ≅
      (Limits.FormalCoproduct.evalOp C AddCommGrpCat.{u}).obj
        (P ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{u}) := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · let A : X.unop.I → ModuleCat R := fun i ↦ P.obj (op (X.unop.obj i))
    exact Limits.PreservesProduct.iso
      (forget₂ (ModuleCat R) AddCommGrpCat.{u}) A
  · intro X Y f
    let F := forget₂ (ModuleCat R) AddCommGrpCat.{u}
    let Aₓ : X.unop.I → ModuleCat R := fun i ↦ P.obj (op (X.unop.obj i))
    let Aᵧ : Y.unop.I → ModuleCat R := fun i ↦ P.obj (op (Y.unop.obj i))
    let q : ∀ i : Y.unop.I, (∏ᶜ Aₓ) ⟶ Aᵧ i := fun i ↦
      Limits.Pi.π Aₓ (f.unop.f i) ≫ P.map (f.unop.φ i).op
    change F.map (Limits.Pi.lift q) ≫ Limits.piComparison F Aᵧ =
      Limits.piComparison F Aₓ ≫ Limits.Pi.lift (fun i ↦
        Limits.Pi.π (fun j ↦ F.obj (Aₓ j)) (f.unop.f i) ≫
          F.map (P.map (f.unop.φ i).op))
    rw [Limits.map_lift_piComparison]
    apply Limits.Pi.hom_ext
    intro i
    rw [Limits.Pi.lift_π]
    rw [Category.assoc, Limits.Pi.lift_π]
    rw [← Category.assoc, Limits.piComparison_comp_π, ← F.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Additive functors commute with the alternating-coface-map complex. -/
theorem map_alternatingCofaceMapComplex
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] :
    AlgebraicTopology.alternatingCofaceMapComplex C ⋙
        F.mapHomologicalComplex (ComplexShape.up ℕ) =
      (CosimplicialObject.whiskering C D).obj F ⋙
        AlgebraicTopology.alternatingCofaceMapComplex D := by
  apply Functor.ext
  · intro X Y f
    ext n
    simp only [Functor.comp_map, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.eqToHom_f,
      eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl
  · intro X
    apply HomologicalComplex.ext
    · rintro i j (rfl : i + 1 = j)
      dsimp only [Functor.comp_obj]
      simp only [Functor.mapHomologicalComplex_obj_d, eqToHom_refl,
        Category.comp_id, Category.id_comp]
      dsimp [AlgebraicTopology.alternatingCofaceMapComplex,
        AlgebraicTopology.AlternatingCofaceMapComplex.obj,
        AlgebraicTopology.AlternatingCofaceMapComplex.objD]
      rw [CochainComplex.of_d, CochainComplex.of_d]
      change F.map (∑ k : Fin (i + 2),
        (-1 : ℤ) ^ (k : ℕ) • X.δ k) =
          ∑ k : Fin (i + 2), (-1 : ℤ) ^ (k : ℕ) • F.map (X.δ k)
      rw [Functor.map_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Functor.map_zsmul]
    · ext n
      rfl

/-- The Čech complex of an underlying additive-group-valued presheaf is canonically the
forgotten module-valued Čech complex. -/
noncomputable def cechComplexForget₂AddCommGrpIso
    {C : Type u} [Category C] [HasFiniteProducts C]
    {R : CommRingCat.{u}} {I : Type u} (U : I → C)
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    ((forget₂ (ModuleCat R) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj P) ≅
      (cechComplexFunctor U).obj
        (P ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{u}) := by
  let V := Limits.FormalCoproduct.mk I U
  let E := V.cech.rightOp
  let e := Functor.isoWhiskerLeft E (evalOpForget₂AddCommGrpIso P)
  let eK := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).mapIso e
  let K₁ := ((forget₂ (ModuleCat R) AddCommGrpCat.{u}).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj ((cechComplexFunctor U).obj P)
  let K₂ := (AlgebraicTopology.alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
    ((Limits.FormalCoproduct.cosimplicialObjectFunctor V.cech).obj P ⋙
      forget₂ (ModuleCat R) AddCommGrpCat.{u})
  have hK : K₁ = K₂ := by
    exact congrArg (fun F ↦ F.obj
      ((Limits.FormalCoproduct.cosimplicialObjectFunctor V.cech).obj P))
        (map_alternatingCofaceMapComplex
          (forget₂ (ModuleCat R) AddCommGrpCat.{u}))
  let e₁ : K₁ ≅ K₂ := eqToIso hK
  exact e₁ ≪≫ eK

/-- Exactness of a module-valued Čech complex passes to the Čech complex of the underlying
additive-group-valued presheaf. -/
lemma cechComplex_exactAt_forget₂AddCommGrp_of_exactAt
    {C : Type u} [Category C] [HasFiniteProducts C]
    {R : CommRingCat.{u}} {I : Type u} (U : I → C)
    (P : Cᵒᵖ ⥤ ModuleCat.{u} R) (n : ℕ)
    (h : ((cechComplexFunctor U).obj P).ExactAt n) :
    ((cechComplexFunctor U).obj
      (P ⋙ forget₂ (ModuleCat R) AddCommGrpCat.{u})).ExactAt n := by
  let F := forget₂ (ModuleCat R) AddCommGrpCat.{u}
  let K := (cechComplexFunctor U).obj P
  have hmap : ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).ExactAt n := by
    rw [HomologicalComplex.exactAt_iff]
    change ((K.sc n).map F).Exact
    exact h.map F
  exact hmap.of_iso (cechComplexForget₂AddCommGrpIso U P)

end CategoryTheory
