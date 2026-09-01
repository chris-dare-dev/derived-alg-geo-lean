/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Tactic.CategoryTheory.CancelIso
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Transporting pseudofunctor presentations through equivalences

This file centralizes the Cat-level transport used when an objectwise model of
a pseudofunctor is replaced by equivalent categories. It conjugates transition
functors and transports their compositors, units, pentagon equation, and two
triangle equations. Concrete consumers provide the presentation being
transported; the coherence calculus itself belongs to the pseudofunctor root.
-/

namespace CategoryTheory.Pseudofunctor

noncomputable section

/-- Conjugate a functor by equivalences of its source and target. -/
def equivalenceTransportFunctor
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁) (F : C₀ ⥤ C₁) :
    D₀ ⥤ D₁ :=
  E₀.inverse ⋙ F ⋙ E₁.functor

/-- A compositor is transported through objectwise equivalences. -/
def equivalenceTransportCompIso
    {C₀ D₀ C₁ D₁ C₂ D₂ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    [Category C₂] [Category D₂]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁) (E₂ : C₂ ≌ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (e : F ⋙ G ≅ H) :
    equivalenceTransportFunctor E₀ E₁ F ⋙
        equivalenceTransportFunctor E₁ E₂ G ≅
      equivalenceTransportFunctor E₀ E₂ H := by
  let cancelE₁ : E₁.functor ⋙ (E₁.inverse ⋙ G) ≅ G :=
    (Functor.associator E₁.functor E₁.inverse G).symm ≪≫
      Functor.isoWhiskerRight E₁.unitIso.symm G ≪≫ G.leftUnitor
  change (E₀.inverse ⋙ F ⋙ E₁.functor) ⋙
      (E₁.inverse ⋙ G ⋙ E₂.functor) ≅
    E₀.inverse ⋙ H ⋙ E₂.functor
  exact
    (Functor.associator (E₀.inverse ⋙ F ⋙ E₁.functor)
      (E₁.inverse ⋙ G) E₂.functor).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator (E₀.inverse ⋙ F) E₁.functor
        (E₁.inverse ⋙ G)) E₂.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (E₀.inverse ⋙ F) cancelE₁) E₂.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.associator E₀.inverse F G) E₂.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft E₀.inverse e) E₂.functor

/-- A two-stage comparison with the identity is transported through an
equivalence. -/
def equivalenceTransportIdIso
    {C D : Type*} [Category C] [Category D]
    (E : C ≌ D) (F G : C ⥤ C) (e₀ : F ≅ G) (e₁ : G ≅ 𝟭 C) :
    equivalenceTransportFunctor E E F ≅ 𝟭 D :=
  Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft E.inverse e₀) E.functor ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft E.inverse e₁) E.functor ≪≫
    Functor.isoWhiskerRight (Functor.rightUnitor E.inverse) E.functor ≪≫
    E.counitIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The transported compositors satisfy the pentagon equation whenever the
original compositors do. -/
theorem equivalenceTransport_associativity
    {C₀ D₀ C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    [Category C₂] [Category D₂] [Category C₃] [Category D₃]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁)
    (E₂ : C₂ ≌ D₂) (E₃ : C₃ ≌ D₃)
    (F₀₁ : C₀ ⥤ C₁) (F₁₂ : C₁ ⥤ C₂) (F₂₃ : C₂ ⥤ C₃)
    (F₀₂ : C₀ ⥤ C₂) (F₁₃ : C₁ ⥤ C₃) (F₀₃ : C₀ ⥤ C₃)
    (c₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂) (c₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃)
    (c₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃) (c₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃)
    (hassoc : c₀₂₃.symm.hom ≫ Functor.whiskerRight c₀₁₂.symm.hom F₂₃ ≫
      (Functor.associator F₀₁ F₁₂ F₂₃).hom ≫
      Functor.whiskerLeft F₀₁ c₁₂₃.hom ≫ c₀₁₃.hom = 𝟙 _) :
    (equivalenceTransportCompIso E₀ E₂ E₃ F₀₂ F₂₃ F₀₃ c₀₂₃).symm.hom ≫
      Functor.whiskerRight
        (equivalenceTransportCompIso E₀ E₁ E₂ F₀₁ F₁₂ F₀₂ c₀₁₂).symm.hom _ ≫
      (Functor.associator
        (equivalenceTransportFunctor E₀ E₁ F₀₁)
        (equivalenceTransportFunctor E₁ E₂ F₁₂)
        (equivalenceTransportFunctor E₂ E₃ F₂₃)).hom ≫
      Functor.whiskerLeft (equivalenceTransportFunctor E₀ E₁ F₀₁)
        (equivalenceTransportCompIso E₁ E₂ E₃ F₁₂ F₂₃ F₁₃ c₁₂₃).hom ≫
      (equivalenceTransportCompIso E₀ E₁ E₃ F₀₁ F₁₃ F₀₃ c₀₁₃).hom =
        𝟙 _ := by
  apply NatTrans.ext
  funext K
  have hCompNaturality := c₁₂₃.hom.naturality
    (E₁.unitIso.hom.app (F₀₁.obj (E₀.inverse.obj K)))
  dsimp at hCompNaturality
  have hCore := NatTrans.congr_app hassoc (E₀.inverse.obj K)
  simp at hCore
  apply E₃.inverse.map_injective
  dsimp [equivalenceTransportCompIso, equivalenceTransportFunctor]
  simp [Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp, Functor.map_id, Category.assoc]
  slice_lhs 4 5 => rw [hCompNaturality]
  simp [Category.assoc]
  slice_lhs 2 5 => rw [hCore]
  simpa only [Category.id_comp] using
    E₃.unitIso_inv_hom_id_app (F₀₃.obj (E₀.inverse.obj K))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The transported unit and compositor satisfy the left triangle equation
whenever the original comparisons do. -/
theorem equivalenceTransport_leftUnitality
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁)
    (Fid Gid : C₀ ⥤ C₀) (F : C₀ ⥤ C₁)
    (e₀ : Fid ≅ Gid) (e₁ : Gid ≅ 𝟭 C₀) (c : Fid ⋙ F ≅ F)
    (hleft : c.symm.hom ≫ Functor.whiskerRight (e₀ ≪≫ e₁).hom F ≫
      (Functor.leftUnitor F).hom = 𝟙 _) :
    (equivalenceTransportCompIso E₀ E₀ E₁ Fid F F c).symm.hom ≫
      Functor.whiskerRight (equivalenceTransportIdIso E₀ Fid Gid e₀ e₁).hom
        (equivalenceTransportFunctor E₀ E₁ F) ≫
      (Functor.leftUnitor (equivalenceTransportFunctor E₀ E₁ F)).hom = 𝟙 _ := by
  apply NatTrans.ext
  funext K
  have hCore := NatTrans.congr_app hleft (E₀.inverse.obj K)
  simp at hCore
  apply E₁.inverse.map_injective
  dsimp [equivalenceTransportCompIso, equivalenceTransportIdIso,
    equivalenceTransportFunctor]
  simp [Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp, Functor.map_id, Category.assoc]
  slice_lhs 2 4 => rw [hCore]
  simpa only [Category.id_comp] using
    E₁.unitIso_inv_hom_id_app (F.obj (E₀.inverse.obj K))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The transported unit and compositor satisfy the right triangle equation
whenever the original comparisons do. -/
theorem equivalenceTransport_rightUnitality
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    (E₀ : C₀ ≌ D₀) (E₁ : C₁ ≌ D₁)
    (F : C₀ ⥤ C₁) (Fid Gid : C₁ ⥤ C₁)
    (e₀ : Fid ≅ Gid) (e₁ : Gid ≅ 𝟭 C₁) (c : F ⋙ Fid ≅ F)
    (hright : c.symm.hom ≫ Functor.whiskerLeft F (e₀ ≪≫ e₁).hom ≫
      (Functor.rightUnitor F).hom = 𝟙 _) :
    (equivalenceTransportCompIso E₀ E₁ E₁ F Fid F c).symm.hom ≫
      Functor.whiskerLeft (equivalenceTransportFunctor E₀ E₁ F)
        (equivalenceTransportIdIso E₁ Fid Gid e₀ e₁).hom ≫
      (Functor.rightUnitor (equivalenceTransportFunctor E₀ E₁ F)).hom = 𝟙 _ := by
  apply NatTrans.ext
  funext K
  have hCore := NatTrans.congr_app hright (E₀.inverse.obj K)
  simp at hCore
  apply E₁.inverse.map_injective
  dsimp [equivalenceTransportCompIso, equivalenceTransportIdIso,
    equivalenceTransportFunctor]
  simp [Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj,
    Functor.map_comp, Functor.map_id, Category.assoc]
  slice_lhs 2 4 => rw [hCore]
  simpa only [Category.id_comp] using
    E₁.unitIso_inv_hom_id_app (F.obj (E₀.inverse.obj K))

end

end CategoryTheory.Pseudofunctor
