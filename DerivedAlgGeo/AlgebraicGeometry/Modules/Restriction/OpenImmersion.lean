/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Presentation.Transport
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Topology.Sheaves.Over

/-!
# Comparing open-immersion restriction with slice-site restriction

For an open immersion `f : X ⟶ Y`, the open-set site of `X` is equivalent to the slice of the
open-set site of `Y` over the range of `f`. This file constructs that equivalence and lifts it to
an equivalence of the corresponding categories of sheaves of modules.
-/

universe u

open CategoryTheory TopologicalSpace

namespace CategoryTheory.Over

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsCocontinuous J K] (X : C)

/-- Cocontinuity passes to the induced functor on over categories. -/
instance post_isCocontinuous :
    (Over.post (X := X) F).IsCocontinuous (J.over X) (K.over (F.obj X)) where
  cover_lift {U} S hS := by
    rw [GrothendieckTopology.mem_over_iff] at hS ⊢
    have h := F.cover_lift J K hS
    convert h using 1
    ext Z g
    rw [Sieve.overEquiv_iff]
    dsimp [Sieve.functorPullback, Presieve.functorPullback]
    let A : Over X := Over.mk (g ≫ U.hom)
    let a : (Over.post F).obj A ⟶ (Over.post F).obj U :=
      (Over.post F).map (Over.homMk g)
    let B : Over (F.obj X) := Over.mk (F.map g ≫ F.map U.hom)
    let b : B ⟶ (Over.post F).obj U := Over.homMk (F.map g)
    constructor
    · intro hg
      apply (Sieve.overEquiv_iff (Y := Over.mk (F.map U.hom)) S (F.map g)).mpr
      change S b
      change S a at hg
      let p : B ⟶ (Over.post F).obj A := Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ F.map (g ≫ U.hom) = F.map g ≫ F.map U.hom
        simpa only [Category.id_comp] using F.map_comp g U.hom)
      have hp := S.downward_closed hg p
      rw [show p ≫ a = b by ext; exact Category.id_comp _] at hp
      exact hp
    · intro hg
      have hg :=
        (Sieve.overEquiv_iff (Y := Over.mk (F.map U.hom)) S (F.map g)).mp hg
      change S b at hg
      change S a
      let p : (Over.post F).obj A ⟶ B := Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ F.map g ≫ F.map U.hom = F.map (g ≫ U.hom)
        simpa only [Category.id_comp] using (F.map_comp g U.hom).symm)
      have hp := S.downward_closed hg p
      rw [show p ≫ b = a by ext; exact Category.id_comp _] at hp
      exact hp

end CategoryTheory.Over

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : C)

@[simp]
lemma overFunctor_obj (M : SheafOfModules.{u} R) :
    (overFunctor R U).obj M = M.over U := rfl

end SheafOfModules

namespace CategoryTheory

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {I : Type*} {U : I → C}

/-- An equivalence whose forward functor preserves covers sends a family covering the terminal
object to a family covering the terminal object. -/
lemma GrothendieckTopology.CoversTop.map_equivalence :
    (hU : J.CoversTop U) → (e : _root_.CategoryTheory.Equivalence C D) →
      CoverPreserving J K e.functor →
      K.CoversTop (fun i ↦ e.functor.obj (U i)) := by
  intro hU e he
  have hcover (Z : C) :
      Sieve.ofObjects (fun i ↦ e.functor.obj (U i)) (e.functor.obj Z) ∈
        K (e.functor.obj Z) := by
    refine K.superset_covering ?_
      (CoverPreserving.cover_preserve he (hU Z))
    intro T g hg
    obtain ⟨A, a, b, ha, rfl⟩ := hg
    obtain ⟨i, ⟨c⟩⟩ := (Sieve.mem_ofObjects_iff U a).mp ha
    exact (Sieve.mem_ofObjects_iff _ _).mpr ⟨i, ⟨b ≫ e.functor.map c⟩⟩
  intro Z
  refine K.superset_covering ?_
    (K.pullback_stable (e.counitInv.app Z) (hcover (e.inverse.obj Z)))
  intro T g hg
  change ∃ i, Nonempty (T ⟶ e.functor.obj (U i)) at hg ⊢
  exact hg

end CategoryTheory

namespace AlgebraicGeometry

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- The open-set site of the source of an open immersion is equivalent to the slice of the
open-set site of the target over the range of the immersion. -/
@[simps!]
def opensRangeEquivalence : Over f.opensRange ≌ X.Opens where
  functor := Over.forget f.opensRange ⋙ Opens.map f.base
  inverse :=
    { obj := fun U => Over.mk (Y := f ''ᵁ U) (homOfLE (f.image_le_opensRange U))
      map := fun g => Over.homMk (f.opensFunctor.map g) }
  unitIso := NatIso.ofComponents fun U => Over.isoMk (eqToIso (by
    apply Opens.ext
    simpa [Set.image_preimage_eq_inter_range] using
      Set.image_preimage_eq_of_subset (show (U.left : Set Y) ⊆ Set.range f from U.hom.le)))
  counitIso := NatIso.ofComponents fun U => eqToIso (f.preimage_image_eq U)

instance opensRangeEquivalence_functor_isContinuous :
    (f.opensRangeEquivalence.functor).IsContinuous
      ((Opens.grothendieckTopology Y).over f.opensRange)
      (Opens.grothendieckTopology X) :=
  by
    change (Over.forget f.opensRange ⋙ Opens.map f.base).IsContinuous _ _
    exact Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology Y) _

lemma opensRangeEquivalence_functor_coverPreserving :
    CoverPreserving ((Opens.grothendieckTopology Y).over f.opensRange)
      (Opens.grothendieckTopology X) f.opensRangeEquivalence.functor :=
  CoverPreserving.comp _ _
    (GrothendieckTopology.over_forget_coverPreserving
      (Opens.grothendieckTopology Y) f.opensRange)
    (coverPreserving_opens_map f.base)

lemma opensRangeEquivalence_inverse_coverPreserving :
    CoverPreserving (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology Y).over f.opensRange)
      f.opensRangeEquivalence.inverse where
  cover_preserve {U S} hS := by
    rw [GrothendieckTopology.mem_over_iff]
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨V, i, hi, hxV⟩ := hS x hx
    refine ⟨f ''ᵁ V, f.opensFunctor.map i, ?_, Set.mem_image_of_mem f hxV⟩
    rw [Sieve.overEquiv_iff]
    exact ⟨V, i, 𝟙 _, hi, by aesop_cat⟩

instance opensRangeEquivalence_functor_isCocontinuous :
    (f.opensRangeEquivalence.functor).IsCocontinuous
      ((Opens.grothendieckTopology Y).over f.opensRange)
      (Opens.grothendieckTopology X) :=
  (f.opensRangeEquivalence.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
    f.opensRangeEquivalence_inverse_coverPreserving

instance opensRangeEquivalence_inverse_isCocontinuous :
    (f.opensRangeEquivalence.inverse).IsCocontinuous
      (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology Y).over f.opensRange) :=
  (f.opensRangeEquivalence.symm.toAdjunction.isCocontinuous_iff_coverPreserving _ _).2
    f.opensRangeEquivalence_functor_coverPreserving

instance opensRangeEquivalence_inverse_isContinuous :
    (f.opensRangeEquivalence.inverse).IsContinuous
      (Opens.grothendieckTopology X)
      ((Opens.grothendieckTopology Y).over f.opensRange) := by
  apply Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ f.opensRangeEquivalence.inverse)
  exact f.opensRangeEquivalence_inverse_coverPreserving

/-- The equivalence on slice categories induced by `opensRangeEquivalence`. -/
def opensRangeOverEquivalence (W : Over f.opensRange) :
    Over W ≌ Over (f.opensRangeEquivalence.functor.obj W) :=
  CategoryTheory.Over.postEquiv W f.opensRangeEquivalence

instance opensRangeOverEquivalence_functor_isCocontinuous (W : Over f.opensRange) :
    (f.opensRangeOverEquivalence W).functor.IsCocontinuous
      (((Opens.grothendieckTopology Y).over f.opensRange).over W)
      ((Opens.grothendieckTopology X).over
        (f.opensRangeEquivalence.functor.obj W)) := by
  change (Over.post f.opensRangeEquivalence.functor).IsCocontinuous _ _
  infer_instance

instance opensRangeOverEquivalence_inverse_isCocontinuous (W : Over f.opensRange) :
    (f.opensRangeOverEquivalence W).inverse.IsCocontinuous
      ((Opens.grothendieckTopology X).over
        (f.opensRangeEquivalence.functor.obj W))
      (((Opens.grothendieckTopology Y).over f.opensRange).over W) := by
  change (Over.post f.opensRangeEquivalence.inverse ⋙
    Over.map (f.opensRangeEquivalence.unitInv.app W)).IsCocontinuous _ _
  constructor
  intro U S hS
  let hmap : (Over.map (f.opensRangeEquivalence.unitInv.app W)).IsCocontinuous
      (((Opens.grothendieckTopology Y).over f.opensRange).over
        (f.opensRangeEquivalence.inverse.obj
          (f.opensRangeEquivalence.functor.obj W)))
      (((Opens.grothendieckTopology Y).over f.opensRange).over W) :=
    GrothendieckTopology.instIsCocontinuousOverMapOver
      ((Opens.grothendieckTopology Y).over f.opensRange)
      (f.opensRangeEquivalence.unitInv.app W)
  have hS' := hmap.cover_lift hS
  let hpost : (Over.post f.opensRangeEquivalence.inverse).IsCocontinuous
      ((Opens.grothendieckTopology X).over
        (f.opensRangeEquivalence.functor.obj W))
      (((Opens.grothendieckTopology Y).over f.opensRange).over
        (f.opensRangeEquivalence.inverse.obj
          (f.opensRangeEquivalence.functor.obj W))) := inferInstance
  exact hpost.cover_lift hS'

instance opensRangeOverEquivalence_functor_isContinuous (W : Over f.opensRange) :
    (f.opensRangeOverEquivalence W).functor.IsContinuous
      (((Opens.grothendieckTopology Y).over f.opensRange).over W)
      ((Opens.grothendieckTopology X).over
        (f.opensRangeEquivalence.functor.obj W)) := by
  letI : (f.opensRangeOverEquivalence W).symm.functor.IsCocontinuous
      ((Opens.grothendieckTopology X).over
        (f.opensRangeEquivalence.functor.obj W))
      (((Opens.grothendieckTopology Y).over f.opensRange).over W) :=
    f.opensRangeOverEquivalence_inverse_isCocontinuous W
  exact (f.opensRangeOverEquivalence W).symm.toAdjunction.isContinuous_of_isCocontinuous _ _

instance opensRangeOverEquivalence_inverse_isContinuous (W : Over f.opensRange) :
    (f.opensRangeOverEquivalence W).inverse.IsContinuous
      ((Opens.grothendieckTopology X).over
        (f.opensRangeEquivalence.functor.obj W))
      (((Opens.grothendieckTopology Y).over f.opensRange).over W) :=
  (f.opensRangeOverEquivalence W).toAdjunction.isContinuous_of_isCocontinuous _ _

/-- The structure-sheaf morphism on the slice over `W` induced by an open immersion. -/
def overOverRingCatSheafHom (W : Over f.opensRange) :
    (Y.ringCatSheaf.over f.opensRange).over W ⟶
      ((f.opensRangeOverEquivalence W).functor.sheafPushforwardContinuous RingCat.{u}
        (((Opens.grothendieckTopology Y).over f.opensRange).over W)
      ((Opens.grothendieckTopology X).over
          (f.opensRangeEquivalence.functor.obj W))).obj
        (X.ringCatSheaf.over (f.opensRangeEquivalence.functor.obj W)) :=
  ((((Opens.grothendieckTopology Y).over f.opensRange).overPullback RingCat.{u} W).map
    (((Opens.grothendieckTopology Y).overPullback RingCat.{u} f.opensRange).map
      f.toRingCatSheafHom))

/-- The inverse structure-sheaf morphism on the slice over `W`. -/
noncomputable def ringCatSheafOverToPushforwardOverOver (W : Over f.opensRange) :
    X.ringCatSheaf.over (f.opensRangeEquivalence.functor.obj W) ⟶
      ((f.opensRangeOverEquivalence W).inverse.sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology X).over
          (f.opensRangeEquivalence.functor.obj W))
        (((Opens.grothendieckTopology Y).over f.opensRange).over W)).obj
        ((Y.ringCatSheaf.over f.opensRange).over W) where
  hom :=
    { app := fun V => (forget₂ CommRingCat RingCat).map (f.appIso V.unop.left).inv
      naturality := fun U V g => by
        change
          (forget₂ CommRingCat RingCat).map
                (X.presheaf.map ((Over.forget _).op.map g)) ≫
              (forget₂ CommRingCat RingCat).map (f.appIso V.unop.left).inv =
            (forget₂ CommRingCat RingCat).map (f.appIso U.unop.left).inv ≫
              (forget₂ CommRingCat RingCat).map
                (Y.presheaf.map (f.opensFunctor.op.map ((Over.forget _).op.map g)))
        rw [← Functor.map_comp, ← Functor.map_comp]
        exact congr_arg (fun k => (forget₂ CommRingCat RingCat).map k)
          (f.appIso_inv_naturality ((Over.forget _).op.map g)) }

/-- The module equivalence induced on the slice over `W`. -/
noncomputable def opensRangeOverModulesEquivalence (W : Over f.opensRange) :
    SheafOfModules.{u} (X.ringCatSheaf.over
        (f.opensRangeEquivalence.functor.obj W)) ≌
      SheafOfModules.{u} ((Y.ringCatSheaf.over f.opensRange).over W) :=
  SheafOfModules.pushforwardPushforwardEquivalence (f.opensRangeOverEquivalence W)
    (f.overOverRingCatSheafHom W) (f.ringCatSheafOverToPushforwardOverOver W)
    (by
      ext V x
      exact congr_arg (fun k => k x) (f.appIso_inv_app V.unop.left).symm)
    (by
      ext U x
      change ((f.app U.unop.left.left ≫
        (f.appIso (f ⁻¹ᵁ U.unop.left.left)).inv ≫
          Y.presheaf.map _).hom x) = x
      rw [f.app_appIso_inv_assoc, ← Functor.map_comp]
      let k := (homOfLE (Set.image_preimage_subset f U.unop.left.left.1)).op ≫
        (Over.forget f.opensRange).op.map
          ((Over.forget W).op.map
            ((NatTrans.op (f.opensRangeOverEquivalence W).unit).app U))
      change (Y.presheaf.map k).hom x = x
      rw [show k = 𝟙 _ from Subsingleton.elim _ _]
      exact congr_arg (fun q => q.hom x) (Y.presheaf.map_id _))

/-- The inverse slice equivalence sends the unit module to the unit module. -/
noncomputable def opensRangeOverModulesEquivalenceInverseUnitIso
    (W : Over f.opensRange) :
    (f.opensRangeOverModulesEquivalence W).inverse.obj
        (.unit ((Y.ringCatSheaf.over f.opensRange).over W)) ≅
      .unit (X.ringCatSheaf.over (f.opensRangeEquivalence.functor.obj W)) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun V => ?_) ?_
  · refine
      { hom := ConcreteCategory.ofHom (C := ModuleCat _)
          { toFun := (f.appIso V.unop.left).hom
            map_add' := fun
                (x y : Γ(Y, f ''ᵁ V.unop.left)) =>
              (f.appIso V.unop.left).hom.hom.map_add x y
            map_smul' := fun (r : Γ(X, V.unop.left))
                (x : Γ(Y, f ''ᵁ V.unop.left)) => by
              change (f.appIso V.unop.left).hom ((f.appIso V.unop.left).inv r * x) =
                r * (f.appIso V.unop.left).hom x
              simp }
        inv := ConcreteCategory.ofHom (C := ModuleCat _)
          { toFun := (f.appIso V.unop.left).inv
            map_add' := fun (x y : Γ(X, V.unop.left)) =>
              (f.appIso V.unop.left).inv.hom.map_add x y
            map_smul' := fun (r x : Γ(X, V.unop.left)) => by
              change (f.appIso V.unop.left).inv (r * x) =
                (f.appIso V.unop.left).inv r * (f.appIso V.unop.left).inv x
              simp }
        hom_inv_id := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact Iso.hom_inv_id_apply (C := CommRingCat) (f.appIso V.unop.left) x
        inv_hom_id := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact Iso.inv_hom_id_apply (C := CommRingCat) (f.appIso V.unop.left) x }
  · intro U V g
    let g' := (Over.forget (f.opensRangeEquivalence.functor.obj W)).op.map g
    have h : Y.presheaf.map (f.opensFunctor.op.map g') ≫
        (f.appIso V.unop.left).hom =
        (f.appIso U.unop.left).hom ≫ X.presheaf.map g' := by
      exact f.appIso_hom_naturality g'
    ext x
    exact congr($(h) x)

/-- The forward slice equivalence sends the unit module to the unit module. -/
noncomputable def opensRangeOverModulesEquivalenceUnitIso
    (W : Over f.opensRange) :
    (f.opensRangeOverModulesEquivalence W).functor.obj
        (.unit (X.ringCatSheaf.over (f.opensRangeEquivalence.functor.obj W))) ≅
      .unit ((Y.ringCatSheaf.over f.opensRange).over W) :=
  ((f.opensRangeOverModulesEquivalence W).functor.mapIso
      (f.opensRangeOverModulesEquivalenceInverseUnitIso W)).symm.trans
    ((f.opensRangeOverModulesEquivalence W).counitIso.app _)

/-- Restricting twice and transporting across the slice equivalence agrees with restricting the
scheme-level module and then restricting to an object of its open-set site. -/
noncomputable def restrictOverIso (M : Y.Modules) (W : Over f.opensRange) :
    (f.opensRangeOverModulesEquivalence W).inverse.obj
        ((M.over f.opensRange).over W) ≅
      (M.restrict f).over (f.opensRangeEquivalence.functor.obj W) :=
  Iso.refl _

/-- The forward slice equivalence carries a restriction of the scheme-level restriction back to
the corresponding iterated slice restriction on the target. -/
noncomputable def restrictOverIsoForward (M : Y.Modules) (W : Over f.opensRange) :
    (f.opensRangeOverModulesEquivalence W).functor.obj
        ((M.restrict f).over (f.opensRangeEquivalence.functor.obj W)) ≅
      (M.over f.opensRange).over W :=
  ((f.opensRangeOverModulesEquivalence W).functor.mapIso
      (f.restrictOverIso M W).symm).trans
    ((f.opensRangeOverModulesEquivalence W).counitIso.app _)

/-- The morphism from the restriction of the target's structure sheaf to the structure sheaf
of the source, viewed on the equivalent slice site. -/
def overRingCatSheafHom :
    Y.ringCatSheaf.over f.opensRange ⟶
      (f.opensRangeEquivalence.functor.sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology Y).over f.opensRange)
        (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
  ((Opens.grothendieckTopology Y).overPullback RingCat.{u} f.opensRange).map
    f.toRingCatSheafHom

/-- The inverse structure-sheaf morphism, whose components are the inverse maps on sections
induced by the open immersion. -/
noncomputable def ringCatSheafToPushforwardOver :
    X.ringCatSheaf ⟶
      (f.opensRangeEquivalence.inverse.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X)
        ((Opens.grothendieckTopology Y).over f.opensRange)).obj
        (Y.ringCatSheaf.over f.opensRange) where
  hom :=
    { app := fun U => (forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv
      naturality := fun U V g => by
        change
          (forget₂ CommRingCat RingCat).map (X.presheaf.map g) ≫
              (forget₂ CommRingCat RingCat).map (f.appIso V.unop).inv =
            (forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv ≫
              (forget₂ CommRingCat RingCat).map
                (Y.presheaf.map (f.opensFunctor.op.map g))
        rw [← Functor.map_comp, ← Functor.map_comp, f.appIso_inv_naturality g]
        rfl }

/-- The equivalence between modules on the source of an open immersion and modules on the
slice site over its range. -/
noncomputable def opensRangeModulesEquivalence :
    X.Modules ≌ SheafOfModules.{u} (Y.ringCatSheaf.over f.opensRange) :=
  SheafOfModules.pushforwardPushforwardEquivalence f.opensRangeEquivalence
    f.overRingCatSheafHom f.ringCatSheafToPushforwardOver
    (by
      ext U x
      exact congr_arg (fun k => k x) (f.appIso_inv_app U.unop).symm)
    (by
      ext U x
      change ((f.app U.unop.left ≫ (f.appIso (f ⁻¹ᵁ U.unop.left)).inv ≫
        Y.presheaf.map _).hom x) = x
      rw [f.app_appIso_inv_assoc, ← Functor.map_comp]
      let k := (homOfLE (Set.image_preimage_subset f U.unop.left.1)).op ≫
        (Over.forget f.opensRange).op.map
          ((NatTrans.op f.opensRangeEquivalence.unit).app U)
      change (Y.presheaf.map k).hom x = x
      rw [show k = 𝟙 _ from Subsingleton.elim _ _]
      exact congr_arg (fun q => q.hom x) (Y.presheaf.map_id _))

/-- The inverse open-immersion equivalence sends the unit module on the range slice to the
unit module on the source. -/
noncomputable def opensRangeModulesEquivalenceInverseUnitIso :
    f.opensRangeModulesEquivalence.inverse.obj
        (.unit (Y.ringCatSheaf.over f.opensRange)) ≅
      .unit X.ringCatSheaf := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun U => ?_) ?_
  · refine
      { hom := ConcreteCategory.ofHom (C := ModuleCat _)
          { toFun := (f.appIso U.unop).hom
            map_add' := fun (x y : Γ(Y, f ''ᵁ U.unop)) =>
              (f.appIso U.unop).hom.hom.map_add x y
            map_smul' := fun (r : Γ(X, U.unop)) (x : Γ(Y, f ''ᵁ U.unop)) => by
              change (f.appIso U.unop).hom ((f.appIso U.unop).inv r * x) =
                r * (f.appIso U.unop).hom x
              simp }
        inv := ConcreteCategory.ofHom (C := ModuleCat _)
          { toFun := (f.appIso U.unop).inv
            map_add' := fun (x y : Γ(X, U.unop)) =>
              (f.appIso U.unop).inv.hom.map_add x y
            map_smul' := fun (r x : Γ(X, U.unop)) => by
              change (f.appIso U.unop).inv (r * x) =
                (f.appIso U.unop).inv r * (f.appIso U.unop).inv x
              simp }
        hom_inv_id := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact Iso.hom_inv_id_apply (C := CommRingCat) (f.appIso U.unop) x
        inv_hom_id := by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          exact Iso.inv_hom_id_apply (C := CommRingCat) (f.appIso U.unop) x }
  · intro U V g
    have h : Y.presheaf.map (f.opensFunctor.op.map g) ≫
        (f.appIso V.unop).hom =
        (f.appIso U.unop).hom ≫ X.presheaf.map g := by
      exact f.appIso_hom_naturality g
    ext x
    exact congr($(h) x)

/-- A presentation on the range slice of an open immersion transports to a presentation of the
scheme-level restriction on its source. -/
noncomputable def restrictPresentation (M : Y.Modules)
    (P : (M.over f.opensRange).Presentation) :
    (M.restrict f).Presentation :=
  P.map f.opensRangeModulesEquivalence.inverse
    f.opensRangeModulesEquivalenceInverseUnitIso.symm

/-- Restriction to the slice over the range, transported back across
`opensRangeModulesEquivalence`, agrees with scheme-level restriction. -/
noncomputable def restrictFunctorIsoOver :
    SheafOfModules.overFunctor Y.ringCatSheaf f.opensRange ⋙
        f.opensRangeModulesEquivalence.inverse ≅
      Scheme.Modules.restrictFunctor f :=
  Iso.refl _

-- Needs both budgets raised: it times out in `isDefEq` on the default 200000, and its
-- `HasSheafify` goals for the doubly-sliced site time out on the default 20000 synthesis
-- heartbeats. Scoped with `in` rather than set for the whole file, so a future slowdown in any
-- other declaration surfaces as a failure there instead of being silently absorbed.
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Transport local presentation data on the slice over the range of an open immersion to local
presentation data for the scheme-level restriction. -/
noncomputable def restrictQuasicoherentData (M : Y.Modules)
    (q : (M.over f.opensRange).QuasicoherentData) :
    (M.restrict f).QuasicoherentData where
  I := q.I
  X i := f.opensRangeEquivalence.functor.obj (q.X i)
  coversTop := GrothendieckTopology.CoversTop.map_equivalence q.coversTop
    f.opensRangeEquivalence f.opensRangeEquivalence_functor_coverPreserving
  presentation i :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u}
      (σ := (q.presentation i).map
        (f.opensRangeOverModulesEquivalence (q.X i)).inverse
        (f.opensRangeOverModulesEquivalenceInverseUnitIso (q.X i)).symm)
      (f.restrictOverIso M (q.X i)).hom

-- The mapped index witnesses require the same expensive iterated-slice identifications as the
-- data itself on Mathlib v4.32.
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Transporting finite local presentation data from the range slice to the source preserves
finiteness. -/
instance restrictQuasicoherentData_isFinitePresentation (M : Y.Modules)
    (q : (M.over f.opensRange).QuasicoherentData) [q.IsFinitePresentation] :
    (f.restrictQuasicoherentData M q).IsFinitePresentation where
  isFinite_presentation i := by
    dsimp only [restrictQuasicoherentData] at i ⊢
    let U := f.opensRangeEquivalence.functor.obj (q.X i)
    let hWeak := (inferInstance : ∀ U : X.Opens,
      HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u})
    let hW := (inferInstance : ∀ U : X.Opens,
      ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u})
    apply @SheafOfModules.Presentation.IsFinite.mk (Over U) _
      ((Opens.grothendieckTopology X).over U) (X.ringCatSheaf.over U)
      (hWeak U) (hW U)
    · apply @SheafOfModules.GeneratingSections.IsFiniteType.mk (Over U) _
        ((Opens.grothendieckTopology X).over U) (X.ringCatSheaf.over U)
        (hWeak U) (hW U)
      change Finite (q.presentation i).generators.I
      infer_instance
    · apply @SheafOfModules.GeneratingSections.IsFiniteType.mk (Over U) _
        ((Opens.grothendieckTopology X).over U) (X.ringCatSheaf.over U)
        (hWeak U) (hW U)
      change Finite (q.presentation i).relations.I
      infer_instance

/-- Finite presentation on the range slice implies finite presentation after scheme-level
restriction along the open immersion. -/
theorem isFinitePresentation_restrict (M : Y.Modules)
    (hM : SheafOfModules.IsFinitePresentation.{u, u, u} (M.over f.opensRange)) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (M.restrict f) := by
  obtain ⟨q, hq⟩ := hM.exists_quasicoherentData
  letI := hq
  constructor
  exact ⟨f.restrictQuasicoherentData M q, inferInstance⟩

/-! ### The reverse transport

Everything above carries finite presentation from the range slice to the scheme-level
restriction. This section supplies the other direction, so that finite presentation is
*invariant* under the equivalence rather than merely transported one way.

One asymmetry drives the shape of what follows. The forward direction never round-trips:
`restrictOverIso` is stated at `f.opensRangeEquivalence.functor.obj W` for a `W` taken
straight from the quasicoherent data, so the object is already in the form it is needed in.
The reverse direction must round-trip, because the data now lives on `X.Opens` and its cover
has to be pulled back to `Over f.opensRange`.

That round trip is an *equality* of opens rather than merely an isomorphism —
`opensRangeEquivalence`'s counit is `eqToIso (f.preimage_image_eq _)` — which is what makes it
tractable. It is discharged once, by `subst`, in `presentationOverOfEq`, rather than by a
dependent rewrite at each use site: the ambient category of `(M.restrict f).over U` depends on
`U`, so rewriting `U` after the fact means transporting across a change of category. -/

/-- Transport a presentation of the scheme-level restriction over `U` to a presentation of the
range-slice restriction over `W`, given that `W` maps to `U` under the site equivalence.

The equality hypothesis is what lets `subst` do the dependent work in one place. -/
noncomputable def presentationOverOfEq (M : Y.Modules) (W : Over f.opensRange) (U : X.Opens)
    (h : f.opensRangeEquivalence.functor.obj W = U)
    (P : ((M.restrict f).over U).Presentation) :
    ((M.over f.opensRange).over W).Presentation := by
  subst h
  exact SheafOfModules.Presentation.ofIsIso.{u, u, u}
    (σ := P.map (f.opensRangeOverModulesEquivalence W).functor
      (f.opensRangeOverModulesEquivalenceUnitIso W).symm)
    (f.restrictOverIsoForward M W).hom

/-- The transported presentation is finite when the original is: neither `Presentation.map` nor
`Presentation.ofIsIso` touches the generator and relation index types. -/
instance presentationOverOfEq_isFinite (M : Y.Modules) (W : Over f.opensRange) (U : X.Opens)
    (h : f.opensRangeEquivalence.functor.obj W = U)
    (P : ((M.restrict f).over U).Presentation) [P.IsFinite] :
    (f.presentationOverOfEq M W U h P).IsFinite := by
  subst h
  dsimp only [presentationOverOfEq]
  refine ⟨?_, ?_⟩
  · refine ⟨?_⟩
    change Finite P.generators.I
    infer_instance
  · refine ⟨?_⟩
    change Finite P.relations.I
    infer_instance

/-- Transport local presentation data for the scheme-level restriction back to local
presentation data on the slice over the range. -/
noncomputable def overQuasicoherentData (M : Y.Modules)
    (q : (M.restrict f).QuasicoherentData) :
    (M.over f.opensRange).QuasicoherentData where
  I := q.I
  X i := f.opensRangeEquivalence.inverse.obj (q.X i)
  coversTop := GrothendieckTopology.CoversTop.map_equivalence q.coversTop
    f.opensRangeEquivalence.symm f.opensRangeEquivalence_inverse_coverPreserving
  presentation i :=
    f.presentationOverOfEq M _ (q.X i) (f.preimage_image_eq (q.X i)) (q.presentation i)

/-- Transporting finite local presentation data back to the range slice preserves
finiteness. -/
instance overQuasicoherentData_isFinitePresentation (M : Y.Modules)
    (q : (M.restrict f).QuasicoherentData) [hq : q.IsFinitePresentation] :
    (f.overQuasicoherentData M q).IsFinitePresentation where
  isFinite_presentation i := by
    haveI : (q.presentation i).IsFinite := hq.isFinite_presentation i
    dsimp only [overQuasicoherentData]
    exact f.presentationOverOfEq_isFinite M _ (q.X i) _ (q.presentation i)

/-- Finite presentation after scheme-level restriction along an open immersion implies finite
presentation on the range slice — the converse of `isFinitePresentation_restrict`. -/
theorem isFinitePresentation_over_of_restrict (M : Y.Modules)
    (hM : SheafOfModules.IsFinitePresentation.{u, u, u} (M.restrict f)) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (M.over f.opensRange) := by
  obtain ⟨q, hq⟩ := hM.exists_quasicoherentData
  letI := hq
  constructor
  exact ⟨f.overQuasicoherentData M q, inferInstance⟩

/-- **Finite presentation is invariant under the open-immersion/slice equivalence.**

This is the statement downstream work should quote; the two one-directional theorems remain
available for when only one implication is wanted. -/
theorem isFinitePresentation_over_iff_restrict (M : Y.Modules) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (M.over f.opensRange) ↔
      SheafOfModules.IsFinitePresentation.{u, u, u} (M.restrict f) :=
  ⟨f.isFinitePresentation_restrict M, f.isFinitePresentation_over_of_restrict M⟩

end Scheme.Hom

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- **The restricted sheaf's scalar action is the original one, transported along `appIso`.**

`Scheme.Modules.restrictAppIso` is `Iso.refl`, so both sides live in the same
type and the statement is purely about which action is used.

**This is `rfl`.** `by rfl` proves the statement verbatim; the proof term below
just reads it off Mathlib's form. So it is not a defeq barrier, and reaching for
it is never *forced* — do not read this lemma as evidence that a restricted
scalar action cannot be closed definitionally, because it can.

What it is for is *shape*. Mathlib's `smul_restrictAppIso_hom_apply` states the
same fact with two `restrictAppIso.hom` applications wrapped around it; this
states it bare, so that instantiating it as a `have` hands back an equation whose
sides match a goal written in the obvious way. `Proj.chartUnitToTwist_eq` uses it
exactly so — to move an equation from the restricted action to the original one,
where the pointwise lemma about the original applies.

A caveat on how to *use* it, learned the hard way: `rw` with it will fail on a
goal carrying `show`-ascription residue, which Lean reports as the goal being
"not type-correct under the `instances` transparency level". That is a property
of the goal, not of this lemma. Instantiate it at explicit arguments as a `have`
and combine with `Eq.trans`. -/
theorem restrict_smul_eq {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : X.Opens) (r : Γ(X, U)) (x : Γ(M.restrict f, U)) :
    (r • x : Γ(M.restrict f, U))
      = (show Γ(Y, f ''ᵁ U) from (Scheme.Hom.appIso f U).inv.hom r) •
        (show Γ(M, f ''ᵁ U) from x) :=
  Scheme.Modules.smul_restrictAppIso_hom_apply f M U r x

end AlgebraicGeometry.Scheme.Modules
