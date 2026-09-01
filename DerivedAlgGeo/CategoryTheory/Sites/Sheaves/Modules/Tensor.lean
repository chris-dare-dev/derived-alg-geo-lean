/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.CoversTop
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.Invertible
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Tensor descent for invertible module sheaves on a ringed site

Tensoring a module-presheaf morphism with a locally free rank-one module sheaf preserves the
local equivalences inverted by sheafification. The proof works on an arbitrary Grothendieck site:
local surjectivity is preserved by tensoring, while local injectivity is checked on a covering
family where the rank-one factor is identified with the unit.

The stalkwise strengthening available on topological spaces, which removes the rank-one
hypothesis, lives in `DerivedAlgGeo.Topology.Sheaves.ModuleTensor`.
-/

open CategoryTheory Limits MonoidalCategory

universe u v u₁ v₁

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

noncomputable section

section CommRing

variable {S : Cᵒᵖ ⥤ CommRingCat.{u}}

local instance : MonoidalCategory
    (PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.monoidalCategory (R := S)

set_option pp.universes false in
omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Tensoring on the left preserves local surjectivity on an arbitrary site. -/
lemma isLocallySurjective_whiskerLeft
    (F : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    {G₁ G₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    (g : G₁ ⟶ G₂)
    [Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map g)] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (F ◁ g)) := by
  constructor
  intro U z
  induction z using TensorProduct.induction_on with
  | zero =>
      have h : Presheaf.imageSieve
          ((PresheafOfModules.toPresheaf _).map (F ◁ g))
          (((PresheafOfModules.toPresheaf _).map (F ◁ g)).app (.op U) 0) ∈ J U := by
        rw [Presheaf.imageSieve_app]
        exact J.top_mem _
      rw [map_zero] at h
      exact h
  | tmul x y =>
      apply J.superset_covering
        (S := Presheaf.imageSieve ((PresheafOfModules.toPresheaf _).map g) y)
      · intro V f hf
        let y' : ToType (((PresheafOfModules.toPresheaf _).obj G₂).obj (.op U)) := y
        let y₁' : ToType (((PresheafOfModules.toPresheaf _).obj G₁).obj (.op V)) :=
          Presheaf.localPreimage ((PresheafOfModules.toPresheaf _).map g) y' f hf
        let y₁ : G₁.obj (.op V) := y₁'
        let z₁ : (F ⊗ G₁).obj (.op V) := F.restrictₛₗ f.op x ⊗ₜ y₁
        refine ⟨z₁, ?_⟩
        change (F ◁ g).app (.op V) z₁ = (F ⊗ G₂).map f.op (x ⊗ₜ y)
        rw [PresheafOfModules.whiskerLeft_app]
        dsimp only [z₁]
        erw [ModuleCat.MonoidalCategory.whiskerLeft_apply,
          PresheafOfModules.Monoidal.tensorObj_map_tmul]
        change F.restrictₛₗ f.op x ⊗ₜ _ =
          F.restrictₛₗ f.op x ⊗ₜ G₂.restrictₛₗ f.op y
        congr 1
        exact Presheaf.app_localPreimage
          ((PresheafOfModules.toPresheaf _).map g) y' f hf
      · exact Presheaf.imageSieve_mem J
          ((PresheafOfModules.toPresheaf _).map g) y
  | add z₁ z₂ hz₁ hz₂ =>
      apply J.superset_covering
        (S := Presheaf.imageSieve
            ((PresheafOfModules.toPresheaf _).map (F ◁ g)) z₁ ⊓
          Presheaf.imageSieve
            ((PresheafOfModules.toPresheaf _).map (F ◁ g)) z₂)
      · intro V f hf
        refine ⟨Presheaf.localPreimage
            ((PresheafOfModules.toPresheaf _).map (F ◁ g)) z₁ f hf.1 +
          Presheaf.localPreimage
            ((PresheafOfModules.toPresheaf _).map (F ◁ g)) z₂ f hf.2, ?_⟩
        rw [map_add, Presheaf.app_localPreimage, Presheaf.app_localPreimage]
        exact (map_add _ _ _).symm
      · exact J.intersection_covering hz₁ hz₂

omit [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Tensoring on the left by an object isomorphic to the unit preserves local injectivity. -/
lemma isLocallyInjective_whiskerLeft_of_isoUnit
    (F : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat))
    (e : 𝟙_ _ ≅ F)
    {G₁ G₂ : PresheafOfModules.{u} (S ⋙ forget₂ CommRingCat RingCat)}
    (g : G₁ ⟶ G₂)
    [Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map g)] :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (F ◁ g)) := by
  let e₁ : F ⊗ G₁ ≅ G₁ := MonoidalCategory.tensorIso e.symm (Iso.refl G₁) ≪≫ λ_ G₁
  let e₂ : F ⊗ G₂ ≅ G₂ := MonoidalCategory.tensorIso e.symm (Iso.refl G₂) ≪≫ λ_ G₂
  have hfg : F ◁ g = e₁.hom ≫ g ≫ e₂.inv := by
    rw [← cancel_mono e₂.hom]
    dsimp only [e₁, e₂]
    simp
    rw [← Category.assoc, MonoidalCategory.whisker_exchange]
    rw [Category.assoc, MonoidalCategory.leftUnitor_naturality]
  rw [hfg, Functor.map_comp, Functor.map_comp]
  infer_instance

end CommRing

section LocallyRankOne

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
  {S : Sheaf K CommRingCat.{u}}
  [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasWeakSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

private abbrev ringSheaf (S : Sheaf K CommRingCat.{u}) : Sheaf K RingCat.{u} :=
  (sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S

local instance : MonoidalCategory
    (PresheafOfModules.{u} (ringSheaf S).obj) :=
  PresheafOfModules.monoidalCategory (R := S.obj)

local instance : SymmetricCategory
    (PresheafOfModules.{u} (ringSheaf S).obj) :=
  PresheafOfModules.symmetricCategory (R := S.obj)

set_option maxHeartbeats 400000 in
omit [HasWeakSheafify K AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- Tensoring by a locally free rank-one module sheaf preserves local injectivity. -/
lemma isLocallyInjective_whiskerLeft_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    {G₁ G₂ : PresheafOfModules.{u} (ringSheaf S).obj}
    (g : G₁ ⟶ G₂)
    [Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map g)] :
    Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map (M.val ◁ g)) := by
  apply Presheaf.isLocallyInjective_of_coversTop _ q.X q.coversTop
  intro i
  let F := PresheafOfModules.pushforward
    (𝟙 ((ringSheaf S).over (q.X i)).obj)
  let g' := F.map g
  letI : MonoidalCategory
      (PresheafOfModules.{u}
        ((ringSheaf S).over (q.X i)).obj) :=
    PresheafOfModules.monoidalCategory (R := (S.over (q.X i)).obj)
  haveI hg' : Presheaf.IsLocallyInjective (K.over (q.X i))
      ((PresheafOfModules.toPresheaf _).map g') := by
    haveI : Presheaf.IsLocallyInjective (K.over (q.X i))
        (Functor.whiskerLeft (Over.forget (q.X i)).op
          ((PresheafOfModules.toPresheaf _).map g)) :=
      Presheaf.isLocallyInjective_whisker (K.over (q.X i)) K
        (Over.forget (q.X i)) _
    change Presheaf.IsLocallyInjective (K.over (q.X i))
      (Functor.whiskerLeft (Over.forget (q.X i)).op
        ((PresheafOfModules.toPresheaf _).map g))
    infer_instance
  let e := q.rankOneTrivialization hq i
  let ep := (SheafOfModules.forget ((ringSheaf S).over (q.X i))).mapIso e
  haveI : Presheaf.IsLocallyInjective (K.over (q.X i))
      ((PresheafOfModules.toPresheaf
        ((S.over (q.X i)).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map g') := by
    change Presheaf.IsLocallyInjective (K.over (q.X i))
      ((PresheafOfModules.toPresheaf ((ringSheaf S).over (q.X i)).obj).map g')
    exact hg'
  have hlocal := isLocallyInjective_whiskerLeft_of_isoUnit
    (J := K.over (q.X i)) (S := (S.over (q.X i)).obj)
    ((M.over (q.X i)).val) ep g'
  exact hlocal

set_option maxHeartbeats 400000 in
omit [HasWeakSheafify K AddCommGrpCat.{u}] in
/-- Tensoring by a locally free rank-one module sheaf preserves sheafification equivalences. -/
lemma W_whiskerLeft_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    {G₁ G₂ : PresheafOfModules.{u} (ringSheaf S).obj}
    (g : G₁ ⟶ G₂)
    (hg : K.W ((PresheafOfModules.toPresheaf _).map g)) :
    K.W ((PresheafOfModules.toPresheaf _).map (M.val ◁ g)) := by
  letI : Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map g) := hg.isLocallyInjective
  letI : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf _).map g) := hg.isLocallySurjective
  letI : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf
        (S.obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})).map g) := by
    change Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf (ringSheaf S).obj).map g)
    infer_instance
  letI : Presheaf.IsLocallyInjective K
      ((PresheafOfModules.toPresheaf _).map (M.val ◁ g)) :=
    isLocallyInjective_whiskerLeft_of_rankOneData q hq g
  letI : Presheaf.IsLocallySurjective K
      ((PresheafOfModules.toPresheaf _).map (M.val ◁ g)) :=
    isLocallySurjective_whiskerLeft (S := S.obj) M.val g
  exact K.W_of_isLocallyBijective _

set_option maxHeartbeats 400000 in
/-- Sheafification sends the left-whiskered local equivalence to an isomorphism. -/
lemma isIso_sheafification_map_whiskerLeft_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    {G₁ G₂ : PresheafOfModules.{u} (ringSheaf S).obj}
    (g : G₁ ⟶ G₂)
    (hg : K.W ((PresheafOfModules.toPresheaf _).map g)) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringSheaf S).obj)).map (M.val ◁ g)) := by
  apply Localization.inverts
    (PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj))
    (K.W.inverseImage (PresheafOfModules.toPresheaf (ringSheaf S).obj))
  exact W_whiskerLeft_of_rankOneData q hq g hg

set_option maxHeartbeats 400000 in
/-- Sheafification sends the right-whiskered local equivalence to an isomorphism. -/
lemma isIso_sheafification_map_whiskerRight_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    {G₁ G₂ : PresheafOfModules.{u} (ringSheaf S).obj}
    (g : G₁ ⟶ G₂)
    (hg : K.W ((PresheafOfModules.toPresheaf _).map g)) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringSheaf S).obj)).map (g ▷ M.val)) := by
  let a := PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)
  haveI : IsIso (a.map (M.val ◁ g)) :=
    isIso_sheafification_map_whiskerLeft_of_rankOneData q hq g hg
  have hgm : g ▷ M.val =
      (β_ G₁ M.val).hom ≫ (M.val ◁ g) ≫ (β_ M.val G₂).hom := by
    rw [← cancel_mono (β_ G₂ M.val).hom]
    simp
  rw [hgm, Functor.map_comp, Functor.map_comp]
  infer_instance

set_option maxHeartbeats 400000 in
/-- Sheafification inverts left whiskering of its unit by a rank-one module sheaf. -/
lemma isIso_sheafification_map_whiskerLeft_unit_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    (P : PresheafOfModules.{u} (ringSheaf S).obj) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringSheaf S).obj)).map
        (M.val ◁ (PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheaf S).obj)).unit.app P)) := by
  apply isIso_sheafification_map_whiskerLeft_of_rankOneData q hq
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact K.W_toSheafify P.presheaf

set_option maxHeartbeats 400000 in
/-- Sheafification inverts right whiskering of its unit by a rank-one module sheaf. -/
lemma isIso_sheafification_map_whiskerRight_unit_of_rankOneData
    {M : SheafOfModules.{u} (ringSheaf S)}
    (q : M.LocalGeneratorsData) [q.IsLocallyFreeData] (hq : q.IsRankOne)
    (P : PresheafOfModules.{u} (ringSheaf S).obj) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringSheaf S).obj)).map
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (ringSheaf S).obj)).unit.app P ▷ M.val)) := by
  apply isIso_sheafification_map_whiskerRight_of_rankOneData q hq
  rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
  exact K.W_toSheafify P.presheaf

end LocallyRankOne

end


end SheafOfModules
