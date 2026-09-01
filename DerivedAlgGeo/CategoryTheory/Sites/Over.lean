/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Over

/-!
# Cocontinuity on over categories

Cocontinuity of a functor between arbitrary sites passes to the induced functor between their
over categories. This construction is independent of any geometric realization of the sites.
-/

universe u

open CategoryTheory

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
