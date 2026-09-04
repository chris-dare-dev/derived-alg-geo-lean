/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.ExteriorPower.Semilinear
import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Exterior powers of presheaves of modules

The exterior power of a presheaf of modules is defined objectwise, using the
semilinear exterior powers of its restriction maps. This construction is valid
over an arbitrary category and ring presheaf; geometric sheafifications belong
in their corresponding consumer layer.
-/

open CategoryTheory LinearMap

universe u v w w'

namespace PresheafOfModules

variable {C : Type w} [Category.{w'} C]
variable (A : Cᵒᵖ ⥤ CommRingCat.{u})

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The objectwise exterior power of a presheaf of modules. Its restriction maps are the
semilinear exterior powers of the original restriction maps. -/
@[simps obj]
noncomputable def exteriorPower
    (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) (n : ℕ) :
    PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) where
  obj U := (Q.obj U).exteriorPower n
  map {U V} f := by
    let g := LinearMap.exteriorPower n
      ((A ⋙ forget₂ CommRingCat RingCat).map f).hom (Q.restrictₛₗ f)
    exact ModuleCat.semilinearMapAddEquiv
      ((A ⋙ forget₂ CommRingCat RingCat).map f).hom _ _ g
  map_id U := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    dsimp
    change LinearMap.exteriorPower n (A.map (𝟙 U)).hom (Q.restrictₛₗ (𝟙 U))
      (_root_.exteriorPower.ιMulti (A.obj U) n x) =
      _root_.exteriorPower.ιMulti (A.obj U) n x
    rw [LinearMap.exteriorPower_ιMulti]
    congr 1
    funext i
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (Q.map_id U)) (x i)
  map_comp f g := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    dsimp
    change LinearMap.exteriorPower n (A.map (f ≫ g)).hom (Q.restrictₛₗ (f ≫ g))
      (_root_.exteriorPower.ιMulti (A.obj _) n x) = _
    rw [LinearMap.exteriorPower_ιMulti]
    change _root_.exteriorPower.ιMulti (A.obj _) n ((Q.restrictₛₗ (f ≫ g)) ∘ x) =
      LinearMap.exteriorPower n (A.map g).hom (Q.restrictₛₗ g)
        (LinearMap.exteriorPower n (A.map f).hom (Q.restrictₛₗ f)
          (_root_.exteriorPower.ιMulti (A.obj _) n x))
    rw [LinearMap.exteriorPower_ιMulti, LinearMap.exteriorPower_ιMulti]
    congr 1
    funext i
    exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (Q.map_comp f g)) (x i)

namespace exteriorPower

variable {A}
variable {Q Q' Q'' : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)}

set_option backward.isDefEq.respectTransparency false in
/-- Exterior power is functorial in morphisms of presheaves of modules. -/
noncomputable def map (f : Q ⟶ Q') (n : ℕ) :
    PresheafOfModules.exteriorPower A Q n ⟶
      PresheafOfModules.exteriorPower A Q' n where
  app U := ModuleCat.exteriorPower.map (f.app U) n
  naturality {U V} g := by
    apply ModuleCat.exteriorPower.hom_ext
    ext x
    dsimp [PresheafOfModules.exteriorPower]
    rw [ModuleCat.semilinearMapAddEquiv_apply,
      ModuleCat.semilinearMapAddEquiv_apply, ModuleCat.exteriorPower.map_mk]
    change ModuleCat.exteriorPower.map (f.app V) n
        (LinearMap.exteriorPower n (A.map g).hom (Q.restrictₛₗ g)
          (_root_.exteriorPower.ιMulti (A.obj U) n x)) =
      LinearMap.exteriorPower n (A.map g).hom (Q'.restrictₛₗ g)
        (_root_.exteriorPower.ιMulti (A.obj U) n (f.app U ∘ x))
    rw [LinearMap.exteriorPower_ιMulti]
    erw [ModuleCat.exteriorPower.map_mk]
    rw [LinearMap.exteriorPower_ιMulti]
    congr 1
    funext i
    exact DFunLike.congr_fun
      (ModuleCat.hom_ext_iff.mp (f.naturality g)) (x i)

@[simp]
theorem map_app_ιMulti (f : Q ⟶ Q') (n : ℕ) (U : Cᵒᵖ) (x : Fin n → Q.obj U) :
    (map f n).app U (ModuleCat.exteriorPower.mk x) =
      ModuleCat.exteriorPower.mk (f.app U ∘ x) :=
  ModuleCat.exteriorPower.map_mk _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_id (Q : PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat)) (n : ℕ) :
    map (𝟙 Q) n = 𝟙 (PresheafOfModules.exteriorPower A Q n) := by
  ext U : 1
  exact (ModuleCat.exteriorPower.functor (A.obj U) n).map_id (Q.obj U)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_comp (f : Q ⟶ Q') (g : Q' ⟶ Q'') (n : ℕ) :
    map (f ≫ g) n = map f n ≫ map g n := by
  ext U : 1
  exact (ModuleCat.exteriorPower.functor (A.obj U) n).map_comp (f.app U) (g.app U)

/-- Exterior power sends an isomorphism of presheaves to an isomorphism. -/
noncomputable def mapIso (e : Q ≅ Q') (n : ℕ) :
    PresheafOfModules.exteriorPower A Q n ≅
      PresheafOfModules.exteriorPower A Q' n where
  hom := map e.hom n
  inv := map e.inv n
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

end exteriorPower

/-- Exterior power as an endofunctor on presheaves of modules. -/
noncomputable def exteriorPowerFunctor (n : ℕ) :
    PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (A ⋙ forget₂ CommRingCat RingCat) where
  obj Q := exteriorPower A Q n
  map f := exteriorPower.map f n
  map_id Q := exteriorPower.map_id Q n
  map_comp f g := exteriorPower.map_comp f g n

end PresheafOfModules
