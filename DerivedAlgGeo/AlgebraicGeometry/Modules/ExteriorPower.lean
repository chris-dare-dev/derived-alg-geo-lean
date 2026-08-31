/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.Modules.ExteriorPower
import DerivedAlgGeo.LinearAlgebra.ExteriorPower.Top
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Exterior powers of sheaves of modules

This geometric consumer sheafifies the categorical objectwise exterior power
from `CategoryTheory/Sites/Sheaves/Modules/ExteriorPower.lean`. It also proves
that the top exterior power of a free rank-`n` module sheaf is the structure
sheaf. The semilinear algebra and free-module calculations live under
`LinearAlgebra/ExteriorPower/`.
-/

open CategoryTheory Limits LinearMap

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

local instance exteriorPowerCategory : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

/-- The exterior power of a sheaf of modules, obtained by sheafifying the objectwise exterior
power presheaf. -/
noncomputable def exteriorPower (E : X.Modules) (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModules.exteriorPower X.presheaf
      ((SheafOfModules.forget X.ringCatSheaf).obj E) n)

/-- Exterior powers carry isomorphic module sheaves to isomorphic module sheaves. -/
noncomputable def exteriorPowerMapIso {E F : X.Modules} (e : E ≅ F) (n : ℕ) :
    exteriorPower E n ≅ exteriorPower F n :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (PresheafOfModules.exteriorPower.mapIso
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e) n)

/-- The sheafification unit defining the exterior power of a sheaf of modules. -/
noncomputable def exteriorPowerSheafification (E : X.Modules) (n : ℕ) :
    PresheafOfModules.exteriorPower X.presheaf
        ((SheafOfModules.forget X.ringCatSheaf).obj E) n ⟶
      (SheafOfModules.forget X.ringCatSheaf).obj (exteriorPower E n) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.app _

private noncomputable def freeAppIsoFinsupp
    (I : Type u) [Finite I] (U : X.Opensᵒᵖ) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).val.obj U ≅
      ModuleCat.of (X.presheaf.obj U) (I →₀ X.presheaf.obj U) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf U
  letI : (SheafOfModules.evaluation X.ringCatSheaf U).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  haveI : PreservesColimit (Functor.const (Discrete I) |>.obj
      (SheafOfModules.unit X.ringCatSheaf)) F := by
    infer_instance
  exact IsColimit.coconePointUniqueUpToIso
    (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan I))
    (ModuleCat.finsuppCoconeIsColimit
      (X.presheaf.obj U) (X.presheaf.obj U) I)

private lemma freeAppIsoFinsupp_ιFree
    (I : Type u) [Finite I] (U : X.Opensᵒᵖ)
    (i : I) (r : X.presheaf.obj U) :
    (freeAppIsoFinsupp (X := X) I U).hom
        ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app U r) =
      Finsupp.single i r := by
  let F := SheafOfModules.evaluation X.ringCatSheaf U
  letI : (SheafOfModules.evaluation X.ringCatSheaf U).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  haveI : PreservesColimit (Functor.const (Discrete I) |>.obj
      (SheafOfModules.unit X.ringCatSheaf)) F := by
    infer_instance
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan I))
    (ModuleCat.finsuppCoconeIsColimit
      (X.presheaf.obj U) (X.presheaf.obj U) I) (Discrete.mk i)
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) r

private noncomputable def constantType (I : Type u) :=
  (Functor.const X.Opensᵒᵖ).obj I

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def freeForgetIso (I : Type u) [Finite I] :
    (SheafOfModules.forget X.ringCatSheaf).obj
        (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
        (constantType (X := X) I) :=
  PresheafOfModules.isoMk (fun U ↦ freeAppIsoFinsupp (X := X) I U) (by
    intro U V f
    rw [← cancel_epi (freeAppIsoFinsupp (X := X) I U).inv]
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext
    intro r
    simp only [Iso.inv_hom_id_assoc]
    change (freeAppIsoFinsupp (X := X) I V).hom
        (((SheafOfModules.forget X.ringCatSheaf).obj
          (SheafOfModules.free (R := X.ringCatSheaf) I)).map f
            ((freeAppIsoFinsupp (X := X) I U).inv (Finsupp.single i r))) =
      (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
        (constantType (X := X) I)).map f (Finsupp.single i r)
    have hinv : (freeAppIsoFinsupp (X := X) I U).inv
          (Finsupp.single i r) =
        (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app U r := by
      apply (freeAppIsoFinsupp (X := X) I U).toLinearEquiv.injective
      exact (freeAppIsoFinsupp (X := X) I U).toLinearEquiv.apply_symm_apply _ |>.trans
        (freeAppIsoFinsupp_ιFree (X := X) I U i r).symm
    rw [hinv]
    change (freeAppIsoFinsupp (X := X) I V).hom
        ((SheafOfModules.free (R := X.ringCatSheaf) I).val.map f
          ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app U r)) = _
    have hn := PresheafOfModules.naturality_apply
      (SheafOfModules.ιFree (R := X.ringCatSheaf) i).val f r
    rw [← hn]
    rw [freeAppIsoFinsupp_ιFree]
    change Finsupp.single i (X.presheaf.map f r) =
      (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
        (constantType (X := X) I)).map f (Finsupp.single i r)
    conv_rhs => rw [← Finsupp.smul_single_one i r]
    rw [PresheafOfModules.map_smul]
    dsimp only [PresheafOfModules.freeObj, constantType]
    rw [show Finsupp.single i (1 : X.presheaf.obj U) =
      ModuleCat.freeMk i from rfl]
    rw [ModuleCat.freeDesc_apply]
    change Finsupp.single i (X.ringCatSheaf.obj.map f r) =
      X.ringCatSheaf.obj.map f r •
        (Finsupp.single i 1 : I →₀ X.ringCatSheaf.obj.obj V)
    simp)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def topExteriorFreePresheafIso (n : ℕ) :
    PresheafOfModules.exteriorPower X.presheaf
        (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
          (constantType (X := X) (ULift.{u} (Fin n)))) n ≅
      PresheafOfModules.unit X.ringCatSheaf.obj :=
  PresheafOfModules.isoMk (fun U ↦
    (Module.topExteriorFreeEquiv (X.presheaf.obj U) n).toModuleIso) (by
      intro U V f
      apply ModuleCat.exteriorPower.hom_ext
      ext x
      change Module.topExteriorFreeEquiv (X.presheaf.obj V) n
          (LinearMap.exteriorPower n (X.presheaf.map f).hom
            ((PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
              (constantType (X := X) (ULift.{u} (Fin n)))).restrictₛₗ f)
            (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n x)) =
        X.presheaf.map f
          (Module.topExteriorFreeEquiv (X.presheaf.obj U) n
            (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n x))
      rw [LinearMap.exteriorPower_ιMulti]
      change Module.topExteriorFreeEquiv (X.presheaf.obj V) n
          (_root_.exteriorPower.ιMulti (X.presheaf.obj V) n
            (((PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
              (constantType (X := X) (ULift.{u} (Fin n)))).restrictₛₗ f) ∘ x)) =
        X.presheaf.map f
          (Module.topExteriorFreeEquiv (X.presheaf.obj U) n
            (_root_.exteriorPower.ιMulti (X.presheaf.obj U) n x))
      rw [Module.topExteriorFreeEquiv_ιMulti, Module.topExteriorFreeEquiv_ιMulti]
      let σ := (X.presheaf.map f).hom
      have hmap (y : ULift.{u} (Fin n) →₀ X.presheaf.obj U) :
          (show ULift.{u} (Fin n) →₀ X.presheaf.obj V from
            (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
              (constantType (X := X) (ULift.{u} (Fin n)))).map f y) =
            Finsupp.mapRange σ σ.map_zero y := by
        induction y using Finsupp.induction with
        | zero => simp
        | single_add a r y _ha _hr ih =>
            rw [map_add]
            rw [Finsupp.mapRange_add σ.map_add]
            apply congrArg₂ (fun p q ↦ p + q)
            · conv_lhs => rw [← Finsupp.smul_single_one a r]
              rw [PresheafOfModules.map_smul]
              dsimp only [PresheafOfModules.freeObj, constantType]
              rw [show Finsupp.single a (1 : X.presheaf.obj U) =
                ModuleCat.freeMk a from rfl]
              rw [ModuleCat.freeDesc_apply]
              simp only [Finsupp.mapRange_single]
              simp only [Functor.const_obj_map]
              change (X.ringCatSheaf.obj.map f) r • Finsupp.single a 1 =
                Finsupp.single a ((X.ringCatSheaf.obj.map f) r)
              rw [Finsupp.smul_single_one]
            · exact ih
      have hentry (i j : Fin n) :
          (show ULift.{u} (Fin n) →₀ X.presheaf.obj V from
            (((PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
              (constantType (X := X) (ULift.{u} (Fin n)))).restrictₛₗ f) ∘ x) i)
              (Set.powersetCard.ofFinEmbEquiv.symm (Module.topPowerset.{u} n) j) =
            σ ((show ULift.{u} (Fin n) →₀ X.presheaf.obj U from x i)
              (Set.powersetCard.ofFinEmbEquiv.symm (Module.topPowerset.{u} n) j)) := by
        change (show ULift.{u} (Fin n) →₀ X.presheaf.obj V from
          (PresheafOfModules.freeObj (R := X.ringCatSheaf.obj)
            (constantType (X := X) (ULift.{u} (Fin n)))).map f (x i)) _ = _
        rw [hmap]
        simp
      simp_rw [hentry]
      exact (σ.map_det _).symm)

set_option maxHeartbeats 1600000 in
/-- The top exterior power of the free rank-`n` module sheaf is the structure sheaf. -/
noncomputable def topExteriorFreeIso (n : ℕ) :
    exteriorPower
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) n ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (PresheafOfModules.exteriorPower.mapIso
        (freeForgetIso (X := X) (ULift.{u} (Fin n))) n ≪≫
        topExteriorFreePresheafIso (X := X) n) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app
        (SheafOfModules.unit X.ringCatSheaf)

end

end AlgebraicGeometry.Scheme.Modules
