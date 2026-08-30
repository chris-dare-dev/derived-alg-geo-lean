/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.ExteriorPower
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Basic

/-!
# Restriction and exterior powers

This file compares restriction of a sheaf exterior power with the sheafification of the
objectwise exterior power on the restricted site.
-/

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

local instance exteriorPowerRestrictionCategory : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

private abbrev overPresheafFunctor (X : Scheme.{u}) (U : X.Opens) :=
  PresheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U).obj)

private noncomputable def overFreeAppIsoFinsupp
    (U : X.Opens) (I : Type u) [Finite I] (V : (Over U)ᵒᵖ) :
    (SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.obj V ≅
      ModuleCat.of ((X.sheaf.over U).obj.obj V)
        (I →₀ (X.sheaf.over U).obj.obj V) := by
  let F := SheafOfModules.evaluation (X.ringCatSheaf.over U) V
  letI : (SheafOfModules.evaluation (X.ringCatSheaf.over U) V).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  haveI : PreservesColimit (Functor.const (Discrete I) |>.obj
      (SheafOfModules.unit (X.ringCatSheaf.over U))) F := by
    infer_instance
  exact IsColimit.coconePointUniqueUpToIso
    (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan I))
    (ModuleCat.finsuppCoconeIsColimit
      ((X.sheaf.over U).obj.obj V) ((X.sheaf.over U).obj.obj V) I)

private lemma overFreeAppIsoFinsupp_ιFree
    (U : X.Opens) (I : Type u) [Finite I] (V : (Over U)ᵒᵖ)
    (i : I) (r : (X.sheaf.over U).obj.obj V) :
    (overFreeAppIsoFinsupp (X := X) U I V).hom
        ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i).val.app V r) =
      Finsupp.single i r := by
  let F := SheafOfModules.evaluation (X.ringCatSheaf.over U) V
  letI : (SheafOfModules.evaluation (X.ringCatSheaf.over U) V).Additive := by
    dsimp [SheafOfModules.evaluation]
    infer_instance
  haveI : PreservesColimit (Functor.const (Discrete I) |>.obj
      (SheafOfModules.unit (X.ringCatSheaf.over U))) F := by
    infer_instance
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (isColimitOfPreserves F (SheafOfModules.isColimitFreeCofan I))
    (ModuleCat.finsuppCoconeIsColimit
      ((X.sheaf.over U).obj.obj V) ((X.sheaf.over U).obj.obj V) I) (Discrete.mk i)
  exact DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp h) r

private noncomputable def overConstantType (U : X.Opens) (I : Type u) :=
  (Functor.const (Over U)ᵒᵖ).obj I

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def overFreeForgetIso (U : X.Opens)
    (I : Type u) [Finite I] :
    (SheafOfModules.forget (X.ringCatSheaf.over U)).obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I) ≅
      PresheafOfModules.freeObj (R := (X.ringCatSheaf.over U).obj)
        (overConstantType (X := X) U I) :=
  PresheafOfModules.isoMk
    (fun V ↦ overFreeAppIsoFinsupp (X := X) U I V) (by
      intro V W f
      rw [← cancel_epi (overFreeAppIsoFinsupp (X := X) U I V).inv]
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext'
      intro i
      apply LinearMap.ext
      intro r
      simp only [Iso.inv_hom_id_assoc]
      change (overFreeAppIsoFinsupp (X := X) U I W).hom
          (((SheafOfModules.forget (X.ringCatSheaf.over U)).obj
            (SheafOfModules.free (R := X.ringCatSheaf.over U) I)).map f
              ((overFreeAppIsoFinsupp (X := X) U I V).inv (Finsupp.single i r))) =
        (PresheafOfModules.freeObj (R := (X.ringCatSheaf.over U).obj)
          (overConstantType (X := X) U I)).map f (Finsupp.single i r)
      have hinv : (overFreeAppIsoFinsupp (X := X) U I V).inv
            (Finsupp.single i r) =
          (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i).val.app V r := by
        apply (overFreeAppIsoFinsupp (X := X) U I V).toLinearEquiv.injective
        exact (overFreeAppIsoFinsupp (X := X) U I V).toLinearEquiv.apply_symm_apply _ |>.trans
          (overFreeAppIsoFinsupp_ιFree (X := X) U I V i r).symm
      rw [hinv]
      change (overFreeAppIsoFinsupp (X := X) U I W).hom
          ((SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.map f
            ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i).val.app V r)) = _
      have hn := PresheafOfModules.naturality_apply
        (SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i).val f r
      rw [← hn]
      rw [overFreeAppIsoFinsupp_ιFree]
      change Finsupp.single i ((X.sheaf.over U).obj.map f r) =
        (PresheafOfModules.freeObj (R := (X.ringCatSheaf.over U).obj)
          (overConstantType (X := X) U I)).map f (Finsupp.single i r)
      conv_rhs => rw [← Finsupp.smul_single_one i r]
      rw [PresheafOfModules.map_smul]
      dsimp only [PresheafOfModules.freeObj, overConstantType]
      rw [show Finsupp.single i (1 : (X.sheaf.over U).obj.obj V) =
        ModuleCat.freeMk i from rfl]
      rw [ModuleCat.freeDesc_apply]
      change Finsupp.single i ((X.ringCatSheaf.over U).obj.map f r) =
        (X.ringCatSheaf.over U).obj.map f r •
          (Finsupp.single i 1 : I →₀ (X.ringCatSheaf.over U).obj.obj W)
      simp)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private noncomputable def topExteriorFreeOverPresheafIso
    (U : X.Opens) (n : ℕ) :
    PresheafOfModules.exteriorPower (X.sheaf.over U).obj
        (PresheafOfModules.freeObj (R := (X.ringCatSheaf.over U).obj)
          (overConstantType (X := X) U (ULift.{u} (Fin n)))) n ≅
      PresheafOfModules.unit (X.ringCatSheaf.over U).obj :=
  PresheafOfModules.isoMk (fun V ↦
    (topExteriorFreeEquiv ((X.sheaf.over U).obj.obj V) n).toModuleIso) (by
      intro V W f
      apply ModuleCat.exteriorPower.hom_ext
      ext x
      change topExteriorFreeEquiv ((X.sheaf.over U).obj.obj W) n
          (LinearMap.exteriorPower n ((X.sheaf.over U).obj.map f).hom
            ((PresheafOfModules.freeObj (R := (X.ringCatSheaf.over U).obj)
              (overConstantType (X := X) U (ULift.{u} (Fin n)))).restrictₛₗ f)
            (_root_.exteriorPower.ιMulti ((X.sheaf.over U).obj.obj V) n x)) =
        (X.sheaf.over U).obj.map f
          (topExteriorFreeEquiv ((X.sheaf.over U).obj.obj V) n
            (_root_.exteriorPower.ιMulti ((X.sheaf.over U).obj.obj V) n x))
      rw [LinearMap.exteriorPower_ιMulti]
      change topExteriorFreeEquiv ((X.sheaf.over U).obj.obj W) n
          (_root_.exteriorPower.ιMulti ((X.sheaf.over U).obj.obj W) n
            (((PresheafOfModules.freeObj (R := (X.ringCatSheaf.over U).obj)
              (overConstantType (X := X) U (ULift.{u} (Fin n)))).restrictₛₗ f) ∘ x)) =
        (X.sheaf.over U).obj.map f
          (topExteriorFreeEquiv ((X.sheaf.over U).obj.obj V) n
            (_root_.exteriorPower.ιMulti ((X.sheaf.over U).obj.obj V) n x))
      rw [topExteriorFreeEquiv_ιMulti, topExteriorFreeEquiv_ιMulti]
      let σ := ((X.sheaf.over U).obj.map f).hom
      have hmap (y : ULift.{u} (Fin n) →₀ (X.sheaf.over U).obj.obj V) :
          (show ULift.{u} (Fin n) →₀ (X.sheaf.over U).obj.obj W from
            (PresheafOfModules.freeObj (R := (X.ringCatSheaf.over U).obj)
              (overConstantType (X := X) U (ULift.{u} (Fin n)))).map f y) =
            Finsupp.mapRange σ σ.map_zero y := by
        induction y using Finsupp.induction with
        | zero => simp
        | single_add a r y _ha _hr ih =>
            rw [map_add]
            rw [Finsupp.mapRange_add σ.map_add]
            apply congrArg₂ (fun p q ↦ p + q)
            · conv_lhs => rw [← Finsupp.smul_single_one a r]
              rw [PresheafOfModules.map_smul]
              dsimp only [PresheafOfModules.freeObj, overConstantType]
              rw [show Finsupp.single a (1 : (X.sheaf.over U).obj.obj V) =
                ModuleCat.freeMk a from rfl]
              rw [ModuleCat.freeDesc_apply]
              simp only [Finsupp.mapRange_single]
              simp only [Functor.const_obj_map]
              change ((X.ringCatSheaf.over U).obj.map f) r • Finsupp.single a 1 =
                Finsupp.single a (((X.ringCatSheaf.over U).obj.map f) r)
              rw [Finsupp.smul_single_one]
            · exact ih
      have hentry (i j : Fin n) :
          (show ULift.{u} (Fin n) →₀ (X.sheaf.over U).obj.obj W from
            (((PresheafOfModules.freeObj (R := (X.ringCatSheaf.over U).obj)
              (overConstantType (X := X) U (ULift.{u} (Fin n)))).restrictₛₗ f) ∘ x) i)
              (Set.powersetCard.ofFinEmbEquiv.symm (topPowerset.{u} n) j) =
            σ ((show ULift.{u} (Fin n) →₀ (X.sheaf.over U).obj.obj V from x i)
              (Set.powersetCard.ofFinEmbEquiv.symm (topPowerset.{u} n) j)) := by
        change (show ULift.{u} (Fin n) →₀ (X.sheaf.over U).obj.obj W from
          (PresheafOfModules.freeObj (R := (X.ringCatSheaf.over U).obj)
            (overConstantType (X := X) U (ULift.{u} (Fin n)))).map f (x i)) _ = _
        rw [hmap]
        simp
      simp_rw [hentry]
      exact (σ.map_det _).symm)

/-- On an open slice, sheafify the objectwise exterior power of the restricted sheaf. -/
noncomputable def exteriorPowerOver (E : X.Modules) (U : X.Opens) (n : ℕ) :
    SheafOfModules (X.ringCatSheaf.over U) :=
  (PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)).obj
      (PresheafOfModules.exteriorPower (X.sheaf.over U).obj
        ((SheafOfModules.forget (X.ringCatSheaf.over U)).obj (E.over U)) n)

/-- Sheafified exterior power on an open slice carries isomorphic module sheaves to isomorphic
exterior powers. -/
noncomputable def exteriorPowerOverMapIsoOfIso (U : X.Opens)
    {M N : SheafOfModules (X.ringCatSheaf.over U)} (e : M ≅ N) (n : ℕ) :
    (PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).obj
        (PresheafOfModules.exteriorPower (X.sheaf.over U).obj
          ((SheafOfModules.forget (X.ringCatSheaf.over U)).obj M) n) ≅
      (PresheafOfModules.sheafification
        (𝟙 (X.ringCatSheaf.over U).obj)).obj
          (PresheafOfModules.exteriorPower (X.sheaf.over U).obj
            ((SheafOfModules.forget (X.ringCatSheaf.over U)).obj N) n) :=
  (PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)).mapIso
      (PresheafOfModules.exteriorPower.mapIso
        ((SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso e) n)

/-- Exterior power on an open slice carries isomorphic restricted sheaves to isomorphic
exterior powers. -/
noncomputable def exteriorPowerOverMapIso {E F : X.Modules} (U : X.Opens)
    (e : E.over U ≅ F.over U) (n : ℕ) :
    exteriorPowerOver E U n ≅ exteriorPowerOver F U n :=
  exteriorPowerOverMapIsoOfIso U e n

/-- On an open slice, the top exterior power of the free rank-`n` sheaf is the structure
sheaf. -/
noncomputable def topExteriorFreeOverIso (U : X.Opens) (n : ℕ) :
    (PresheafOfModules.sheafification
      (𝟙 (X.ringCatSheaf.over U).obj)).obj
        (PresheafOfModules.exteriorPower (X.sheaf.over U).obj
          ((SheafOfModules.forget (X.ringCatSheaf.over U)).obj
            (SheafOfModules.free (R := X.ringCatSheaf.over U)
              (ULift.{u} (Fin n)))) n) ≅
      SheafOfModules.unit (X.ringCatSheaf.over U) := by
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  exact aU.mapIso
      (PresheafOfModules.exteriorPower.mapIso
        (overFreeForgetIso (X := X) U (ULift.{u} (Fin n))) n ≪≫
        topExteriorFreeOverPresheafIso (X := X) U n) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.ringCatSheaf.over U).obj)).counit).app
        (SheafOfModules.unit (X.ringCatSheaf.over U))

set_option maxHeartbeats 6400000 in
/-- Restricting an objectwise exterior-power presheaf is the objectwise exterior power of the
restricted presheaf. -/
noncomputable def overExteriorPowerPresheafIso
    (P : X.PresheafOfModules) (U : X.Opens) (n : ℕ) :
    (overPresheafFunctor X U).obj
        (PresheafOfModules.exteriorPower X.presheaf P n) ≅
      PresheafOfModules.exteriorPower (X.sheaf.over U).obj
        ((overPresheafFunctor X U).obj P) n :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (by
    intro V W f
    rfl)

/-- Restriction of a sheaf exterior power agrees with the exterior power formed on the open
slice. -/
noncomputable def exteriorPowerOverIso (E : X.Modules) (U : X.Opens) (n : ℕ) :
    (exteriorPower E n).over U ≅ exteriorPowerOver E U n := by
  let P := (SheafOfModules.forget X.ringCatSheaf).obj E
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let c := overSheafificationComparison
    (PresheafOfModules.exteriorPower X.presheaf P n) U
  exact (@asIso _ _ _ _ c (isIso_overSheafificationComparison _ _)).symm ≪≫
    aU.mapIso (overExteriorPowerPresheafIso P U n)

end

end AlgebraicGeometry.Scheme.Modules
