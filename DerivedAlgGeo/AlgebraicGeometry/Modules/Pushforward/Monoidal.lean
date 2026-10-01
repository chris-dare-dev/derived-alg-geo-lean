/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Sections
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Pushforward of module sheaves is lax monoidal

For a morphism of schemes `f : X ⟶ Y`, the pushforward `f_* : X.Modules ⥤ Y.Modules` is lax
monoidal for the sheafified tensor product (Stacks, Tag 01CD is the dual statement for the
pullback, which this structure induces through the doctrinal adjunction).

The tensorator `f_*M ⊗ f_*N ⟶ f_*(M ⊗ N)` is multiplication of sections: a pure tensor of
sections of `M` and `N` over `f⁻¹ U` is a section of `M ⊗ N` over `f⁻¹ U`. It is built from
`TensorLiftData` and checked on pure tensors, so no sheafification is computed.

## Main definitions

* `Scheme.Modules.pushforwardTensorHom`: the tensorator.
* `Scheme.Modules.pushforwardUnitHom`: the unit `𝒪_Y ⟶ f_*𝒪_X`, Mathlib's
  `SheafOfModules.unitToPushforwardObjUnit`.
* `Scheme.Modules.pushforwardLaxMonoidal`: the instance `(pushforward f).LaxMonoidal`.
-/

open CategoryTheory MonoidalCategory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

noncomputable section

/-- The sectionwise multiplication data for the lax structure of pushforward: a pure tensor of
sections of `M` and `N` over `f⁻¹ U` is a section of `M ⊗ N` over `f⁻¹ U`. -/
def pushforwardTensorData (M N : X.Modules) :
    TensorLiftData ((pushforward f).obj M) ((pushforward f).obj N)
      ((pushforward f).obj (tensorObj M N)) where
  toFun U a b := tmulSection M N (op (f ⁻¹ᵁ U)) a b
  add_left U a a' b := tmulSection_add_left M N (op (f ⁻¹ᵁ U)) a a' b
  smul_left U r a b := (smul_tmulSection_left M N (op (f ⁻¹ᵁ U)) (f.app U r) a b).symm
  add_right U a b b' := tmulSection_add_right M N (op (f ⁻¹ᵁ U)) a b b'
  smul_right U r a b := (smul_tmulSection M N (op (f ⁻¹ᵁ U)) (f.app U r) a b).symm
  res h a b := (res_tmulSection M N ((Opens.map f.base).map (homOfLE h)).le a b)


/-- The tensorator `f_*M ⊗ f_*N ⟶ f_*(M ⊗ N)` of pushforward. -/
def pushforwardTensorHom (M N : X.Modules) :
    tensorObj ((pushforward f).obj M) ((pushforward f).obj N) ⟶
      (pushforward f).obj (tensorObj M N) :=
  (pushforwardTensorData f M N).lift

/-- The tensorator of pushforward acts on pure tensors by pure tensors. -/
theorem pushforwardTensorHom_app_tmulSection (M N : X.Modules) (U : Y.Opens)
    (a : Γ((pushforward f).obj M, U)) (b : Γ((pushforward f).obj N, U)) :
    (pushforwardTensorHom f M N).app U (tmulSection _ _ (op U) a b) =
      tmulSection M N (op (f ⁻¹ᵁ U)) a b :=
  (pushforwardTensorData f M N).lift_app_tmulSection U a b

/-- The unit of pushforward: the ring map `𝒪_Y → f_* 𝒪_X`. -/
def pushforwardUnitHom : 𝟙_ Y.Modules ⟶ (pushforward f).obj (𝟙_ X.Modules) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

/-- The unit of pushforward is the ring map `f.app U` on sections. -/
theorem pushforwardUnitHom_app (U : Y.Opens) (r : Γ(𝟙_ Y.Modules, U)) :
    (pushforwardUnitHom f).app U r =
      (show Γ(𝟙_ X.Modules, f ⁻¹ᵁ U) from f.app U (show Γ(Y, U) from r)) := rfl

/-- **Pushforward of module sheaves is lax monoidal** for the sheafified tensor product: the
tensorator `f_*M ⊗ f_*N ⟶ f_*(M ⊗ N)` is multiplication of sections, and the unit is the ring map
`𝒪_Y → f_*𝒪_X`. Every coherence equation is checked on pure tensors
(`tensorObj_hom_ext`, `tensorObj_tensorObj_hom_ext`). -/
noncomputable instance pushforwardLaxMonoidal : (pushforward f).LaxMonoidal where
  ε := pushforwardUnitHom f
  μ M N := pushforwardTensorHom f M N
  μ_natural_left g M' := by
    refine tensorObj_hom_ext _ _ fun U a b => ?_
    change (pushforwardTensorHom f _ M').app U ((tensorHom ((pushforward f).map g) (𝟙 _)).app U
      (tmulSection _ _ (op U) a b)) =
      ((pushforward f).map (tensorHom g (𝟙 _))).app U
        ((pushforwardTensorHom f _ M').app U (tmulSection _ _ (op U) a b))
    rw [tensorHom_tmulSection, pushforwardTensorHom_app_tmulSection,
      pushforwardTensorHom_app_tmulSection]
    rw [pushforward_map_app, pushforward_map_app]
    exact (tensorHom_tmulSection g (𝟙 M') (f ⁻¹ᵁ U) a b).symm
  μ_natural_right M' g := by
    refine tensorObj_hom_ext _ _ fun U a b => ?_
    change (pushforwardTensorHom f M' _).app U ((tensorHom (𝟙 _) ((pushforward f).map g)).app U
      (tmulSection _ _ (op U) a b)) =
      ((pushforward f).map (tensorHom (𝟙 M') g)).app U
        ((pushforwardTensorHom f M' _).app U (tmulSection _ _ (op U) a b))
    have e1 := tensorHom_tmulSection (𝟙 ((pushforward f).obj M')) ((pushforward f).map g) U a b
    rw [e1, pushforward_map_app, pushforwardTensorHom_app_tmulSection]
    have h2 := pushforwardTensorHom_app_tmulSection f M' _ U a b
    rw [h2]
    exact (tensorHom_tmulSection (𝟙 M') g (f ⁻¹ᵁ U) a b).symm
  associativity M N P := by
    refine tensorObj_tensorObj_hom_ext _ _ fun U a b c => ?_
    change ((pushforward f).map (tensorAssocIso M N P).hom).app U
      ((pushforwardTensorHom f (tensorObj M N) P).app U
        ((tensorHom (pushforwardTensorHom f M N) (𝟙 _)).app U
          (tmulSection _ _ (op U) (tmulSection _ _ (op U) a b) c))) =
      (pushforwardTensorHom f M (tensorObj N P)).app U
        ((tensorHom (𝟙 _) (pushforwardTensorHom f N P)).app U
          ((tensorAssocIso _ _ _).hom.app U
            (tmulSection _ _ (op U) (tmulSection _ _ (op U) a b) c)))
    rw [tensorAssocIso_hom_tmulSection]
    have e1 := tensorHom_tmulSection (pushforwardTensorHom f M N) (𝟙 ((pushforward f).obj P)) U
      (((pushforward f).obj M).tmulSection ((pushforward f).obj N) (op U) a b) c
    have e2 := tensorHom_tmulSection (𝟙 ((pushforward f).obj M)) (pushforwardTensorHom f N P) U a
      (((pushforward f).obj N).tmulSection ((pushforward f).obj P) (op U) b c)
    rw [e1, e2]
    have h1 := pushforwardTensorHom_app_tmulSection f M N U a b
    have h2 := pushforwardTensorHom_app_tmulSection f N P U b c
    change ((pushforward f).map (tensorAssocIso M N P).hom).app U
      ((pushforwardTensorHom f (tensorObj M N) P).app U
        (tmulSection ((pushforward f).obj (tensorObj M N)) ((pushforward f).obj P) (op U)
          ((pushforwardTensorHom f M N).app U (tmulSection _ _ (op U) a b)) c)) =
      (pushforwardTensorHom f M (tensorObj N P)).app U
        (tmulSection ((pushforward f).obj M) ((pushforward f).obj (tensorObj N P)) (op U) a
          ((pushforwardTensorHom f N P).app U (tmulSection _ _ (op U) b c)))
    rw [h1, h2, pushforwardTensorHom_app_tmulSection, pushforwardTensorHom_app_tmulSection]
    exact tensorAssocIso_hom_tmulSection M N P (f ⁻¹ᵁ U) a b c
  left_unitality M := by
    refine tensorObj_hom_ext _ _ fun U r m => ?_
    change (tensorUnitLeftIso ((pushforward f).obj M)).hom.app U (tmulSection _ _ (op U) r m) =
      ((pushforward f).map (tensorUnitLeftIso M).hom).app U
        ((pushforwardTensorHom f _ M).app U ((tensorHom (pushforwardUnitHom f) (𝟙 _)).app U
          (tmulSection _ _ (op U) r m)))
    rw [tensorUnitLeftIso_hom_tmulSection, tensorHom_tmulSection, pushforward_map_app]
    have h := pushforwardTensorHom_app_tmulSection f (SheafOfModules.unit X.ringCatSheaf) M U
      ((pushforwardUnitHom f).app U r) m
    exact (tensorUnitLeftIso_hom_tmulSection M (f ⁻¹ᵁ U) _ m).symm.trans (congrArg _ h.symm)
  right_unitality M := by
    refine tensorObj_hom_ext _ _ fun U m r => ?_
    change (tensorUnitRightIso ((pushforward f).obj M)).hom.app U (tmulSection _ _ (op U) m r) =
      ((pushforward f).map (tensorUnitRightIso M).hom).app U
        ((pushforwardTensorHom f M _).app U ((tensorHom (𝟙 _) (pushforwardUnitHom f)).app U
          (tmulSection _ _ (op U) m r)))
    rw [tensorUnitRightIso_hom_tmulSection, tensorHom_tmulSection, pushforward_map_app]
    have h := pushforwardTensorHom_app_tmulSection f M (SheafOfModules.unit X.ringCatSheaf) U m
      ((pushforwardUnitHom f).app U r)
    exact (tensorUnitRightIso_hom_tmulSection M (f ⁻¹ᵁ U) m _).symm.trans (congrArg _ h.symm)

end

end AlgebraicGeometry.Scheme.Modules
