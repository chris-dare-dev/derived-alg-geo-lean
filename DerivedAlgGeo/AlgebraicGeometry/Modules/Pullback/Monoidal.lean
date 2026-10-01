/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Invertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Monoidal
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Stalk
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Pullback of module sheaves is strong monoidal

For every morphism of schemes f : X ⟶ Y, pullback of module sheaves from Y to X is strong monoidal
for the sheafified tensor product: f^*(M ⊗ N) ≅ f^*M ⊗ f^*N and f^*𝒪_Y ≅ 𝒪_X. The canonical instance
is built by upgrading the oplax monoidal structure that Mathlib's doctrinal adjunction attaches to
the left adjoint of the lax monoidal pushforward.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pullbackTensorHom`: the oplax tensor comparison f^*(M ⊗ N) ⟶
  f^*M ⊗ f^*N, the mate of the tensorator of the pushforward.
* `AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal`: the oplax monoidal structure of the
  doctrinal adjunction.
* `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal`: the strong monoidal structure on pullback.
* `AlgebraicGeometry.Scheme.Modules.pullbackTensorIso` and
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`: the tensor and unit comparison isomorphisms
  read off the strong monoidal structure.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_stalkMap_pullbackTensorHom` and
  `AlgebraicGeometry.Scheme.Modules.isIso_pullbackTensorHom`: the tensor comparison is an
  isomorphism on every stalk, hence an isomorphism.
* `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal_toOplaxMonoidal`: the oplax part of the strong
  structure is the one induced by the adjunction.
* `AlgebraicGeometry.Scheme.Modules.pullbackTensorHom_unit_app_tmulSection`: the tensor comparison
  on the unit image of a pure tensor.
* `AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_inv` and
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom`: the comparisons are the oplax structure
  maps.

## Implementation notes

The unit comparison is Mathlib's `SheafOfModules.pullbackObjUnitToUnit`, an isomorphism because
inverse image on opens is final. The tensor comparison is shown invertible on stalks, which jointly
reflect isomorphisms
(`AlgebraicGeometry.Scheme.Modules.moduleStalkFunctors_jointlyReflectIsomorphisms`). At a point x,
the inverse of `AlgebraicGeometry.Scheme.Modules.pullbackStalkIso` sends 1 ⊗ germ m to the germ of
the unit image of m (`AlgebraicGeometry.Scheme.Modules.pullbackStalkIso_inv_app_one_tmul_germ`), the
stalk of a sheafified tensor product is the tensor product of the stalks
(`AlgebraicGeometry.Scheme.Modules.moduleStalkTensorEquiv`), and extension of scalars is monoidal;
the stalk of the comparison is checked equal to the resulting isomorphism on the generators 1 ⊗
germ(m ⊗ n). No flatness hypothesis is used. The strong structure is obtained from
`CategoryTheory.Adjunction.leftAdjointOplaxMonoidal` with
`CategoryTheory.Functor.Monoidal.ofOplaxMonoidal`, so there is no second oplax structure on
pullback. The lax monoidal structure of the pushforward is
`AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal`.

## References

* The Stacks Project, Tag 01CB (Lemma 17.16.1, the stalk of a tensor product of modules on a ringed
  space), Tag 01CD (Lemma 17.16.4, pullback of a tensor product of modules on ringed spaces) and Tag
  01E8 (Lemma 20.54.2, the projection formula for a finite locally free module). The statements were
  not obtained verbatim: only summaries of those pages were fetched, so these tags give the
  literature context and are not quoted.

## Tags

pullback, inverse image, strong monoidal functor, tensor product, sheaf of modules, stalk
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The oplax tensorator of pullback: the mate of the tensorator of pushforward. -/
def pullbackTensorHom (M N : Y.Modules) :
    (pullback f).obj (tensorObj M N) ⟶
      tensorObj ((pullback f).obj M) ((pullback f).obj N) :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (((pullbackPushforwardAdjunction f).unit.app M ⊗ₘ
        (pullbackPushforwardAdjunction f).unit.app N) ≫ pushforwardTensorHom f _ _)

/-- **The oplax tensorator on the image of a pure tensor under the unit.** The mate
`f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N` sends the unit image `η(m ⊗ n)` of a pure tensor to the pure tensor of
the unit images `η m ⊗ η n`, as sections of the pullback over `f⁻¹ V`. -/
theorem pullbackTensorHom_unit_app_tmulSection (M N : Y.Modules) (V : Y.Opens)
    (m : Γ(M, V)) (n : Γ(N, V)) :
    (pullbackTensorHom f M N).app (f ⁻¹ᵁ V)
      (((pullbackPushforwardAdjunction f).unit.app (tensorObj M N)).app V
        (tmulSection M N (op V) m n)) =
      tmulSection ((pullback f).obj M) ((pullback f).obj N) (op (f ⁻¹ᵁ V))
        (((pullbackPushforwardAdjunction f).unit.app M).app V m)
        (((pullbackPushforwardAdjunction f).unit.app N).app V n) := by
  have h : (pullbackPushforwardAdjunction f).unit.app (tensorObj M N) ≫
      (pushforward f).map (pullbackTensorHom f M N) =
      ((pullbackPushforwardAdjunction f).unit.app M ⊗ₘ
        (pullbackPushforwardAdjunction f).unit.app N) ≫ pushforwardTensorHom f _ _ := by
    have := ((pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply
      (((pullbackPushforwardAdjunction f).unit.app M ⊗ₘ
        (pullbackPushforwardAdjunction f).unit.app N) ≫ pushforwardTensorHom f _ _)
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have h2 := congrArg (fun φ => φ.app V (tmulSection M N (op V) m n)) h
  refine h2.trans ?_
  change (pushforwardTensorHom f _ _).app V
    ((tensorHom ((pullbackPushforwardAdjunction f).unit.app M)
      ((pullbackPushforwardAdjunction f).unit.app N)).app V (tmulSection M N (op V) m n)) = _
  exact (congrArg (fun z => (pushforwardTensorHom f _ _).app V z)
    (tensorHom_tmulSection ((pullbackPushforwardAdjunction f).unit.app M)
      ((pullbackPushforwardAdjunction f).unit.app N) V m n)).trans
    (pushforwardTensorHom_app_tmulSection f _ _ V _ _)


/-- Extension of scalars along the local-ring map at `x`. -/
private abbrev stalkExtend (x : X) :
    ModuleCat.{u} (Y.presheaf.stalk (f x)) ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  ModuleCat.extendScalars (f.stalkMap x).hom

open TensorProduct in
/-- **Stalkwise, the tensor comparison of pullback is an isomorphism.** On the stalk at `x`, both
`f^*(M ⊗ N)` and `f^*M ⊗ f^*N` are `𝒪_{X,x} ⊗ (M ⊗ N)_{f x}` (extension of scalars is monoidal, the
stalk of a pullback is the extension of the stalk, the stalk of a tensor product is the tensor
product of the stalks), and the comparison is that identification: it is checked on the generators
`1 ⊗ germ(m ⊗ n)` using `AlgebraicGeometry.Scheme.Modules.pullbackStalkIso_inv_app_one_tmul_germ`.
-/
theorem isIso_stalkMap_pullbackTensorHom (M N : Y.Modules) (x : X) :
    IsIso ((moduleStalkFunctor X x).map (pullbackTensorHom f M N)) := by
  letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let A := (moduleStalkFunctor Y (f x)).obj M
  let B := (moduleStalkFunctor Y (f x)).obj N
  let ΦM := (pullbackStalkIso f x).app M
  let ΦN := (pullbackStalkIso f x).app N
  let ΦT := (pullbackStalkIso f x).app (tensorObj M N)
  let ωY : A ⊗ B ≅ (moduleStalkFunctor Y (f x)).obj (tensorObj M N) :=
    (moduleStalkTensorEquiv Y (f x) M N).toModuleIso
  let ωX : (moduleStalkFunctor X x).obj ((pullback f).obj M) ⊗
      (moduleStalkFunctor X x).obj ((pullback f).obj N) ≅
      (moduleStalkFunctor X x).obj (tensorObj ((pullback f).obj M) ((pullback f).obj N)) :=
    (moduleStalkTensorEquiv X x _ _).toModuleIso
  let κ : (stalkExtend f x).obj ((moduleStalkFunctor Y (f x)).obj (tensorObj M N)) ≅
      (moduleStalkFunctor X x).obj (tensorObj ((pullback f).obj M) ((pullback f).obj N)) :=
    (stalkExtend f x).mapIso ωY.symm ≪≫ asIso (Functor.OplaxMonoidal.δ (stalkExtend f x) A B) ≪≫
      tensorIso ΦM.symm ΦN.symm ≪≫ ωX
  have key : ΦT.inv ≫ (moduleStalkFunctor X x).map (pullbackTensorHom f M N) = κ.hom := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro ξ
    obtain ⟨ζ, rfl⟩ := (moduleStalkTensorEquiv Y (f x) M N).surjective ξ
    induction ζ using TensorProduct.induction_on with
    | zero =>
      rw [map_zero, TensorProduct.tmul_zero]
      exact (map_zero (ModuleCat.Hom.hom _)).trans (map_zero (ModuleCat.Hom.hom _)).symm
    | tmul a b =>
      obtain ⟨V, hV, m, n, rfl, rfl⟩ := moduleStalkGerm_exists_pair Y (f x) M N a b
      have hL : (ΦT.inv ≫ (moduleStalkFunctor X x).map (pullbackTensorHom f M N)).hom
          ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)]
            (moduleStalkTensorEquiv Y (f x) M N)
              (moduleStalkGerm Y (f x) M V hV m ⊗ₜ moduleStalkGerm Y (f x) N V hV n)) =
          moduleStalkGerm X x (tensorObj ((pullback f).obj M) ((pullback f).obj N)) (f ⁻¹ᵁ V) hV
            (tmulSection ((pullback f).obj M) ((pullback f).obj N) (op (f ⁻¹ᵁ V))
              (((pullbackPushforwardAdjunction f).unit.app M).app V m)
              (((pullbackPushforwardAdjunction f).unit.app N).app V n)) := by
        rw [moduleStalkTensorEquiv_germ_tmul_germ]
        refine (congrArg ((moduleStalkFunctor X x).map (pullbackTensorHom f M N)).hom
          (pullbackStalkIso_inv_app_one_tmul_germ f x (M.tensorObj N) V hV
            (tmulSection M N (op V) m n))).trans ?_
        refine (presheafModuleStalkFunctor_map_germ X x _ (f ⁻¹ᵁ V) hV _).trans ?_
        exact congrArg (moduleStalkGerm X x _ (f ⁻¹ᵁ V) hV)
          (pullbackTensorHom_unit_app_tmulSection f M N V m n)
      have hR : κ.hom.hom
          ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)]
            (moduleStalkTensorEquiv Y (f x) M N)
              (moduleStalkGerm Y (f x) M V hV m ⊗ₜ moduleStalkGerm Y (f x) N V hV n)) =
          moduleStalkGerm X x (tensorObj ((pullback f).obj M) ((pullback f).obj N)) (f ⁻¹ᵁ V) hV
            (tmulSection ((pullback f).obj M) ((pullback f).obj N) (op (f ⁻¹ᵁ V))
              (((pullbackPushforwardAdjunction f).unit.app M).app V m)
              (((pullbackPushforwardAdjunction f).unit.app N).app V n)) := by
        have e1 : ((stalkExtend f x).map ωY.inv).hom
            ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)]
              (moduleStalkTensorEquiv Y (f x) M N)
                (moduleStalkGerm Y (f x) M V hV m ⊗ₜ moduleStalkGerm Y (f x) N V hV n)) =
            (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)]
              (moduleStalkGerm Y (f x) M V hV m ⊗ₜ[Y.presheaf.stalk (f x)]
                moduleStalkGerm Y (f x) N V hV n) := by
          have e0 : ωY.inv.hom ((moduleStalkTensorEquiv Y (f x) M N)
              (moduleStalkGerm Y (f x) M V hV m ⊗ₜ moduleStalkGerm Y (f x) N V hV n)) =
              moduleStalkGerm Y (f x) M V hV m ⊗ₜ[Y.presheaf.stalk (f x)]
                moduleStalkGerm Y (f x) N V hV n :=
            (moduleStalkTensorEquiv Y (f x) M N).symm_apply_apply _
          exact (ModuleCat.ExtendScalars.map_tmul (f.stalkMap x).hom ωY.inv 1 _).trans
            (congrArg _ e0)
        have e2 := ModuleCat.extendScalars_δ_tmul (f.stalkMap x).hom A B
          (moduleStalkGerm Y (f x) M V hV m) (moduleStalkGerm Y (f x) N V hV n)
        have e3 := ModuleCat.MonoidalCategory.tensorHom_tmul ΦM.inv ΦN.inv
          ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] moduleStalkGerm Y (f x) M V hV m)
          ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (f x)] moduleStalkGerm Y (f x) N V hV n)
        have e4 := pullbackStalkIso_inv_app_one_tmul_germ f x M V hV m
        have e5 := pullbackStalkIso_inv_app_one_tmul_germ f x N V hV n
        have e6 := moduleStalkTensorEquiv_germ_tmul_germ X x ((pullback f).obj M)
          ((pullback f).obj N) (f ⁻¹ᵁ V) hV (((pullbackPushforwardAdjunction f).unit.app M).app V m)
          (((pullbackPushforwardAdjunction f).unit.app N).app V n)
        refine (congrArg (fun z => ωX.hom.hom ((ΦM.inv ⊗ₘ ΦN.inv).hom
          ((Functor.OplaxMonoidal.δ (stalkExtend f x) A B).hom z))) e1).trans ?_
        refine (congrArg (fun z => ωX.hom.hom ((ΦM.inv ⊗ₘ ΦN.inv).hom z)) e2).trans ?_
        refine (congrArg (fun z => ωX.hom.hom z) e3).trans ?_
        refine (congrArg₂ (fun u v => ωX.hom.hom (u ⊗ₜ[X.presheaf.stalk x] v)) e4 e5).trans ?_
        exact e6
      exact hL.trans hR.symm
    | add ζ ζ' h h' =>
      rw [map_add, TensorProduct.tmul_add]
      exact (map_add (ModuleCat.Hom.hom _) _ _).trans
        ((congrArg₂ (· + ·) h h').trans (map_add (ModuleCat.Hom.hom _) _ _).symm)
  have hδ : (moduleStalkFunctor X x).map (pullbackTensorHom f M N) = (ΦT ≪≫ κ).hom := by
    rw [Iso.trans_hom, ← key, Iso.hom_inv_id_assoc]
  rw [hδ]
  exact (ΦT ≪≫ κ).isIso_hom

/-- **The tensor comparison of pullback is an isomorphism** (Stacks, Tag 01CD), checked on
stalks. No flatness hypothesis on `f` is needed. -/
instance isIso_pullbackTensorHom (M N : Y.Modules) : IsIso (pullbackTensorHom f M N) := by
  haveI : ∀ x : X, IsIso ((moduleStalkFunctor X x).map (pullbackTensorHom f M N)) :=
    fun x => isIso_stalkMap_pullbackTensorHom f M N x
  exact (moduleStalkFunctors_jointlyReflectIsomorphisms X).isIso _

/-- The oplax monoidal structure on module-sheaf pullback induced by the doctrinal adjunction:
`pushforward f` is lax monoidal, so its left adjoint `pullback f` is oplax monoidal. -/
abbrev pullbackOplaxMonoidal : (pullback f).OplaxMonoidal :=
  (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal

/-- **Stacks, Tag 01CD: pullback of module sheaves is strong monoidal.**

The oplax structure is `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal` for
`pullbackPushforwardAdjunction f` and the lax structure of `pushforward f`
(`AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal`); its comparison maps are isomorphisms:
`SheafOfModules.pullbackObjUnitToUnit` for the unit, and
`AlgebraicGeometry.Scheme.Modules.isIso_pullbackTensorHom` (a stalkwise check) for the tensor
product. This is the only monoidal structure on `pullback f`. -/
noncomputable instance pullbackMonoidal : (pullback f).Monoidal :=
  letI := pullbackOplaxMonoidal f
  haveI : IsIso (Functor.OplaxMonoidal.η (pullback f)) :=
    inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom))
  haveI : ∀ M N : Y.Modules, IsIso (Functor.OplaxMonoidal.δ (pullback f) M N) :=
    fun M N => isIso_pullbackTensorHom f M N
  Functor.Monoidal.ofOplaxMonoidal (pullback f)

/-- The oplax part of `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal` is the one induced by the
doctrinal adjunction; there is no second oplax structure on `pullback f`. -/
theorem pullbackMonoidal_toOplaxMonoidal :
    (pullbackMonoidal f).toOplaxMonoidal = pullbackOplaxMonoidal f :=
  rfl

/-- The tensor comparison of pullback along any morphism of schemes. -/
noncomputable def pullbackTensorIso (f : X ⟶ Y) (M N : Y.Modules) :
    tensorObj ((pullback f).obj M) ((pullback f).obj N) ≅
      (pullback f).obj (tensorObj M N) := by
  change (pullback f).obj M ⊗ (pullback f).obj N ≅
    (pullback f).obj (M ⊗ N)
  exact Functor.Monoidal.μIso (pullback f) M N

/-- The unit comparison of pullback along any morphism of schemes. -/
noncomputable def pullbackUnitIso (f : X ⟶ Y) :
    (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  change (pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules
  exact (Functor.Monoidal.εIso (pullback f)).symm

/-- The inverse of the tensor comparison is the oplax tensorator
`AlgebraicGeometry.Scheme.Modules.pullbackTensorHom`. -/
theorem pullbackTensorIso_inv (M N : Y.Modules) :
    (pullbackTensorIso f M N).inv = pullbackTensorHom f M N :=
  rfl

/-- The unit comparison is Mathlib's `SheafOfModules.pullbackObjUnitToUnit`. -/
theorem pullbackUnitIso_hom :
    (pullbackUnitIso f).hom = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom :=
  rfl

/-- The two comparisons elaborate with no `CategoryTheory.Functor.Monoidal` argument: the instance
is canonical. -/
example (M N : Y.Modules) :
    tensorObj ((pullback f).obj M) ((pullback f).obj N) ≅
      (pullback f).obj (tensorObj M N) :=
  pullbackTensorIso f M N


end

end AlgebraicGeometry.Scheme.Modules
