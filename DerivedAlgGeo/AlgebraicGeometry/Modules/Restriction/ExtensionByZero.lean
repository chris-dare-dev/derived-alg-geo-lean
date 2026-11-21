/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Adjunction.Triple
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.Sections

/-!
# Extension by zero of module sheaves along an open immersion

For an open immersion `f : X ⟶ Y` of schemes, restriction
`Scheme.Modules.restrictFunctor f : Y.Modules ⥤ X.Modules` is Mathlib's pushforward of sheaves of
modules along the continuous functor `f.opensFunctor`. Its left adjoint is the pullback along that
functor, and this file calls it `extendByZero f`, the functor `f_!` of the literature. It is not a
new left Kan extension: it is `SheafOfModules.pullback` for the ring map defining restriction.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.extendByZero`: the functor `f_!`.
* `AlgebraicGeometry.Scheme.Modules.extendByZeroAdjunction`: `f_! ⊣ f^*`.
* `AlgebraicGeometry.Scheme.Modules.extendByZeroPullbackAdjunction`: the same adjunction, with the
  right adjoint presented as module pullback.
* `AlgebraicGeometry.Scheme.Modules.extendByZeroStalkIso`: `(f_! M)_{f x} ≅ M_x`.
* `AlgebraicGeometry.Scheme.Modules.extendByZeroCompRestrictIso`: `f^* ∘ f_! ≅ 𝟭`.
* `AlgebraicGeometry.Scheme.Modules.extendByZeroCompPullbackIsoOfIsPullback`: `f_!` commutes with
  pullback along every morphism `g`, for any pullback square of `f` along `g`.
* `AlgebraicGeometry.Scheme.Modules.extendByZeroCompPullbackIso`: the case of the chosen
  pullback.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isZero_extendByZero_stalk`: the stalk of `f_! M` at a point
  outside the image of `f` is zero.
* the instance `PreservesFiniteLimits (extendByZero f)`: `f_!` is exact.

## Implementation notes

The adjunction comes from Mathlib. The unit of `f_! ⊣ f^*` is invertible because `f_!` sits in an
adjoint triple `f_! ⊣ f^* ⊣ f_*` whose right adjoint `f_*` has invertible counit.

The stalk at a point outside the image vanishes because a module stalk is left adjoint to a module
skyscraper, and the pushforward of a skyscraper at a point outside the image of `f` has only zero
sections. This is applied to the presheaf pullback, and module sheafification preserves stalks.

Base change is proved on the right adjoints, for any pullback square `fst, snd, g, f` of the open
immersion `f` along `g`: restriction after pushforward along `g` is pushforward along `snd` after
restriction along `fst`. Both sides have the same sections, because
`fst ''ᵁ snd ⁻¹ᵁ U = g ⁻¹ᵁ f ''ᵁ U`, and the identification is compatible with the scalar actions.
Uniqueness of left adjoints then gives the base change isomorphism for `f_!`.

## References

* Stacks Project, Tags 00A4 and 00A7 (extension by zero for sheaves of modules on an open subset)
  and Tag 01AK (it is exact).

## Tags

extension by zero, open immersion, sheaf of modules, restriction, base change
-/

universe u

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory Limits Opposite TopologicalSpace

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

set_option backward.defeqAttrib.useBackward true in
/-- The morphism of sheaves of rings on `X.Opens` defining restriction along the open immersion
`f`: it sends `Γ(X, U)` to `Γ(Y, f ''ᵁ U)` by the inverse of `f.appIso U`. -/
def restrictRingCatSheafHom :
    X.ringCatSheaf ⟶ (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf :=
  letI α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf := { app U := (f.appIso U.unop).inv }
  ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Extension by zero `f_!` of module sheaves along an open immersion `f : X ⟶ Y`, the left
adjoint of restriction `Scheme.Modules.restrictFunctor f` (Stacks Tags 00A4 and 00A7 (1)-(2)).

It is Mathlib's `SheafOfModules.pullback` along `f.opensFunctor`, so it is the sheafification of
the presheaf extension by zero `V ↦ M (f ⁻¹ᵁ V)` if `V ⊆ f(X)` and `0` otherwise.

Downstream, `f_!` is preferred to the derived direct image `Rf_*` because it is exact
(`instance : PreservesFiniteLimits (extendByZero f)`) and commutes with pullback along every
morphism (`extendByZeroCompPullbackIso`), whereas `Rf_*` commutes only with flat base change. -/
def extendByZero : X.Modules ⥤ Y.Modules :=
  SheafOfModules.pullback.{u} (restrictRingCatSheafHom f)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Extension by zero is left adjoint to restriction. -/
def extendByZeroAdjunction : extendByZero f ⊣ restrictFunctor f :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} (restrictRingCatSheafHom f)

instance : (extendByZero f).IsLeftAdjoint := (extendByZeroAdjunction f).isLeftAdjoint

instance : (extendByZero f).Additive :=
  haveI : PreservesBinaryBiproducts (extendByZero f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.additive_of_preservesBinaryBiproducts _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Extension by zero is left adjoint to module pullback, which is isomorphic to restriction. -/
def extendByZeroPullbackAdjunction : extendByZero f ⊣ pullback f :=
  (extendByZeroAdjunction f).ofNatIsoRight (restrictFunctorIsoPullback f)

/-- The adjoint triple `f_! ⊣ f^* ⊣ f_*`. -/
def extendByZeroTriple :
    Adjunction.Triple (extendByZero f) (restrictFunctor f) (pushforward f) :=
  ⟨extendByZeroAdjunction f, restrictAdjunction f⟩

/-- The unit of `f_! ⊣ f^*` is invertible: the right adjoint `f_*` of `f^*` has invertible
counit. -/
instance : IsIso (extendByZeroAdjunction f).unit :=
  (extendByZeroTriple f).isIso_unit_iff_isIso_counit.mpr inferInstance

instance : IsIso (extendByZeroPullbackAdjunction f).unit := by
  unfold extendByZeroPullbackAdjunction
  show IsIso ((extendByZeroAdjunction f).unit ≫ _)
  infer_instance

/-- Restriction after extension by zero is the identity (Stacks Tag 00A7 (4)). -/
def extendByZeroCompRestrictIso : extendByZero f ⋙ restrictFunctor f ≅ 𝟭 X.Modules :=
  (asIso (extendByZeroAdjunction f).unit).symm

/-! ### Stalks -/

/-- The stalk of `f_! M` at `f x` is the stalk of `M` at `x`, naturally in `M`. -/
def extendByZeroStalkNatIso (x : X) :
    extendByZero f ⋙ toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor _ (f.base x) ≅
      toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x :=
  (Functor.isoWhiskerLeft (extendByZero f) (restrictStalkNatIso f x)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extendByZeroCompRestrictIso f)
      (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor _ x) ≪≫
    Functor.leftUnitor _

/-- Stacks Tag 00A7 (3), at points of `X`: `(f_! M)_{f x} ≅ M_x`. -/
def extendByZeroStalkIso (M : X.Modules) (x : X) :
    ((extendByZero f).obj M).presheaf.stalk (f.base x) ≅ M.presheaf.stalk x :=
  (extendByZeroStalkNatIso f x).app M

set_option backward.isDefEq.respectTransparency.types false in
/-- The module stalk of `f_! M` at a point outside the image of `f` is zero. -/
theorem isZero_extendByZero_moduleStalk (M : X.Modules) (y : Y) (hy : y ∉ Set.range f.base) :
    IsZero ((moduleStalkFunctor Y y).obj ((extendByZero f).obj M)) := by
  have h := isZero_presheafModuleStalk_pullback_of_forall_notMem
    (F := f.opensFunctor) (restrictRingCatSheafHom f).hom y
    (fun U hU ↦ hy (by obtain ⟨x, _, hx⟩ := hU; exact ⟨x, hx⟩)) M.val
  refine IsZero.of_iso h ?_
  have := presheafModuleStalkToSheafificationApp_isIso Y y
    ((PresheafOfModules.pullback (restrictRingCatSheafHom f).hom).obj
      ((SheafOfModules.forget X.ringCatSheaf).obj M))
  exact (moduleStalkFunctor Y y).mapIso ((SheafOfModules.pullbackIso.{u}
    (restrictRingCatSheafHom f)).app M) ≪≫
    (asIso (presheafModuleStalkToSheafificationApp Y y _)).symm

/-- Stacks Tag 00A7 (3), outside the image: the stalk of `f_! M` at a point not in the image of
`f` is zero. -/
theorem isZero_extendByZero_stalk (M : X.Modules) (y : Y) (hy : y ∉ Set.range f.base) :
    Limits.IsZero (((extendByZero f).obj M).presheaf.stalk y) :=
  (Functor.map_isZero (forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u})
    (isZero_extendByZero_moduleStalk f M y hy)).of_iso
    ((moduleStalkForgetIso Y y).app ((extendByZero f).obj M)).symm

/-! ### Exactness -/

/-- The abelian-group stalk of the underlying presheaf of a module sheaf preserves finite
limits. -/
theorem preservesFiniteLimits_toPresheaf_stalkFunctor (Z : Scheme.{u}) (z : Z) :
    PreservesFiniteLimits (toPresheaf Z ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z) := by
  let e : moduleStalkFunctor Z z ⋙ forget₂ (ModuleCat.{u} (Z.presheaf.stalk z)) AddCommGrpCat.{u} ≅
      toPresheaf Z ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z :=
    moduleStalkForgetIso Z z ≪≫ (Functor.associator _ _ _).symm
  have := moduleStalkFunctor_preservesFiniteLimits Z z
  have : PreservesFiniteLimits (moduleStalkFunctor Z z ⋙
      forget₂ (ModuleCat.{u} (Z.presheaf.stalk z)) AddCommGrpCat.{u}) := inferInstance
  exact preservesFiniteLimits_of_natIso e

/-- Extension by zero followed by any module stalk preserves finite limits: at a point `f x` the
composite is the stalk at `x`, and elsewhere it is zero. -/
theorem extendByZero_stalk_preservesFiniteLimits (y : Y) :
    PreservesFiniteLimits (extendByZero f ⋙ moduleStalkFunctor Y y) := by
  by_cases hy : y ∈ Set.range f.base
  · obtain ⟨x, rfl⟩ := hy
    let forgetY := forget₂ (ModuleCat.{u} (Y.presheaf.stalk (f.base x))) AddCommGrpCat.{u}
    let e : (extendByZero f ⋙ moduleStalkFunctor Y (f.base x)) ⋙ forgetY ≅
        toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (extendByZero f)
          (moduleStalkForgetIso Y (f.base x) ≪≫ (Functor.associator _ _ _).symm) ≪≫
        extendByZeroStalkNatIso f x
    have : PreservesFiniteLimits ((extendByZero f ⋙ moduleStalkFunctor Y (f.base x)) ⋙
        forgetY) :=
      @preservesFiniteLimits_of_natIso _ _ _ _ _ _ e.symm
        (preservesFiniteLimits_toPresheaf_stalkFunctor X x)
    exact preservesFiniteLimits_of_reflects_of_preserves
      (extendByZero f ⋙ moduleStalkFunctor Y (f.base x)) forgetY
  · have : PreservesLimitsOfSize.{0, 0} (extendByZero f ⋙ moduleStalkFunctor Y y) :=
      Functor.preservesLimitsOfSize_of_isZero _
        (Functor.isZero _ fun M ↦ isZero_extendByZero_moduleStalk f M y hy)
    infer_instance

/-- Extension by zero is exact (Stacks Tag 01AK, for modules): exactness of module sheaves is
checked on stalks, and the stalks of `f_! M` are those of `M` inside the image of `f` and zero
outside it. -/
instance : PreservesFiniteLimits (extendByZero f) :=
  preservesFiniteLimits_of_stalkwise (extendByZero f) (extendByZero_stalk_preservesFiniteLimits f)

/-! ### Base change -/

section BaseChange

variable {Y' P : Scheme.{u}} (g : Y' ⟶ Y) (fst : P ⟶ Y') (snd : P ⟶ X) [IsOpenImmersion fst]
  (hP : IsPullback fst snd g f)

include hP

/-- For an open immersion `f`, the image under `fst` of the preimage under
`snd` of `U` is the preimage under `g` of the image of `U` under `f`. -/
theorem baseChange_image_preimage (U : X.Opens) :
    fst ''ᵁ snd ⁻¹ᵁ U = g ⁻¹ᵁ f ''ᵁ U :=
  IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    hP.flip U

/-- The two ring maps `Γ(X, U) ⟶ Γ(Y', g ⁻¹ᵁ f ''ᵁ U)` and `Γ(X, U) ⟶ Γ(Y', fst ''ᵁ snd ⁻¹ᵁ U)`
that act on the two sides of base change agree after the identification of the opens. -/
theorem baseChange_ring (U : X.Opens) :
    (f.appIso U).inv ≫ g.app (f ''ᵁ U) ≫
      Y'.presheaf.map (eqToHom (baseChange_image_preimage f g fst snd hP U)).op =
    snd.app U ≫
      (Scheme.Hom.appIso fst (snd ⁻¹ᵁ U)).inv := by
  rw [← cancel_mono (Scheme.Hom.appIso fst (snd ⁻¹ᵁ U)).hom,
    Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq snd f
      (fst ≫ g) hP.w U]
  simp [Scheme.Hom.appIso_hom]
  congr 1
  congr 1
  rw [← Functor.map_comp]
  rfl

variable (N : Y'.Modules)

/-- Restriction along `f` of the pushforward along `g` and pushforward along `snd` of
the restriction along `fst` have the same sections: this is the transport of sections
along `baseChange_image_preimage`. -/
def baseChangeSections (U : X.Opens) :
    Γ((restrictFunctor f).obj ((pushforward g).obj N), U) ⟶
      Γ((pushforward snd).obj ((restrictFunctor fst).obj N), U) :=
  N.presheaf.map (eqToHom (baseChange_image_preimage f g fst snd hP U)).op

/-- The inverse of `baseChangeSections`. -/
def baseChangeSectionsInv (U : X.Opens) :
    Γ((pushforward snd).obj ((restrictFunctor fst).obj N), U) ⟶
      Γ((restrictFunctor f).obj ((pushforward g).obj N), U) :=
  N.presheaf.map (eqToHom (baseChange_image_preimage f g fst snd hP U).symm).op

/-- The transport of sections is linear over `Γ(X, U)`. -/
theorem baseChangeSections_smul (U : X.Opens) (r : Γ(X, U))
    (x : Γ((restrictFunctor f).obj ((pushforward g).obj N), U)) :
    (baseChangeSections f g fst snd hP N U).hom (r • x) =
      r • (baseChangeSections f g fst snd hP N U).hom x := by
  have hL : (r • x : Γ((restrictFunctor f).obj ((pushforward g).obj N), U)) =
      (show Γ(Y', g ⁻¹ᵁ f ''ᵁ U) from (g.app (f ''ᵁ U)).hom ((f.appIso U).inv.hom r)) •
        (show Γ(N, g ⁻¹ᵁ f ''ᵁ U) from x) := rfl
  have hR : (r • (baseChangeSections f g fst snd hP N U).hom x :
      Γ((pushforward snd).obj ((restrictFunctor fst).obj N), U)) =
      (show Γ(Y', fst ''ᵁ snd ⁻¹ᵁ U) from
        (fst.appIso (snd ⁻¹ᵁ U)).inv.hom
          (snd.app U |>.hom r)) •
        (show Γ(N, fst ''ᵁ snd ⁻¹ᵁ U) from
          (baseChangeSections f g fst snd hP N U).hom x) := rfl
  have hring := congrArg (fun φ : Γ(X, U) ⟶ Γ(Y', fst ''ᵁ snd ⁻¹ᵁ U) =>
    φ.hom r) (baseChange_ring f g fst snd hP U)
  refine (Scheme.Modules.map_smul N _ _ _).trans ?_
  refine Eq.symm (hR.trans ?_)
  exact congrArg (fun s : Γ(Y', fst ''ᵁ snd ⁻¹ᵁ U) =>
    s • (show Γ(N, fst ''ᵁ snd ⁻¹ᵁ U) from
      (baseChangeSections f g fst snd hP N U).hom x)) hring.symm

theorem baseChangeSectionsInv_baseChangeSections (U : X.Opens)
    (x : Γ((restrictFunctor f).obj ((pushforward g).obj N), U)) :
    (baseChangeSectionsInv f g fst snd hP N U).hom
      ((baseChangeSections f g fst snd hP N U).hom x) = x := by
  show (N.presheaf.map _ ≫ N.presheaf.map _).hom x = x
  rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id]
  erw [CategoryTheory.Functor.map_id]
  rfl

theorem baseChangeSections_baseChangeSectionsInv (U : X.Opens)
    (x : Γ((pushforward snd).obj ((restrictFunctor fst).obj N),
      U)) :
    (baseChangeSections f g fst snd hP N U).hom
      ((baseChangeSectionsInv f g fst snd hP N U).hom x) = x := by
  show (N.presheaf.map _ ≫ N.presheaf.map _).hom x = x
  rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id]
  erw [CategoryTheory.Functor.map_id]
  rfl

/-- The transport of sections as a linear equivalence over `Γ(X, U)`. -/
def baseChangeSectionsEquiv (U : X.Opens) :
    Γ((restrictFunctor f).obj ((pushforward g).obj N), U) ≃ₗ[Γ(X, U)]
      Γ((pushforward snd).obj ((restrictFunctor fst).obj N),
        U) where
  toFun x := (baseChangeSections f g fst snd hP N U).hom x
  map_add' x y := map_add _ x y
  map_smul' r x := baseChangeSections_smul f g fst snd hP N U r x
  invFun x := (baseChangeSectionsInv f g fst snd hP N U).hom x
  left_inv x := baseChangeSectionsInv_baseChangeSections f g fst snd hP N U x
  right_inv x := baseChangeSections_baseChangeSectionsInv f g fst snd hP N U x

/-- Restriction along `f` of the pushforward along `g` is pushforward along `snd` of
restriction along `fst`, object by object. -/
def pushforwardRestrictBaseChangeIso :
    (restrictFunctor f).obj ((pushforward g).obj N) ≅
      (pushforward snd).obj ((restrictFunctor fst).obj N) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ (baseChangeSectionsEquiv f g fst snd hP N V.unop).toModuleIso)
      (fun {V W} i ↦ by
        ext x
        exact Scheme.Modules.presheaf_map_square_eq N
          ((Opens.map g.base).map (f.opensFunctor.map i.unop)).op
          (eqToHom (baseChange_image_preimage f g fst snd hP W.unop)).op
          (eqToHom (baseChange_image_preimage f g fst snd hP V.unop)).op
          (fst.opensFunctor.map
            ((Opens.map snd.base).map i.unop)).op x))

/-- Restriction along an open immersion `f` commutes with pushforward along `g`, in the form
`g_* ⋙ f^* ≅ fst^* ⋙ snd_*` for the base change of `f` along `g`. -/
def pushforwardRestrictBaseChangeNatIso :
    pushforward g ⋙ restrictFunctor f ≅
      restrictFunctor fst ⋙ pushforward snd :=
  NatIso.ofComponents (pushforwardRestrictBaseChangeIso f g fst snd hP) (fun {M N} φ ↦ by
    apply Scheme.Modules.hom_ext
    intro W
    ext x
    exact (NatTrans.naturality_apply φ.mapPresheaf
      (eqToHom (baseChange_image_preimage f g fst snd hP W)).op x).symm)

/-- Extension by zero commutes with pullback along any morphism `g : Y' ⟶ Y`, for any pullback
square of `f` along `g`: `g^* ∘ f_! ≅ fst_! ∘ snd^*`, where `fst : P ⟶ Y'` is the base change of
the open immersion `f`.

This is the conjugate under the adjunctions `f_! ⊣ f^*`, `fst_! ⊣ fst^*`, `g^* ⊣ g_*` and
`snd^* ⊣ snd_*` of the base change isomorphism `f^* g_* ≅ snd_* fst^*` of restriction and
pushforward. Stacks has no tag for this statement; it follows formally from the adjunctions. -/
def extendByZeroCompPullbackIsoOfIsPullback :
    extendByZero f ⋙ pullback g ≅ pullback snd ⋙ extendByZero fst :=
  Adjunction.leftAdjointUniq
    ((extendByZeroAdjunction f).comp (pullbackPushforwardAdjunction g))
    (((pullbackPushforwardAdjunction snd).comp
      (extendByZeroAdjunction fst)).ofNatIsoRight
        (pushforwardRestrictBaseChangeNatIso f g fst snd hP).symm)

end BaseChange

/-- Extension by zero commutes with pullback along every morphism `g : Y' ⟶ Y`, for the base
changed open immersion `pullback.fst g f`:
`g^* ∘ f_! ≅ (pullback.fst g f)_! ∘ (pullback.snd g f)^*`. This is
`extendByZeroCompPullbackIsoOfIsPullback` for the chosen pullback. -/
def extendByZeroCompPullbackIso {Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    extendByZero f ⋙ pullback g ≅
      pullback (Limits.pullback.snd g f) ⋙ extendByZero (Limits.pullback.fst g f) :=
  extendByZeroCompPullbackIsoOfIsPullback f g (Limits.pullback.fst g f) (Limits.pullback.snd g f)
    (IsPullback.of_hasPullback g f)

end

end AlgebraicGeometry.Scheme.Modules
