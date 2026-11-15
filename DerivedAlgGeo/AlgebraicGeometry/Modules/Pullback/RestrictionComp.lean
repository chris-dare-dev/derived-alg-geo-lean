/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Restriction and pullback along composites of open immersions

Along an open immersion `f`, Mathlib identifies restriction with pullback by
`restrictFunctorIsoPullback f`, and each side has its own compositor:
`restrictFunctorComp` for restriction and `pullbackComp` for pullback. This file
proves that the identification is monoidal: along a composite `g ≫ f` of open
immersions, the identification followed by the pullback compositor is the
restriction compositor followed by the identifications along `g` and `f`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp'` and
  `AlgebraicGeometry.Scheme.Modules.pullbackComp'`: the two compositors along a
  morphism `h` equal to `g ≫ f`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_pullbackComp_inv`: the
  identification is compatible with the compositors, as natural transformations.
* `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_pullbackComp'_hom` and
  `AlgebraicGeometry.Scheme.Modules.pullbackComp'_inv_restrictFunctorIsoPullback_inv`: the
  same, at a module sheaf, for `h = g ≫ f`.

## Implementation notes

`restrictFunctorIsoPullback f` is the uniqueness of left adjoints applied to
`restrictAdjunction f` and `pullbackPushforwardAdjunction f`, so its conjugate is
the identity. `pullbackComp` is conjugate to `pushforwardComp`, and so is
`restrictFunctorComp`, checked section by section. Both sides of the
compatibility therefore have the same conjugate, and `conjugateEquiv` is
injective.

The primed compositors take the composite as a separate morphism `h` with a
proof of `g ≫ f = h`, so that consumers can state the compatibility at a
test object without rewriting the composite.

## References

Mathlib's `conjugateEquiv_pullbackComp_inv` and `Adjunction.leftAdjointUniq`.

## Tags

module sheaf, open immersion, restriction, pullback, compositor
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- On sections over `U`, restriction along an open immersion of a morphism of module sheaves is
the morphism on sections over the image of `U`. -/
@[simp]
lemma restrictFunctor_map_app (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules} (φ : M ⟶ N)
    (U : X.Opens) : ((restrictFunctor f).map φ).app U = φ.app (f ''ᵁ U) := rfl

/-- Two composable restrictions of a module sheaf are the restriction along the composite. -/
@[reassoc]
lemma presheaf_map_comp_eq (M : X.Modules) {U V W : X.Opensᵒᵖ}
    (α : U ⟶ V) (β : V ⟶ W) (γ : U ⟶ W) :
    M.presheaf.map α ≫ M.presheaf.map β = M.presheaf.map γ := by
  rw [← Functor.map_comp]
  exact congrArg _ (Subsingleton.elim _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Under the conjugation of the restriction adjunctions, `restrictFunctorComp` becomes
`pushforwardComp`. Both are restrictions along equalities of opens on sections, so the proof
checks it section by section. -/
lemma conjugateEquiv_restrictFunctorComp_hom (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f]
    [IsOpenImmersion g] :
    conjugateEquiv ((restrictAdjunction g).comp (restrictAdjunction f))
      (restrictAdjunction (f ≫ g)) (restrictFunctorComp f g).hom = (pushforwardComp f g).hom := by
  refine NatTrans.ext (funext fun M => hom_ext _ _ fun W => ?_)
  simp only [conjugateEquiv_apply_app, Adjunction.comp_counit_app, Hom.comp_app,
    pushforwardComp_hom_app_app, Functor.map_comp]
  simp only [pushforward_map_app, restrictFunctor_map_app,
    restrictAdjunction_counit_app_app, restrictAdjunction_unit_app_app,
    restrictFunctorComp_hom_app_app, Functor.comp_obj, pushforward_obj_presheaf_map,
    ← Functor.map_comp]
  exact M.presheaf.map_id _

/-- `restrictFunctorIsoPullback` comes from the uniqueness of left adjoints, so under the two
adjunctions to pushforward it conjugates to the identity. -/
lemma conjugateEquiv_restrictFunctorIsoPullback_hom (h : X ⟶ Y) [IsOpenImmersion h] :
    conjugateEquiv (pullbackPushforwardAdjunction h) (restrictAdjunction h)
      (restrictFunctorIsoPullback h).hom = 𝟙 _ := by
  simp [restrictFunctorIsoPullback, Adjunction.leftAdjointUniq]

/-- The identification of restriction with pullback is compatible with the compositors. -/
lemma restrictFunctorIsoPullback_hom_pullbackComp_inv (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] :
    (restrictFunctorIsoPullback (f ≫ g)).hom ≫ (pullbackComp f g).inv =
      (restrictFunctorComp f g).hom ≫
        Functor.whiskerLeft (restrictFunctor g) (restrictFunctorIsoPullback f).hom ≫
        Functor.whiskerRight (restrictFunctorIsoPullback g).hom (pullback f) := by
  apply (conjugateEquiv ((pullbackPushforwardAdjunction g).comp
    (pullbackPushforwardAdjunction f)) (restrictAdjunction (f ≫ g))).injective
  rw [← conjugateEquiv_comp _ (pullbackPushforwardAdjunction (f ≫ g)),
    ← conjugateEquiv_comp _ ((restrictAdjunction g).comp (restrictAdjunction f)),
    ← conjugateEquiv_comp _ ((restrictAdjunction g).comp (pullbackPushforwardAdjunction f)),
    conjugateEquiv_restrictFunctorIsoPullback_hom, conjugateEquiv_pullbackComp_inv,
    conjugateEquiv_restrictFunctorComp_hom, conjugateEquiv_whiskerLeft,
    conjugateEquiv_whiskerRight, conjugateEquiv_restrictFunctorIsoPullback_hom,
    conjugateEquiv_restrictFunctorIsoPullback_hom]
  simp

/-- Restriction along a composite of open immersions. The prime marks the difference from
`restrictFunctorComp`: the composite is a separate morphism `h` with a proof of `g ≫ f = h`. -/
noncomputable def restrictFunctorComp' (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h] (hgf : g ≫ f = h) :
    restrictFunctor h ≅ restrictFunctor f ⋙ restrictFunctor g :=
  restrictFunctorCongr hgf.symm ≪≫ restrictFunctorComp g f

/-- On sections, `restrictFunctorComp'` is restriction along an equality of opens. -/
@[simp]
lemma restrictFunctorComp'_hom_app_app (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h] (hgf : g ≫ f = h)
    (M : X.Modules) (U : Z.Opens) :
    ((restrictFunctorComp' g f h hgf).hom.app M).app U =
      M.presheaf.map (eqToHom (by subst hgf; simp)).op := by
  subst hgf
  simp only [restrictFunctorComp', Iso.trans_hom, NatTrans.comp_app, Hom.comp_app,
    restrictFunctorCongr_hom_app_app, restrictFunctorComp_hom_app_app]
  exact presheaf_map_comp_eq _ _ _ _

/-- On sections, the inverse of `restrictFunctorComp'` is restriction along an equality of
opens. -/
@[simp]
lemma restrictFunctorComp'_inv_app_app (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h] (hgf : g ≫ f = h)
    (M : X.Modules) (U : Z.Opens) :
    ((restrictFunctorComp' g f h hgf).inv.app M).app U =
      M.presheaf.map (eqToHom (by subst hgf; simp)).op := by
  subst hgf
  simp only [restrictFunctorComp', Iso.trans_inv, NatTrans.comp_app, Hom.comp_app,
    restrictFunctorCongr_inv_app_app, restrictFunctorComp_inv_app_app]
  exact presheaf_map_comp_eq _ _ _ _

/-- Pullback along a composite. The prime marks the difference from `pullbackComp`: the
composite is a separate morphism `h` with a proof of `g ≫ f = h`, and the isomorphism runs from
the pullback along `h`. -/
noncomputable def pullbackComp' (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X)
    (hgf : g ≫ f = h) : pullback h ≅ pullback f ⋙ pullback g :=
  pullbackCongr hgf.symm ≪≫ (pullbackComp g f).symm

/-- The component at `M` of `pullbackComp'`. -/
noncomputable def pullbackCompApp (g : Z ⟶ Y) (f : Y ⟶ X) (h : Z ⟶ X) (hgf : g ≫ f = h)
    (M : X.Modules) : (pullback h).obj M ≅ (pullback g).obj ((pullback f).obj M) :=
  (pullbackComp' g f h hgf).app M

set_option backward.isDefEq.respectTransparency false in
/-- At a module sheaf, the identification of restriction with pullback along `h = g ≫ f`,
followed by the pullback compositor, is the restriction compositor followed by the
identifications along `g` and `f`. -/
@[reassoc]
lemma restrictFunctorIsoPullback_hom_pullbackComp'_hom (g : Z ⟶ Y)
    (f : Y ⟶ X) (h : Z ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h]
    (hgf : g ≫ f = h) (M : X.Modules) :
    (restrictFunctorIsoPullback h).hom.app M ≫ (pullbackComp' g f h hgf).hom.app M =
      (restrictFunctorComp' g f h hgf).hom.app M ≫
        (restrictFunctorIsoPullback g).hom.app (M.restrict f) ≫
        (pullback g).map ((restrictFunctorIsoPullback f).hom.app M) := by
  subst hgf
  have := congr_app (restrictFunctorIsoPullback_hom_pullbackComp_inv g f) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at this
  simp only [pullbackComp', pullbackCongr, eqToIso_refl, Iso.trans_hom, Iso.refl_hom,
    Iso.symm_hom, Category.id_comp]
  refine this.trans ?_
  congr 1
  ext U : 1
  simp only [restrictFunctorComp'_hom_app_app, restrictFunctorComp_hom_app_app]

/-- The inverse form of `restrictFunctorIsoPullback_hom_pullbackComp'_hom`. -/
@[reassoc]
lemma pullbackComp'_inv_restrictFunctorIsoPullback_inv (g : Z ⟶ Y)
    (f : Y ⟶ X) (h : Z ⟶ X) [IsOpenImmersion g] [IsOpenImmersion f] [IsOpenImmersion h]
    (hgf : g ≫ f = h) (M : X.Modules) :
    (pullbackComp' g f h hgf).inv.app M ≫ (restrictFunctorIsoPullback h).inv.app M =
      (pullback g).map ((restrictFunctorIsoPullback f).inv.app M) ≫
        (restrictFunctorIsoPullback g).inv.app (M.restrict f) ≫
        (restrictFunctorComp' g f h hgf).inv.app M := by
  let e₁ := (restrictFunctorIsoPullback h).app M ≪≫ (pullbackComp' g f h hgf).app M
  let e₂ := (restrictFunctorComp' g f h hgf).app M ≪≫
      (restrictFunctorIsoPullback g).app (M.restrict f) ≪≫
      (pullback g).mapIso ((restrictFunctorIsoPullback f).app M)
  have : e₁ = e₂ := Iso.ext (restrictFunctorIsoPullback_hom_pullbackComp'_hom g f h hgf M)
  simpa [e₁, e₂] using congrArg Iso.inv this

end AlgebraicGeometry.Scheme.Modules
