/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Restrict
import DerivedAlgGeo.AlgebraicGeometry.Modules.Restriction.Sections
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pushforward and restriction across an open square

For any scheme morphism `f : X ⟶ Y` and open `U` of `Y`, compare the two ways
to push forward a module sheaf and restrict it across the square

```
  f ⁻¹ᵁ U  ──(f ⁻¹ᵁ U).ι──>  X
     │                        │
  f ∣_ U                      f
     │                        │
     U   ─────U.ι─────────>   Y
```

The comparison is independent of finiteness, affineness, and coherence.

## Why this is the whole geometric content

Both composites send an open `V` of `U` to the preimage of `V` under `f`, viewed in `X` —
`image_morphismRestrict_preimage` is exactly that equality, and it is at the pin. `Opens` is a
poset, so a natural transformation between functors into it is determined by nothing at all:
agreement on objects *is* the isomorphism, and `NatIso.ofComponents` discharges naturality
because the naturality squares live in a subsingleton.

## The comparison of module sheaves, object by object

`pushforwardRestrictIso` compares the resulting module sheaves for one `M`.
`pushforwardRestrictNatIso` assembles these isomorphisms into a functor comparison;
its naturality is the naturality of a sheaf morphism on the same transported
sections. The coherent pushforward chart argument consumes the object component.

## What the comparison rests on

Both sides have the *same sections*: `Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V))` and
`Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V))` are `rfl`-equal to the two composites, and the opens are
equal by `image_morphismRestrict_preimage` — the equality this file's first half packages. So the
comparison map is that transport, `restrictSquareSections`.

What has to be proved is that the transport is linear, and this is the "equality of sheaf-of-rings
data" the earlier version of this file left open. It decomposes into four steps, three of which are
definitional:

* each side's scalar action unfolds to an action through `Scheme.Hom.app`, by `rfl`;
* the open immersion's `Scheme.Hom.appIso` is the identity — `Scheme.Opens.ι_appIso`, and this one
  is **not** definitional, it needs the rewrite;
* the transport is semilinear over `X`'s structure sheaf — `Scheme.Modules.map_smul`;
* the two structure-sheaf maps differ by exactly that transport — `morphismRestrict_app`, whose
  `eqToHom` is the same one, direction included.

## Why the naturality square is written with explicit morphisms

`presheaf_map_square_eq` is applied at its four opens morphisms spelled out, and that is the whole
reason this file needs no `maxHeartbeats` raise. Left as `_`, they are metavariables Lean has to
solve by unifying against a goal that also carries the `instances`-transparency defect — which costs
more than twenty times the default budget and buys nothing, since the morphisms are determined and
can simply be written down. Supplied explicitly, the square closes in one `exact`, in seconds.

The lesson generalises, and it is the opposite of the reflex: a large heartbeat bump here meant the
*statement* was underspecified, not that the proof was hard.

`presheaf_map_square_eq` is stated separately because in a clean context its rewrites fire, while at
the use site only `exact` is available — `exact` unifies up to defeq and never has to match
syntactically, which is what the defective goal rules out.

The functor comparison is built from these explicit objectwise components.
The last theorem identifies its mate in the open-immersion direction with
the direct pushforward-composite comparison. The separate claim that the
mate of `pullbackRestrictNatIso` equals this functor comparison remains open.
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- **The restriction square commutes on opens.** Going round by `U.ι` and then taking the
preimage under `f` is going round by `f ∣_ U` and then taking the image in `X`.

This is `image_morphismRestrict_preimage` packaged as an isomorphism of the two composite
functors `Opens U ⥤ Opens X`, which is the form the base-change comparison of pushforwards
consumes. -/
noncomputable def restrictSquareOpensIso :
    U.ι.opensFunctor ⋙ Opens.map f.base ≅
      Opens.map (f ∣_ U).base ⋙ (f ⁻¹ᵁ U).ι.opensFunctor :=
  NatIso.ofComponents (fun V ↦ eqToIso (image_morphismRestrict_preimage f U V).symm)


section Modules

variable (M : X.Modules)

/-- **The transport of sections across the restriction square.**

Both ways round the square have the same sections over `V` — `Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V))` one way and
`Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V))` the other, each `rfl`-equal to the composite — so the
comparison is the transport along `image_morphismRestrict_preimage`. -/
noncomputable def restrictSquareSections (V : U.toScheme.Opens) :
    Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) ⟶ Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) :=
  M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op

/-- The transport the other way. -/
noncomputable def restrictSquareSectionsInv (V : U.toScheme.Opens) :
    Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) ⟶ Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) :=
  M.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V).symm).op

@[simp]
theorem restrictSquareSectionsInv_restrictSquareSections (V : U.toScheme.Opens)
    (x : Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V))) :
    (restrictSquareSectionsInv f U M V).hom ((restrictSquareSections f U M V).hom x) = x := by
  show (M.presheaf.map _ ≫ M.presheaf.map _).hom x = x
  rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

@[simp]
theorem restrictSquareSections_restrictSquareSectionsInv (V : U.toScheme.Opens)
    (x : Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V))) :
    (restrictSquareSections f U M V).hom ((restrictSquareSectionsInv f U M V).hom x) = x := by
  show (M.presheaf.map _ ≫ M.presheaf.map _).hom x = x
  rw [← Functor.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id,
    CategoryTheory.Functor.map_id]
  rfl

/-- **The transport is linear**, which is the whole content of the module-level comparison.

Each side's action unfolds by `rfl` to an action through `Scheme.Hom.app`; `Scheme.Opens.ι_appIso`
removes the open immersion's `appIso`, which is the one step that is not definitional; and
`morphismRestrict_app` says the two structure-sheaf maps differ by exactly the transport being
compared. -/
theorem restrictSquareSections_smul (V : U.toScheme.Opens) (r : Γ(U.toScheme, V))
    (x : Γ(((Scheme.Modules.pushforward f).obj M).restrict U.ι, V)) :
    (show Γ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V) from
        (restrictSquareSections f U M V).hom (r • x))
      = r • (show Γ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V) from
        (restrictSquareSections f U M V).hom x) := by
  have hL : (r • x : Γ(((Scheme.Modules.pushforward f).obj M).restrict U.ι, V))
      = (show Γ(X, f ⁻¹ᵁ (U.ι ''ᵁ V)) from
          (f.app (U.ι ''ᵁ V)).hom ((Scheme.Hom.appIso U.ι V).inv.hom r)) •
        (show Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) from x) := rfl
  have hR : (r • (show Γ((Scheme.Modules.pushforward (f ∣_ U)).obj
        (M.restrict (f ⁻¹ᵁ U).ι), V) from (restrictSquareSections f U M V).hom x))
      = (show Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) from
          (Scheme.Hom.appIso (f ⁻¹ᵁ U).ι ((f ∣_ U) ⁻¹ᵁ V)).inv.hom
            (((f ∣_ U).app V).hom r)) •
        (show Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) from
          (restrictSquareSections f U M V).hom x) := rfl
  have hι : (Scheme.Hom.appIso U.ι V).inv.hom r = (show Γ(Y, U.ι ''ᵁ V) from r) := by
    rw [Scheme.Opens.ι_appIso]; rfl
  have hmr := congrArg (fun φ : Γ(U.toScheme, V) ⟶ Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) =>
    φ.hom r) (morphismRestrict_app f U V)
  have hι' : (Scheme.Hom.appIso (f ⁻¹ᵁ U).ι ((f ∣_ U) ⁻¹ᵁ V)).inv.hom (((f ∣_ U).app V).hom r)
      = (show Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) from ((f ∣_ U).app V).hom r) := by
    rw [Scheme.Opens.ι_appIso]; rfl
  refine (congrArg (fun y : Γ(M, f ⁻¹ᵁ (U.ι ''ᵁ V)) =>
    (restrictSquareSections f U M V).hom y) hL).trans ?_
  refine (Scheme.Modules.map_smul M _ _ _).trans ?_
  refine Eq.symm (hR.trans ?_)
  refine congrArg (fun s : Γ(X, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) =>
    s • (show Γ(M, (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) from
      (restrictSquareSections f U M V).hom x)) ?_
  refine hι'.trans (hmr.trans ?_)
  exact congrArg (fun s : Γ(Y, U.ι ''ᵁ V) =>
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op).hom
      ((f.app (U.ι ''ᵁ V)).hom s)) hι.symm

/-- **The comparison on sections over one open, as a linear equivalence.**

Named at the `Γ` spelling: written through the unfolded pushforward the `Module` instance does not
synthesize, which is `references/instance-transparency.md` technique 5 in its usual form. -/
noncomputable def restrictSquareSectionsEquiv (V : U.toScheme.Opens) :
    Γ(((Scheme.Modules.pushforward f).obj M).restrict U.ι, V) ≃ₗ[Γ(U.toScheme, V)]
      Γ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι), V) where
  toFun x := (restrictSquareSections f U M V).hom x
  map_add' x y := map_add _ x y
  map_smul' r x := restrictSquareSections_smul f U M V r x
  invFun x := (restrictSquareSectionsInv f U M V).hom x
  left_inv x := restrictSquareSectionsInv_restrictSquareSections f U M V x
  right_inv x := restrictSquareSections_restrictSquareSectionsInv f U M V x

/-- **The open-square comparison, object by object.**

Pushing forward along `f` and then restricting to `U` is restricting to `f ⁻¹ᵁ U` and then pushing
forward along `f ∣_ U`. The coherent-pushforward chart argument uses this
objectwise isomorphism to transport finite presentation.

The component on every open is `restrictSquareSections`, transporting along
`image_morphismRestrict_preimage`. -/
noncomputable def pushforwardRestrictIso :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => (restrictSquareSectionsEquiv f U M V.unop).toModuleIso)
      (fun {V W} i => by
        ext x
        exact Scheme.Modules.presheaf_map_square_eq M
          ((Opens.map f.base).map (U.ι.opensFunctor.map i.unop)).op
          (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
          (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
          ((f ⁻¹ᵁ U).ι.opensFunctor.map ((Opens.map (f ∣_ U).base).map i.unop)).op x))

end Modules

/-- The independent comparison of pushforward and restriction around an open square.
Its component at `M` is `pushforwardRestrictIso f U M`, whose map on sections is
`restrictSquareSections f U M`. -/
noncomputable def pushforwardRestrictNatIso :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ⋙
        Scheme.Modules.pushforward (f ∣_ U) :=
  NatIso.ofComponents (pushforwardRestrictIso f U) (fun {M N} g ↦ by
    apply Scheme.Modules.hom_ext
    intro W
    ext x
    exact (NatTrans.naturality_apply g.mapPresheaf
      (eqToHom (image_morphismRestrict_preimage f U W)).op x).symm)

/-- The geometric pullback comparison around the open square, assembled directly from
the restriction/pullback comparison, pullback composition, and the equality of the two
scheme morphism composites. -/
noncomputable def pullbackRestrictNatIso :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι ≅
      Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) :=
  Functor.isoWhiskerLeft (Scheme.Modules.pullback f)
      (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pullbackComp (f ∣_ U) U.ι).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
      (Scheme.Modules.pullback (f ∣_ U))

/-- The two pushforward composites around the open square agree. This comparison is
built from composition and the equality `morphismRestrict_ι`, independently of
`pushforwardRestrictNatIso`. -/
noncomputable def squarePushforwardIso :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp (f ⁻¹ᵁ U).ι f ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
    (Scheme.Modules.pushforwardComp (f ∣_ U) U.ι).symm

set_option maxRecDepth 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Taking the mate of the independent pushforward/restriction comparison in
the open-immersion direction gives the direct comparison of pushforward
composites. The proof reduces pointwise to maps in the poset of opens. -/
theorem pushforwardRestrictNatIso_mate :
    mateEquiv (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)
      (Scheme.Modules.restrictAdjunction U.ι) (pushforwardRestrictNatIso f U).hom =
        (squarePushforwardIso f U).hom := by
  ext M W x
  change ((
    (Scheme.Modules.restrictAdjunction U.ι).unit.app
      ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f).obj M) ≫
    (Scheme.Modules.pushforward U.ι).map
      ((pushforwardRestrictNatIso f U).hom.app
        ((Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι).obj M)) ≫
    (Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).counit.app M)).app W).hom x =
      (((squarePushforwardIso f U).hom.app M).app W).hom x
  change (M.presheaf.map _ ≫ M.presheaf.map _ ≫ M.presheaf.map _).hom x =
    (M.presheaf.map _).hom x
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

end AlgebraicGeometry
