/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The restriction square, read on opens

`#572` step 2 globalizes `isCoherent_pushforward_of_surjective` along an affine cover, and the
criterion it feeds (`Modules.isCoherent_iff_restrict_affineOpenCover`) asks for
`(ι_* F).restrict (𝒰.f i)` while the affine theorem produces the pushforward along
`ι ∣_ V`. Comparing the two is a base-change statement about the square

```
  f ⁻¹ᵁ U  ──(f ⁻¹ᵁ U).ι──>  X
     │                        │
  f ∣_ U                      f
     │                        │
     U   ─────U.ι─────────>   Y
```

This file records the geometric half of that comparison: the two ways round the square agree
as functors on opens.

## Why this is the whole geometric content

Both composites send an open `V` of `U` to the preimage of `V` under `f`, viewed in `X` —
`image_morphismRestrict_preimage` is exactly that equality, and it is at the pin. `Opens` is a
poset, so a natural transformation between functors into it is determined by nothing at all:
agreement on objects *is* the isomorphism, and `NatIso.ofComponents` discharges naturality
because the naturality squares live in a subsingleton.

## The comparison of module sheaves, object by object

`pushforwardRestrictIso` is the comparison `#572` step 2 consumes: for one `M`, the two ways round
the square agree. `Modules.isCoherent_iff_restrict_affineOpenCover` asks only for
`IsFinitePresentation` of `(ι_* F).restrict (𝒰.f i)`, which transfers along an isomorphism, so an
isomorphism of *objects* is what is needed and a natural isomorphism of functors is not.

That is not only economy. The functor-level statement is the one
`SheafOfModules.pushforwardNatIso` and `pushforwardCongr` are built for, and going through them
means letting unification discover the two site functors underneath `Scheme.Modules.pushforward`
and `Scheme.Modules.restrictFunctor`. **That does not terminate**: it runs `whnf` past 200000
heartbeats, the same failure `ChartExtension.lean` records for `fromTildeΓ`. Naming the objects and
comparing their sections avoids the search entirely.

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

## What this file does not do

It does not build the *functor* comparison
`pushforward f ⋙ restrictFunctor U.ι ≅ restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U)`.
Naturality in `M` is not proved here, and the coherence criterion does not need it.
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

/-- **Any two ways round a square of restrictions agree.**

`Opens` is a poset, so the two composites are `M.presheaf.map` of parallel morphisms and
`Subsingleton.elim` settles it. Stated on its own because in a clean context its rewrites fire,
whereas at the use site the goal carries the transparency defect described above and only `exact`
works. -/
theorem presheaf_map_square_eq (M : X.Modules) {A B C D : X.Opens}
    (α : op A ⟶ op B) (β : op B ⟶ op C) (γ : op A ⟶ op D) (δ : op D ⟶ op C) (x : Γ(M, A)) :
    (M.presheaf.map β).hom ((M.presheaf.map α).hom x)
      = (M.presheaf.map δ).hom ((M.presheaf.map γ).hom x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  exact congrArg (fun φ => (M.presheaf.map φ).hom x) (Subsingleton.elim _ _)

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

/-- **The base-change comparison, object by object.**

Pushing forward along `f` and then restricting to `U` is restricting to `f ⁻¹ᵁ U` and then pushing
forward along `f ∣_ U`. This is what `#572` step 2 consumes:
`isCoherent_iff_restrict_affineOpenCover` asks for `IsFinitePresentation` of the restriction, which
transfers along an isomorphism, so the object-level statement suffices and the functor-level one is
not needed. -/
noncomputable def pushforwardRestrictIso :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V => (restrictSquareSectionsEquiv f U M V.unop).toModuleIso)
      (fun {V W} i => by
        ext x
        exact presheaf_map_square_eq M
          ((Opens.map f.base).map (U.ι.opensFunctor.map i.unop)).op
          (eqToHom (image_morphismRestrict_preimage f U W.unop)).op
          (eqToHom (image_morphismRestrict_preimage f U V.unop)).op
          ((f ⁻¹ᵁ U).ι.opensFunctor.map ((Opens.map (f ∣_ U).base).map i.unop)).op x))

end Modules

end AlgebraicGeometry
