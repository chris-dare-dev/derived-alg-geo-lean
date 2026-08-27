/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.ConstantSheafPullback
import DerivedAlgGeo.CategoryTheory.ExtAdjunction
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Cohomology is unchanged by an exact pushforward

`sheafHPushforwardAddEquiv` : `Hⁿ(K, F) ≃+ Hⁿ(J, G_* F)`, for a continuous `G` whose pullback and
pushforward are both exact. This is `#572` step 3 — cohomology invariance along a closed immersion
— with the geometry replaced by the two hypotheses that actually carry the argument.

## The three pieces, and where each came from

`Sheaf.H F n` is `Ext ((constantSheaf J _).obj (ULift ℤ)) F n`, so the comparison is an `Ext`
transport and not a Čech computation. It assembles from exactly two results and nothing else:

* `constantSheafCompSheafPullbackIso` (`ConstantSheafPullback.lean`) moves the constant sheaf
  across `G⁻¹ ⊣ G_*`, giving `G⁻¹ ℤ_J ≅ ℤ_K`;
* `extAdjunctionAddEquiv` (`ExtAdjunction.lean`) transports `Ext` across that same adjunction;
* `Ext.precompAddEquiv` glues the two, because the first supplies an *isomorphism* rather than an
  equality of first arguments.

The body is one `.trans`. Everything hard happened in the two files it cites.

## Three traps, all of them costing real time, none of them mathematics

**The `Abelian` hypothesis is a diamond, and it was the actual blocker.** Writing
`[Abelian (Sheaf J AddCommGrpCat.{w})]` as a *variable* puts a second `Preadditive` structure on a
category that already has one: the hypothesis carries `Abelian.toPreadditive`, while the ambient
instance is `Preadditive.fullSubcategory (Presheaf.IsSheaf J)`. `Functor.Additive` is stated
against `Preadditive`, so `(G.sheafPullback _ J K).Additive` then fails to synthesize *even when
the hypothesis is named, `include`d and `haveI`'d* — the two spellings are not reducibly equal.
The fix is to assume nothing: with `HasSheafify` and the imports below, `sheafIsAbelian` is found
and there is only one `Preadditive`. Same family as `#662`.

**`HasSheafify`, not `HasWeakSheafify`.** `sheafIsAbelian` needs the former; with only the latter
the `Abelian` instance is genuinely absent rather than duplicated.

**The `Sites.Abelian` and `Grp.Abelian` imports are load-bearing.** Neither
`ConstantSheafPullback.lean` nor `ExtAdjunction.lean` reaches them, and without them
`Abelian (Sheaf J AddCommGrpCat)` is not inferrable — which reads exactly like a missing
mathematical input and is not one.

## A correction, recorded because the wrong diagnosis was written down first

An earlier pass concluded that stating this against `Sheaf.H` was itself the problem — it produced
a `synthInstance` failure at 20k heartbeats and, raised to 1M, an `isDefEq` timeout after 4m24s —
and that the cure was to state everything in `Ext` and relegate `Sheaf.H` to a `rfl`-lemma. **That
was wrong.** The timeout was the diamond above, surfacing at the only place that forced the two
`Preadditive` structures to meet. With the diamond gone, the `Sheaf.H` form elaborates in seconds
and is stated directly, as `#572` asks. The `Ext` form is kept because it is the reusable one, not
because `Sheaf.H` needs avoiding.

## Scope

Both exactness hypotheses are real and neither is decoration. `G_*` is exact for a closed
immersion, which is the intended application, but it is only left exact in general — a caller with
a general continuous map gets nothing from this file. `EnoughInjectives` is what
`extAdjunctionAddEquiv` needs.

## Main results

* `sheafCohomologyPushforwardAddEquiv` — the `Ext` form.
* `sheafH_eq_ext` — `Sheaf.H` is that `Ext`, definitionally.
* `sheafHPushforwardAddEquiv` — the cohomology form, which is `#572` step 3's statement.
-/

universe w w' v u

open CategoryTheory Limits Opposite Abelian

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (G : C ⥤ D) [G.IsContinuous J K]
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  [HasGlobalSectionsFunctor J AddCommGrpCat.{w}] [HasGlobalSectionsFunctor K AddCommGrpCat.{w}]
  [∀ (F : Cᵒᵖ ⥤ AddCommGrpCat.{w}), G.op.HasLeftKanExtension F]
  [HasTerminal C] [HasTerminal D]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{w})]
  [hLa : (G.sheafPullback AddCommGrpCat.{w} J K).Additive]
  [hLl : PreservesFiniteLimits (G.sheafPullback AddCommGrpCat.{w} J K)]
  [hLc : PreservesFiniteColimits (G.sheafPullback AddCommGrpCat.{w} J K)]
  [hRa : (G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).Additive]
  [hRl : PreservesFiniteLimits (G.sheafPushforwardContinuous AddCommGrpCat.{w} J K)]
  [hRc : PreservesFiniteColimits (G.sheafPushforwardContinuous AddCommGrpCat.{w} J K)]
  [hInj : EnoughInjectives (Sheaf K AddCommGrpCat.{w})]

include hLa hLl hLc hRa hRl hRc hInj in
/-- **Cohomology transports along an exact pushforward**, in `Ext` form.

`Ext.precompAddEquiv` absorbs the isomorphism `G⁻¹ ℤ_J ≅ ℤ_K`; `extAdjunctionAddEquiv` does the
transport. The `Ext` spelling is the reusable one — a caller who wants to compose this with other
`Ext` machinery should not have to unfold `Sheaf.H` first. -/
noncomputable def sheafCohomologyPushforwardAddEquiv (hG : IsTerminal (G.obj (⊤_ C)))
    (F : Sheaf K AddCommGrpCat.{w}) (n : ℕ) :
    Ext.{w'} ((constantSheaf K AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) F n
      ≃+ Ext.{w'} ((constantSheaf J AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ)))
          ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj F) n :=
  (Ext.precompAddEquiv.{w'}
      ((constantSheafCompSheafPullbackIso G AddCommGrpCat.{w} hG).app
        (AddCommGrpCat.of (ULift.{w} ℤ))) F n).trans
    (extAdjunctionAddEquiv (G.sheafAdjunctionContinuous AddCommGrpCat.{w} J K) _ F n)

omit [HasGlobalSectionsFunctor K AddCommGrpCat.{w}] [HasTerminal D] hInj in
/-- Sheaf cohomology **is** that `Ext`, by definition of `Sheaf.H`. Recorded so a reader can see
that the two statements below are the same one, not a transport between them. -/
theorem sheafH_eq_ext (F : Sheaf K AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf.H F n
      = Ext.{w'} ((constantSheaf K AddCommGrpCat.{w}).obj (AddCommGrpCat.of (ULift.{w} ℤ))) F n :=
  rfl

include hLa hLl hLc hRa hRl hRc hInj in
/-- **`Hⁿ(K, F) ≃+ Hⁿ(J, G_* F)`.**

`#572` step 3's statement. The `HasExt` universe stays a parameter, as that issue asks, and the
`Sheaf.H` spelling costs nothing over the `Ext` one — see the module docstring, which records why
an earlier pass believed otherwise. -/
noncomputable def sheafHPushforwardAddEquiv (hG : IsTerminal (G.obj (⊤_ C)))
    (F : Sheaf K AddCommGrpCat.{w}) (n : ℕ) :
    Sheaf.H F n ≃+ Sheaf.H ((G.sheafPushforwardContinuous AddCommGrpCat.{w} J K).obj F) n :=
  sheafCohomologyPushforwardAddEquiv G hG F n

end CategoryTheory
