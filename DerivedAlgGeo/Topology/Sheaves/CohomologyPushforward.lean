/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Topology.Sheaves.PushforwardStalks
import DerivedAlgGeo.CategoryTheory.Sites.Sheaves.CohomologyPushforward
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Cohomology is unchanged by pushforward along a closed embedding

`cohomologyPushforwardAddEquiv` : `Hⁿ(X, F) ≃+ Hⁿ(Y, f_* F)` for `f` an inducing map with closed
range. This is `#572` step 3's statement, instantiated at an actual map of spaces.

## Everything here is plumbing

`CategoryTheory/Sites/Sheaves/CohomologyPushforward.lean` proves the comparison abstractly, for a continuous
functor of sites whose pullback and pushforward are both exact. This composition-layer file
discharges those hypotheses for `Opens.map f`. No mathematics happens: the one non-formal input,
exactness of `f_*`, is `PushforwardStalks.lean`, and the rest is instance supply.

That was not obvious in advance and it is worth recording why. Three separate estimates of this
step were wrong, each in the same direction:

* **the site bridge is `rfl`.** `TopCat.Sheaf.pushforward C f` is *defined* as
  `(Opens.map f).sheafPushforwardContinuous _ _ _`, so the topological and site-level functors are
  the same term. Nothing is transported.
* **`EnoughInjectives` and `HasExt` are imports, not theorems.** Both follow from
  `IsGrothendieckAbelian`, which holds for `Sheaf D X` once `Topology.Sheaves.Abelian` and
  `Grp.AB` are in scope. A missing import here presents as a bare "failed to synthesize", which is
  indistinguishable from a missing result.
* **`HasGlobalSectionsFunctor` and the left Kan extension** are already instances for `Opens.map`.

## What must be supplied by hand, and why

Four instances that exist but that search will not find or cannot afford:

* `PreservesFiniteLimits` of the pullback. The instance is
  `Functor.sheafPullbackConstruction.preservesFiniteLimits`; searching for it instead runs `whnf`
  past 200000 heartbeats, the same non-termination `CoherentSheaf/Pushforward/BaseChange.lean`
  records for unification through site functors. **Name it.**
* `Additive` of the pushforward — `rfl` per morphism, but not found.
* `Additive` of the pullback — from the pushforward's, through `Adjunction.left_adjoint_additive`.
* `IsLeftAdjoint`/`IsRightAdjoint` of the two, to get the remaining exactness halves.

## `⊤_` is not `⊤`

The abstract theorem wants `IsTerminal ((Opens.map f).obj (⊤_ (Opens Y)))`. `Opens.map` sends `⊤`
to `⊤` by `rfl`, but the *categorical* terminal `⊤_ (Opens Y)` is not syntactically the lattice
`⊤`; `terminal_opens_eq_top` is the one-line antisymmetry that identifies them, and
`IsTerminal.ofUnique` does not discharge the goal without it.

## Scope

Spaces, not schemes. A closed immersion of schemes induces a closed embedding of underlying
spaces, so this applies to one — but that final step is not taken here, and `#572`'s acceptance
criterion is phrased about schemes.

## Main results

* `cohomologyPushforwardAddEquivAt` — the comparison, at a chosen `HasExt` witness.
* `cohomologyPushforwardAddEquivAt_naturality` — it is natural in the sheaf.
* `cohomologyPushforwardAddEquiv` — the same at the witness instance search finds.
-/

universe w' u

open CategoryTheory Limits TopologicalSpace TopCat
open DerivedAlgGeo.Topology

namespace DerivedAlgGeo.Topology

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- `⊤` is terminal in `Opens`: morphisms are proofs of `≤`, so `le_top` is the unique one. -/
noncomputable def isTerminalTopOpens : IsTerminal (⊤ : Opens X) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => rfl)

/-- The categorical terminal of `Opens` is the lattice `⊤`. Needed because the two are not
syntactically equal and the abstract theorem asks about the former. -/
lemma terminal_opens_eq_top : (⊤_ (Opens Y)) = ⊤ :=
  le_antisymm le_top (leOfHom (terminalIsTerminal.from ⊤))

/-- `Opens.map f` carries the categorical terminal open of `Y` to a terminal open of `X`: it sends
`⊤` to `⊤`. Named, because it is data that the comparison and its naturality statement have to
share. -/
noncomputable def isTerminalOpensMapTerminal :
    IsTerminal ((Opens.map f).obj (⊤_ (Opens Y))) := by
  rw [terminal_opens_eq_top, opensMap_obj_top]
  exact isTerminalTopOpens

set_option maxHeartbeats 1000000 in
/-- **Cohomology is unchanged by pushforward along a closed embedding, at a chosen `HasExt`
witness.**

`#572` step 3, at a map of spaces. Every hypothesis of the abstract comparison is discharged here;
the only one that is not an instance or an import is exactness of `f_*`, which is
`preservesFiniteColimits_pushforward`.

The `HasExt` witnesses are positional, as in the Čech lane: `Sheaf.H` lands in the `HasExt`
universe, and a caller whose groups are named at `HasExt.standard` (the coherent-cohomology
convention, `HasExt.{u + 1}`) cannot let instance search pick the Grothendieck-category
`HasExt.{u}`, which names different groups. -/
noncomputable def cohomologyPushforwardAddEquivAt (hemb : Topology.IsInducing f)
    (hcl : IsClosed (Set.range f))
    (hX : HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hY : HasExt.{w'} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    @Sheaf.H _ _ _ F _ hX n ≃+ @Sheaf.H _ _ _ (((Opens.map f).sheafPushforwardContinuous
        AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj F)
        _ hY n :=
  letI := hX
  letI := hY
  haveI hRa : ((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive :=
    additive_pushforward f
  haveI hRc : PreservesFiniteColimits ((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
    preservesFiniteColimits_pushforward f hemb hcl
  haveI hRadj : ((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).IsRightAdjoint :=
    ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).isRightAdjoint
  haveI hLl : PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
    CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  haveI hLa : ((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive :=
    ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).left_adjoint_additive
  haveI hLadj : ((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).IsLeftAdjoint :=
    ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).isLeftAdjoint
  sheafHPushforwardAddEquiv (Opens.map f) (isTerminalOpensMapTerminal f) F n

set_option maxHeartbeats 1000000 in
/-- **The comparison is natural in the sheaf.** The abstract naturality
`sheafHPushforwardAddEquiv_naturality`, at the same instances and the same terminal witness. -/
theorem cohomologyPushforwardAddEquivAt_naturality (hemb : Topology.IsInducing f)
    (hcl : IsClosed (Set.range f))
    (hX : HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hY : HasExt.{w'} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}))
    {F F' : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (φ : F ⟶ F') (n : ℕ)
    (x : @Sheaf.H _ _ _ F _ hX n) :
    cohomologyPushforwardAddEquivAt f hemb hcl hX hY F' n
        (@Sheaf.H.map _ _ (Opens.grothendieckTopology X) _ hX _ _ φ n x)
      = @Sheaf.H.map _ _ (Opens.grothendieckTopology Y) _ hY _ _
          (((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
            (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map φ) n
          (cohomologyPushforwardAddEquivAt f hemb hcl hX hY F n x) := by
  letI := hX
  letI := hY
  haveI hRa : ((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive :=
    additive_pushforward f
  haveI hRc : PreservesFiniteColimits ((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
    preservesFiniteColimits_pushforward f hemb hcl
  haveI hRadj : ((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).IsRightAdjoint :=
    ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).isRightAdjoint
  haveI hLl : PreservesFiniteLimits ((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)) :=
    CategoryTheory.Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _
  haveI hLa : ((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).Additive :=
    ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).left_adjoint_additive
  haveI hLadj : ((Opens.map f).sheafPullback AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).IsLeftAdjoint :=
    ((Opens.map f).sheafAdjunctionContinuous AddCommGrpCat.{u} _ _).isLeftAdjoint
  exact sheafHPushforwardAddEquiv_naturality (Opens.map f) (isTerminalOpensMapTerminal f) φ n x

/-- **Cohomology is unchanged by pushforward along a closed embedding**, at the `HasExt` witness
instance search finds. -/
noncomputable def cohomologyPushforwardAddEquiv (hemb : Topology.IsInducing f)
    (hcl : IsClosed (Set.range f))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H F n ≃+ Sheaf.H (((Opens.map f).sheafPushforwardContinuous AddCommGrpCat.{u}
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj F) n :=
  cohomologyPushforwardAddEquivAt f hemb hcl inferInstance inferInstance F n

end DerivedAlgGeo.Topology
