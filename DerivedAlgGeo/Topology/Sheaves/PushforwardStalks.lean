/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Stalks of a pushforward off a closed range

`subsingleton_stalk_pushforward` — for `f : X ⟶ Y` with closed range and `y ∉ Set.range f`, the
stalk `(f _* F) y` of the pushforward of a sheaf of abelian groups is a subsingleton.

## Where this sits

Exactness of `ι_*` along a closed immersion is the last input `#572` step 3 needs in order to be
instantiated geometrically (`CategoryTheory/SheafCohomologyPushforward.lean` proves the abstract
statement). The standard proof is stalkwise, and it has two halves:

* **on the range**, `(f _* F)_{f x} ≅ F_x`. This is **already in Mathlib**, as
  `TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing`, and it needs only
  `IsInducing f` — *not* closedness. That matches the geometry: for any embedding, the opens of
  `X` around `x` are exactly the preimages of opens of `Y` around `f x`;
* **off the range**, the stalk vanishes. That is this file, and it is where closedness is spent.

## The proof, and why closedness is the whole of it

`Set.range f` closed makes its complement an open `offRange` containing every `y` outside the
range, and every open `U ≤ offRange` pulls back to `⊥`. So `(f _* F)(U) = F(⊥)`, which is terminal
for a *sheaf* — `TopCat.Sheaf.isTerminalOfEmpty` — hence a subsingleton in `AddCommGrpCat`.

`exists_le_germ_eq` is what makes this an argument about one open rather than a cofinality
computation: it produces, for any element of the stalk, a representing section over an open
**inside a neighbourhood of one's choosing**. Choose `offRange`, and every germ is a germ of a
section of a terminal object. Two such germs agree because both equal the germ of `0` over
`offRange` itself, via `germ_res_apply`.

## Scope

This says nothing about exactness yet. It is one of the two stalk computations that a stalkwise
exactness proof consumes, and the other one is Mathlib's. Bridging from the topological `f _*` to
the site-level `Functor.sheafPushforwardContinuous` that `#572` step 3 actually quantifies over is
further work again, and is not begun here.

## Main results

* `offRange` and `preimage_eq_bot_of_le` — the open, and that it pulls back to nothing.
* `subsingleton_of_isTerminal` — terminal objects of `AddCommGrpCat` have subsingleton carriers.
* `subsingleton_stalk_pushforward` — the vanishing.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat TopCat.Presheaf AlgebraicGeometry

namespace DerivedAlgGeo.Topology

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The complement of a closed range, as an open of the target. -/
def offRange (hcl : IsClosed (Set.range f)) : Opens Y :=
  ⟨(Set.range f)ᶜ, hcl.isOpen_compl⟩

/-- Anything inside the complement of the range pulls back to the empty open. -/
lemma preimage_eq_bot_of_le (hcl : IsClosed (Set.range f)) {U : Opens Y}
    (hU : U ≤ offRange f hcl) : (Opens.map f).obj U = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : f x ∈ offRange f hcl := hU hx
  simp [offRange] at this

/-- A terminal object of `AddCommGrpCat` has a subsingleton carrier.

Stated separately because the route is not the obvious one: there is no `IsTerminal.isZero` to
hand, so this goes through `uniqueUpToIso` against the zero object and then
`AddCommGrpCat.subsingleton_of_isZero`. -/
lemma subsingleton_of_isTerminal {A : AddCommGrpCat.{u}} (h : IsTerminal A) : Subsingleton A := by
  have hz : IsZero A := IsZero.of_iso (isZero_zero AddCommGrpCat.{u})
    (h.uniqueUpToIso ((isZero_zero AddCommGrpCat.{u}).isTerminal))
  exact AddCommGrpCat.subsingleton_of_isZero hz

/-- **Off a closed range, the pushforward of a sheaf has no stalk.**

The companion of Mathlib's `stalkPushforward_iso_of_isInducing`, which handles the range itself and
needs only `IsInducing`. Closedness is spent here and nowhere else. -/
theorem subsingleton_stalk_pushforward (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hcl : IsClosed (Set.range f)) (y : Y) (hy : y ∉ Set.range f) :
    Subsingleton ((f _* F.1).stalk y) := by
  have hyV : y ∈ offRange f hcl := hy
  have hsub : ∀ {U : Opens Y}, U ≤ offRange f hcl →
      Subsingleton ((f _* F.1).obj (op U)) := by
    intro U hU
    have hb : (Opens.map f).obj U = ⊥ := preimage_eq_bot_of_le f hcl hU
    show Subsingleton (F.1.obj (op ((Opens.map f).obj U)))
    rw [hb]
    exact subsingleton_of_isTerminal F.isTerminalOfEmpty
  refine ⟨fun s t => ?_⟩
  obtain ⟨U, hUV, hyU, sU, rfl⟩ := exists_le_germ_eq (f _* F.1) s hyV
  obtain ⟨W, hWV, hyW, sW, rfl⟩ := exists_le_germ_eq (f _* F.1) t hyV
  haveI := hsub (le_refl (offRange f hcl))
  haveI := hsub hUV
  haveI := hsub hWV
  have e1 : (f _* F.1).germ U y hyU sU
      = (f _* F.1).germ (offRange f hcl) y hyV 0 := by
    rw [← germ_res_apply (f _* F.1) (homOfLE hUV) y hyU 0]
    congr 1
    exact Subsingleton.elim _ _
  have e2 : (f _* F.1).germ W y hyW sW
      = (f _* F.1).germ (offRange f hcl) y hyV 0 := by
    rw [← germ_res_apply (f _* F.1) (homOfLE hWV) y hyW 0]
    congr 1
    exact Subsingleton.elim _ _
  rw [e1, e2]

end DerivedAlgGeo.Topology
