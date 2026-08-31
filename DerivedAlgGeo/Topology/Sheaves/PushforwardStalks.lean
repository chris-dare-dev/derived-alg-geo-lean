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
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Topology.Sheaves.Functors
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Topology.Sheaves.Abelian

/-!
# Stalks of a pushforward off a closed range

`subsingleton_stalk_pushforward` — for `f : X ⟶ Y` with closed range and `y ∉ Set.range f`, the
stalk `(f _* F) y` of the pushforward of a sheaf of abelian groups is a subsingleton.

## Where this sits

Exactness of `ι_*` along a closed immersion is the last input `#572` step 3 needs in order to be
instantiated geometrically (`CategoryTheory/Sites/Sheaves/CohomologyPushforward.lean` proves the
abstract
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
* `stalkPushforward_naturality` — naturality in the presheaf, which Mathlib does not have.
* `surjective_stalk_map_pushforward` and `isLocallySurjective_pushforward` — the two stalk facts
  assembled: pushforward along a closed embedding preserves local surjectivity, hence (with
  `isLocallySurjective_iff_epi`) epimorphisms.
* `preservesEpimorphisms_pushforward` — that, as a statement about the sheaf-level functor, which
  is the same functor the site-level `#572` machinery quantifies over.
* `preservesFiniteColimits_pushforward` — hence exactness, with limits free from the adjunction.
* `additive_pushforward`, `opensMap_obj_top` — the two small pieces the instantiation also needs.
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

/-! ## Naturality of `stalkPushforward` -/

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- **`stalkPushforward` is natural in the presheaf.**

Mathlib has `stalkPushforward.id` and `stalkPushforward.comp` — naturality in the *space* — but
not this, naturality in the *presheaf*, which is what a stalkwise argument about a morphism of
sheaves needs.

**Both `set_option`s are load-bearing.** Without them `(pushforward C f).obj F` is a
`Presheaf C Y`, which is not *reducibly* the functor category `(Opens Y)ᵒᵖ ⥤ C`, and every rewrite
fails with an application type mismatch rather than a missing-pattern error. The pair is exactly
what Mathlib itself puts on `stalkPushforward.id` and `stalkPushforward.comp` two declarations
above the result this one sits beside; it is not a workaround invented here.

They also change how dot-notation resolves: under them `F.stalkPushforward` in *tactic* position
looks for `Functor.stalkPushforward` and fails, so a consumer must write
`TopCat.Presheaf.stalkPushforward` in full. The statement below still uses dot-notation because
the options apply to elaboration of the proof, not of the signature. -/
theorem stalkPushforward_naturality (F G : X.Presheaf AddCommGrpCat.{u}) (T : F ⟶ G) (x : X) :
    (stalkFunctor AddCommGrpCat.{u} (f x)).map ((Presheaf.pushforward _ f).map T) ≫
        G.stalkPushforward _ f x
      = F.stalkPushforward _ f x ≫ (stalkFunctor AddCommGrpCat.{u} x).map T := by
  refine stalk_hom_ext _ fun U hU => ?_
  rw [← Category.assoc, stalkFunctor_map_germ, Category.assoc, stalkPushforward_germ,
    ← Category.assoc, stalkPushforward_germ, stalkFunctor_map_germ]
  rfl

/-! ## Surjectivity on stalks, and local surjectivity -/

/-- **Pushforward along an inducing map is surjective on stalks**, given the vanishing off the
range.

Stated for presheaves, with the vanishing as a hypothesis rather than a sheaf condition: the two
cases want different things, and only the off-range one needs `G` to be a sheaf. The caller
supplies `hvan` from `subsingleton_stalk_pushforward`.

On the range this is `stalkPushforward_naturality` plus the fact that both `stalkPushforward`s are
isomorphisms; off it the target stalk is a subsingleton and there is nothing to check. -/
theorem surjective_stalk_map_pushforward (hemb : Topology.IsInducing f)
    (F G : X.Presheaf AddCommGrpCat.{u}) (T : F ⟶ G)
    (hT : ∀ x : X, Function.Surjective ((stalkFunctor AddCommGrpCat.{u} x).map T))
    (hvan : ∀ y : Y, y ∉ Set.range f → Subsingleton ((f _* G).stalk y)) (y : Y) :
    Function.Surjective
      ((stalkFunctor AddCommGrpCat.{u} y).map ((Presheaf.pushforward _ f).map T)) := by
  by_cases hy : y ∈ Set.range f
  · obtain ⟨x, rfl⟩ := hy
    haveI iF : IsIso (F.stalkPushforward AddCommGrpCat.{u} f x) :=
      stalkPushforward.stalkPushforward_iso_of_isInducing (C := AddCommGrpCat.{u}) (f := f) hemb F x
    haveI iG : IsIso (G.stalkPushforward AddCommGrpCat.{u} f x) :=
      stalkPushforward.stalkPushforward_iso_of_isInducing (C := AddCommGrpCat.{u}) (f := f) hemb G x
    have hnat := stalkPushforward_naturality f F G T x
    -- `iG` is passed to `inv` explicitly: instance search will not find it through the other
    -- spelling of `stalkPushforward`, and the resulting error names `IsIso`, not the spelling.
    have heq : (stalkFunctor AddCommGrpCat.{u} (f x)).map ((Presheaf.pushforward _ f).map T)
        = F.stalkPushforward AddCommGrpCat.{u} f x ≫ (stalkFunctor AddCommGrpCat.{u} x).map T
            ≫ @inv _ _ _ _ (G.stalkPushforward AddCommGrpCat.{u} f x) iG := by
      rw [← Category.assoc, ← hnat]
      simp
    have h1 : Function.Surjective (F.stalkPushforward AddCommGrpCat.{u} f x) :=
      (ConcreteCategory.bijective_of_isIso _).2
    have h3 : Function.Surjective (@inv _ _ _ _ (G.stalkPushforward AddCommGrpCat.{u} f x) iG) :=
      (ConcreteCategory.bijective_of_isIso _).2
    -- State the surjectivity in the COMPOSITE spelling and rewrite the hypothesis into the goal's,
    -- not the other way round. `rw [heq]` on the goal produces a term whose instance paths no
    -- longer match anything stated separately; rewriting backwards in a hypothesis does not.
    have hs : Function.Surjective
        ⇑(F.stalkPushforward AddCommGrpCat.{u} f x ≫ (stalkFunctor AddCommGrpCat.{u} x).map T
          ≫ @inv _ _ _ _ (G.stalkPushforward AddCommGrpCat.{u} f x) iG) :=
      h3.comp ((hT x).comp h1)
    rwa [← heq] at hs
  · have hsub := hvan y hy
    intro b
    exact ⟨0, hsub.elim _ _⟩

/-- **Pushforward along a closed embedding preserves local surjectivity.**

With `TopCat.Sheaf.isLocallySurjective_iff_epi` this is preservation of epimorphisms, which is the
half of exactness that `ι_*` does not get for free from being a right adjoint. -/
theorem isLocallySurjective_pushforward (hemb : Topology.IsInducing f)
    (hcl : IsClosed (Set.range f))
    (F G : TopCat.Sheaf AddCommGrpCat.{u} X) (T : F.1 ⟶ G.1)
    (hT : IsLocallySurjective T) :
    IsLocallySurjective ((Presheaf.pushforward _ f).map T) := by
  rw [locally_surjective_iff_surjective_on_stalks] at hT ⊢
  exact fun y => surjective_stalk_map_pushforward f hemb F.1 G.1 T hT
    (fun z hz => subsingleton_stalk_pushforward f G hcl z hz) y

/-! ## Preservation of epimorphisms -/

/-- **Pushforward along a closed embedding preserves epimorphisms.**

Together with `ι_*` being a right adjoint — hence left exact for free — this is exactness, and it
is the last mathematical input `#572` step 3 needs.

## The site bridge costs nothing, and that is worth stating

This is phrased about `TopCat.Sheaf.pushforward`, while `#572` step 3 quantifies over
`Functor.sheafPushforwardContinuous`. **They are the same functor by definition**:
`TopCat.Sheaf.pushforward C f` is *defined* as `(Opens.map f).sheafPushforwardContinuous _ _ _`,
and `Sheaf.pushforward_map` and `Sheaf.pushforward_obj_val` are both `rfl`. No comparison
isomorphism is needed anywhere, and none is built.

## The instances are all imports, not obligations

`TopCat.Sheaf.isLocallySurjective_iff_epi` asks for `Balanced` on both sheaf categories and
`ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization AddCommGrpCat`. Every one of them
exists; they arrive with `Sites.Abelian`, `Grp.Abelian`, `Grp.EpiMono` and
`ConcreteCategory.EpiMono`, and a missing import presents as a bare "failed to synthesize", which
reads exactly like a missing theorem. -/
theorem preservesEpimorphisms_pushforward (hemb : Topology.IsInducing f)
    (hcl : IsClosed (Set.range f)) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesEpimorphisms := by
  constructor
  intro F G T hepi
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi] at hepi ⊢
  exact isLocallySurjective_pushforward f hemb hcl F G T.1 hepi

/-! ## Exactness -/

/-- The sheaf pushforward is additive.

`Sheaf.pushforward_map` is `rfl`, so this is `rfl` on each pair of morphisms; it is stated because
instance search does not find it and `Functor.additive_of_preservesBinaryBiproducts` does not
apply without more setup than the fact deserves. -/
instance additive_pushforward :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive := by
  constructor
  intro F G a b
  rfl

/-- **Pushforward along a closed embedding is exact.**

Limits it preserves for free, being a right adjoint. For colimits: preserving zero morphisms,
epimorphisms and kernels gives `PreservesHomology`
(`Functor.preservesHomology_of_preservesEpis_and_kernels`), and that gives finite colimits. The
epimorphisms are `preservesEpimorphisms_pushforward`; the kernels come with the right adjoint.

This is the input `#572` step 3 needs in order to instantiate the abstract cohomology comparison
of `CategoryTheory/Sites/Sheaves/CohomologyPushforward.lean` at a closed immersion. -/
theorem preservesFiniteColimits_pushforward (hemb : Topology.IsInducing f)
    (hcl : IsClosed (Set.range f)) :
    PreservesFiniteColimits (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) := by
  haveI := preservesEpimorphisms_pushforward f hemb hcl
  haveI : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- `Opens.map` sends the whole space to the whole space.

Trivial, and recorded because the instantiation needs `IsTerminal ((Opens.map f).obj ⊤)` and
`IsTerminal.ofUnique` does *not* discharge it -- the `Unique` instance it wants is not there. -/
lemma opensMap_obj_top : (Opens.map f).obj ⊤ = ⊤ := rfl

end DerivedAlgGeo.Topology
