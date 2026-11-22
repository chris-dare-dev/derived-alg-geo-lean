/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import DerivedAlgGeo.CategoryTheory.Sites.Descent.ModOver
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.ObjectProperty

/-!
# Torsors on a site, and the stack of torsors

Let `G` be a sheaf of groups on a site `(C, J)`, a group object of `Sheaf J (Type w)`. A
`G`-torsor is a sheaf `P` with an action of `G` that is simply transitive on sections and locally
nonempty ([Stacks, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)). This file defines the
torsor condition on Mathlib's module objects, and the stack in groupoids of torsors over the slices
of the site. [Stacks, Tag 04UK](https://stacks.math.columbia.edu/tag/04UK) proves that torsors
form a stack for a sheaf of groups on the big fppf site of a scheme; the proof here follows it on
any site.

## Main definitions

* `Sheaf.IsTorsor G P`: the morphism `ModObj.leftSMul G P`, `(g, p) ↦ (g • p, p)`, is an
  isomorphism and the map of `P` to the terminal sheaf is locally surjective.
* `Sheaf.torsorProperty G`: the torsor condition on the objects of the pseudofunctor of
  `G`-objects `J.pseudofunctorModOver G`.
* `torsorStack G`: the stack in groupoids of torsors under the restrictions of `G` to the slices.

## Main results

* `Sheaf.isTorsor_iff`: the characterization of
  [Stacks, Tag 0499](https://stacks.math.columbia.edu/tag/0499) through
  `ModObj.isIso_leftSMul_iff`, the action being simply transitive on morphisms from every sheaf.
* `Sheaf.isIso_leftSMul_iff_sections` and `Sheaf.isLocallySurjective_toUnit_iff`: the two
  conjuncts of `Sheaf.IsTorsor` are conditions (1) and (2) of Tag 03AH.
* `Sheaf.isTorsor_iff_epi`: when sheafification exists, local nonemptiness is the condition that
  the map to the terminal sheaf is an epimorphism.
* `Sheaf.isTorsor_regular`: the trivial torsor, `G` acting on itself by left multiplication.
* `Sheaf.IsTorsor.overMapPullback`: torsors restrict to torsors along `Over.map`.
* `Sheaf.isLocal_torsorProperty`: being a torsor is local for `J`.

## Implementation notes

Torsors are a property of Mathlib's `ModObj` objects, not a new structure, so `torsorStack G` is
the moduli of objects `StackInGroupoids.ofObjectProperty` of the stack of `G`-objects cut out by
`Sheaf.torsorProperty G`. Its stack condition is proved, from that of sheaves of types on the
slices, which holds when every covering sieve contains a `w`-small covering family
(`GrothendieckTopology.isStack_pseudofunctorOver`).

The local-nonemptiness conjunct is stated as local surjectivity of the map to the terminal sheaf,
which is condition (2) of Tag 03AH. It implies that this map is an epimorphism
(`Sheaf.IsTorsor.epi_toUnit`); the converse uses sheafification in `Type w`, which need not exist
on a large site, and holds under `HasSheafify J (Type w)` (`Sheaf.isTorsor_iff_epi`). The
conjunct is not redundant: the empty sheaf with its unique action satisfies the first one.

The definitions only need a monoid object `G`; the trivial torsor needs a group object, and for
a sheaf of groups the conditions are those of Tag 03AH.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH), Definition 21.4.1.
* [Stacks Project, Tag 0499](https://stacks.math.columbia.edu/tag/0499), Lemma 39.11.2.
* [Stacks Project, Tag 04UK](https://stacks.math.columbia.edu/tag/04UK), Lemma 95.14.2, for a sheaf
  of groups on the big fppf site of a scheme.

## Tags

torsor, principal homogeneous sheaf, stack, descent
-/

universe w v u

namespace CategoryTheory

open Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Obj MonObj

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

section Torsor

/-- A sheaf `P` with an action of a sheaf of monoids `G` is a `G`-torsor
([Stacks, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)) when
1. the morphism `(g, p) ↦ (g • p, p)` of `G ⊗ P` to `P ⊗ P`, Mathlib's `ModObj.leftSMul`, is an
   isomorphism, that is `G(U)` acts simply transitively on `P(U)` for every `U`
   (`Sheaf.isIso_leftSMul_iff_sections`), and
2. `P` is locally nonempty: every object has a covering sieve on whose members `P` has a section
   (`Sheaf.isLocallySurjective_toUnit_iff`).

For a sheaf of groups these are conditions (1) and (2) of Tag 03AH. -/
def IsTorsor (G P : Sheaf J (Type w)) [MonObj G] [ModObj G P] : Prop :=
  IsIso (ModObj.leftSMul G P) ∧ IsLocallySurjective (toUnit P)

variable (G P : Sheaf J (Type w)) [MonObj G] [ModObj G P]

/-- A sheaf with an action of `G` is a `G`-torsor exactly when the action is simply transitive on
morphisms from every sheaf and it is locally nonempty
([Stacks, Tag 0499](https://stacks.math.columbia.edu/tag/0499)). -/
theorem isTorsor_iff :
    IsTorsor G P ↔ (∀ (Z : Sheaf J (Type w)) (x y : Z ⟶ P), ∃! m : Z ⟶ G, m • x = y) ∧
      IsLocallySurjective (toUnit P) :=
  and_congr_left' ModObj.isIso_leftSMul_iff

/-- The map `(g, p) ↦ (g • p, p)` on sections. -/
lemma leftSMul_hom_app_apply (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.obj.obj U) :
    (ModObj.leftSMul G P).hom.app U (g, p) = (γ[G, P].hom.app U (g, p), p) :=
  rfl

/-- A function `(g, p) ↦ (φ (g, p), p)` is bijective exactly when every `φ (-, p)` is. -/
private lemma bijective_iff_existsUnique {A B : Type*} (φ : A × B → B) :
    Function.Bijective (fun z : A × B ↦ (φ z, z.2)) ↔ ∀ x y : B, ∃! a : A, φ (a, x) = y := by
  constructor
  · rintro ⟨hi, hs⟩ x y
    obtain ⟨⟨a, x'⟩, h⟩ := hs (y, x)
    simp only [Prod.mk.injEq] at h
    obtain ⟨h₁, rfl⟩ := h
    refine ⟨a, h₁, fun a' ha' ↦ ?_⟩
    have := @hi (a', x') (a, x') (by simp [ha', h₁])
    simpa using this
  · intro h
    refine ⟨fun ⟨a, x⟩ ⟨a', x'⟩ e ↦ ?_, fun ⟨y, x⟩ ↦ ?_⟩
    · simp only [Prod.mk.injEq] at e
      obtain ⟨e₁, rfl⟩ := e
      obtain ⟨b, -, hb⟩ := h x (φ (a, x))
      rw [hb a rfl, hb a' e₁.symm]
    · obtain ⟨a, ha, -⟩ := h x y
      exact ⟨(a, x), by simp [ha]⟩

/-- Condition (1) of [Stacks, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH): the morphism
`(g, p) ↦ (g • p, p)` is an isomorphism exactly when `G(U)` acts simply transitively on `P(U)`
for every `U`. -/
theorem isIso_leftSMul_iff_sections :
    IsIso (ModObj.leftSMul G P) ↔
      ∀ (U : Cᵒᵖ) (x y : P.obj.obj U), ∃! g : G.obj.obj U, γ[G, P].hom.app U (g, x) = y := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J (Type w)), NatTrans.isIso_iff_isIso_app]
  refine forall_congr' fun U ↦ ?_
  rw [isIso_iff_bijective]
  exact bijective_iff_existsUnique (fun z ↦ γ[G, P].hom.app U z)

/-- Condition (2) of [Stacks, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH): the map of
`P` to the terminal sheaf is locally surjective exactly when every object has a covering sieve
on whose members `P` has a section. -/
theorem isLocallySurjective_toUnit_iff :
    IsLocallySurjective (toUnit P) ↔
      ∀ U : C, ∃ R ∈ J U, ∀ ⦃V : C⦄ (g : V ⟶ U), R g → Nonempty (P.obj.obj (op V)) := by
  constructor
  · intro h U
    exact ⟨_, Presheaf.imageSieve_mem J (toUnit P).hom (PUnit.unit : PUnit.{w + 1}),
      fun V g ⟨t, _⟩ ↦ ⟨t⟩⟩
  · intro h
    refine ⟨fun {U} s ↦ ?_⟩
    obtain ⟨R, hR, hP⟩ := h U
    refine J.superset_covering (fun V g hg ↦ ?_) hR
    obtain ⟨t⟩ := hP g hg
    exact ⟨t, rfl⟩

variable {G P}

theorem IsTorsor.isIso_leftSMul (h : IsTorsor G P) : IsIso (ModObj.leftSMul G P) :=
  h.1

theorem IsTorsor.isLocallySurjective_toUnit (h : IsTorsor G P) :
    IsLocallySurjective (toUnit P) :=
  h.2

/-- A torsor is locally nonempty, so its map to the terminal sheaf is an epimorphism. -/
theorem IsTorsor.epi_toUnit (h : IsTorsor G P) : Epi (toUnit P) :=
  have := h.2
  inferInstance

/-- When sheafification of sheaves of types exists, local nonemptiness of `P` is the condition
that its map to the terminal sheaf is an epimorphism. -/
theorem isTorsor_iff_epi [HasSheafify J (Type w)] :
    IsTorsor G P ↔ IsIso (ModObj.leftSMul G P) ∧ Epi (toUnit P) :=
  and_congr_right' (isLocallySurjective_iff_epi _)

/-- A sheaf with a monoid structure has a global section, its unit, so it is locally
nonempty. -/
theorem isLocallySurjective_toUnit_of_monObj (M : Sheaf J (Type w)) [MonObj M] :
    IsLocallySurjective (toUnit M) :=
  Presheaf.isLocallySurjective_of_surjective J _ fun U _ ↦
    ⟨η[M].hom.app U (PUnit.unit : PUnit.{w + 1}), rfl⟩

/-- The trivial torsor: a sheaf of groups acting on itself by left multiplication
(`ModObj.regular`) is a torsor. -/
theorem isTorsor_regular (G : Sheaf J (Type w)) [GrpObj G] :
    letI := ModObj.regular G
    IsTorsor G G := by
  let _ := ModObj.regular G
  refine ⟨ModObj.isIso_leftSMul_iff.2 fun Z x y ↦ ⟨y * x⁻¹, ?_, fun m hm ↦ ?_⟩,
    isLocallySurjective_toUnit_of_monObj G⟩
  · change (y * x⁻¹) * x = y
    exact inv_mul_cancel_right y x
  · change m * x = y at hm
    rw [← hm, mul_inv_cancel_right]

/-- Torsors are preserved by an isomorphism of `G`-objects. -/
theorem IsTorsor.of_iso {Q : Sheaf J (Type w)} [ModObj G Q] (e : P ≅ Q) [IsModHom G e.hom]
    (h : IsTorsor G P) : IsTorsor G Q := by
  refine ⟨(isIso_leftSMul_iff_sections G Q).2 fun U x y ↦ ?_, ?_⟩
  · have app {A B : Sheaf J (Type w)} {φ ψ : A ⟶ B} (hφ : φ = ψ) (a : A.obj.obj U) :
        φ.hom.app U a = ψ.hom.app U a := by
      rw [hφ]
    have key (g : G.obj.obj U) (p : P.obj.obj U) :
        e.hom.hom.app U (γ[G, P].hom.app U (g, p)) = γ[G, Q].hom.app U (g, e.hom.hom.app U p) :=
      app (IsModHom.smul_hom (A := G) (f := e.hom)) (g, p)
    have hinv (q : Q.obj.obj U) : e.hom.hom.app U (e.inv.hom.app U q) = q :=
      app e.inv_hom_id q
    have hinj : Function.Injective (e.hom.hom.app U) := fun p p' hp ↦ by
      have h₁ : e.inv.hom.app U (e.hom.hom.app U p) = p := app e.hom_inv_id p
      have h₂ : e.inv.hom.app U (e.hom.hom.app U p') = p' := app e.hom_inv_id p'
      rw [← h₁, ← h₂, hp]
    obtain ⟨g, hg, hu⟩ :=
      (isIso_leftSMul_iff_sections G P).1 h.1 U (e.inv.hom.app U x) (e.inv.hom.app U y)
    refine ⟨g, ?_, fun g' hg' ↦ hu g' (hinj ?_)⟩
    · have := key g (e.inv.hom.app U x)
      rw [hg, hinv, hinv] at this
      exact this.symm
    · beta_reduce at hg' ⊢
      rw [key, hinv, hinv]
      exact hg'
  · have := h.2
    rw [toUnit_unique (toUnit Q) (e.inv ≫ toUnit P)]
    infer_instance

end Torsor

section Restriction

variable {G : Sheaf J (Type w)} [MonObj G]

/-- Torsors restrict to torsors along `Over.map f`. -/
theorem IsTorsor.overMapPullback {X Y : C} (f : X ⟶ Y) {P : Sheaf (J.over Y) (Type w)}
    [ModObj ((J.overPullback (Type w) Y).obj G) P]
    (h : IsTorsor ((J.overPullback (Type w) Y).obj G) P) :
    IsTorsor ((J.overPullback (Type w) X).obj G) ((J.overMapPullback (Type w) f).obj P) := by
  have := h.1
  have := h.2
  exact ⟨(inferInstance : IsIso ((J.overMapPullback (Type w) f).map
      (ModObj.leftSMul ((J.overPullback (Type w) Y).obj G) P))),
    Presheaf.isLocallySurjective_whisker (J.over X) (J.over Y) (Over.map f) (toUnit P).hom⟩

end Restriction

section Local

/-- A morphism of sheaves on `Over S` whose restrictions along the arrows of a covering sieve are
isomorphisms is an isomorphism: the restrictions form an isomorphism of descent data, and
restriction to descent data is fully faithful. -/
private lemma isIso_of_isIso_overMapPullback_map {S : C} {A B : Sheaf (J.over S) (Type w)}
    (φ : A ⟶ B) (R : Sieve S) (hR : R ∈ J S)
    (h : ∀ ⦃T : C⦄ (g : T ⟶ S), R g → IsIso ((J.overMapPullback (Type w) g).map φ)) :
    IsIso φ := by
  let f := fun (a : R.arrows.category) ↦ a.obj.hom
  have hF := ((J.pseudofunctorOver (Type w)).isPrestackFor' R hR).fullyFaithful
  have : IsIso (((J.pseudofunctorOver (Type w)).toDescentData f).map φ) := by
    let e := Pseudofunctor.DescentData.isoMk
      (D₁ := ((J.pseudofunctorOver (Type w)).toDescentData f).obj A)
      (D₂ := ((J.pseudofunctorOver (Type w)).toDescentData f).obj B)
      (fun i ↦ @asIso _ _ _ _ ((J.overMapPullback (Type w) i.obj.hom).map φ)
        (h i.obj.hom i.property))
      (fun _ q _ _ f₁ f₂ hf₁ hf₂ ↦
        (((J.pseudofunctorOver (Type w)).toDescentData f).map φ).comm q f₁ f₂ hf₁ hf₂)
    exact (inferInstance : IsIso e.hom)
  exact hF.isIso_of_isIso_map φ

/-- A sheaf on `Over S` whose restrictions along the arrows of a covering sieve are locally
nonempty is locally nonempty. -/
private lemma isLocallySurjective_toUnit_of_sieve {S : C} (P : Sheaf (J.over S) (Type w))
    (R : Sieve S) (hR : R ∈ J S)
    (h : ∀ ⦃T : C⦄ (g : T ⟶ S), R g →
      IsLocallySurjective (toUnit ((J.overMapPullback (Type w) g).obj P))) :
    IsLocallySurjective (toUnit P) := by
  rw [isLocallySurjective_toUnit_iff]
  intro U
  let T : Sieve U.left :=
    { arrows := fun _ d ↦ Nonempty (P.obj.obj (op (Over.mk (d ≫ U.hom))))
      downward_closed := fun {_ _} d ⟨p⟩ e ↦
        ⟨P.obj.map (Over.homMk e (by simp) :
          Over.mk ((e ≫ d) ≫ U.hom) ⟶ Over.mk (d ≫ U.hom)).op p⟩ }
  refine ⟨(Sieve.overEquiv U).symm T, ?_, fun W k hk ↦ ?_⟩
  · rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
    refine J.transitive (J.pullback_stable U.hom hR) T fun Z c hc ↦ ?_
    have hg := h (c ≫ U.hom) hc
    rw [isLocallySurjective_toUnit_iff] at hg
    obtain ⟨R', hR', hP'⟩ := hg (Over.mk (𝟙 Z))
    rw [GrothendieckTopology.mem_over_iff] at hR'
    refine J.superset_covering (fun W e he ↦ ?_) hR'
    rw [Sieve.overEquiv_iff] at he
    obtain ⟨p⟩ := hP' _ he
    exact ⟨P.obj.map (Over.homMk (𝟙 W) (by simp) :
      Over.mk ((e ≫ c) ≫ U.hom) ⟶ Over.mk ((e ≫ 𝟙 Z) ≫ c ≫ U.hom)).op p⟩
  · obtain ⟨p⟩ := hk
    exact ⟨P.obj.map (Over.homMk (𝟙 W.left) (by simp [Over.w k]) :
      W ⟶ Over.mk (k.left ≫ U.hom)).op p⟩

variable (G : Sheaf J (Type w)) [MonObj G]

/-- Being a torsor, as a property of the objects of the pseudofunctor of `G`-objects. -/
def torsorProperty : (J.pseudofunctorModOver G).ObjectProperty where
  prop X := fun (P : Mod (Sheaf (J.over X.as.unop) (Type w))
    ((J.overPullback (Type w) X.as.unop).obj G)) ↦
      IsTorsor ((J.overPullback (Type w) X.as.unop).obj G) P.X

private lemma isTorsor_modOverMap_obj {X Y : C} (f : X ⟶ Y)
    (P : Mod (Sheaf (J.over Y) (Type w)) ((J.overPullback (Type w) Y).obj G))
    (hP : IsTorsor ((J.overPullback (Type w) Y).obj G) P.X) :
    IsTorsor ((J.overPullback (Type w) X).obj G) ((GrothendieckTopology.modOverMap G f).obj P).X :=
  IsTorsor.overMapPullback f hP

private lemma isTorsor_of_modIso {X : C}
    {P Q : Mod (Sheaf (J.over X) (Type w)) ((J.overPullback (Type w) X).obj G)} (e : P ≅ Q)
    (hP : IsTorsor ((J.overPullback (Type w) X).obj G) P.X) :
    IsTorsor ((J.overPullback (Type w) X).obj G) Q.X :=
  let e' : P.X ≅ Q.X :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg Mod.Hom.hom e.hom_inv_id
      inv_hom_id := congrArg Mod.Hom.hom e.inv_hom_id }
  haveI : IsModHom ((J.overPullback (Type w) X).obj G) e'.hom := e.hom.isModHom
  IsTorsor.of_iso e' hP

/-- Being a torsor is local: it is preserved by restriction, and it holds when it holds after
restriction along the arrows of a covering sieve. -/
instance isLocal_torsorProperty : (torsorProperty G).IsLocal J where
  map_obj hP f := isTorsor_modOverMap_obj G f.as.unop _ hP
  of_sieve _ R hR h :=
    ⟨isIso_of_isIso_overMapPullback_map _ R hR fun _ g hg ↦ (h g hg).1,
      isLocallySurjective_toUnit_of_sieve _ R hR fun _ g hg ↦ (h g hg).2⟩

instance isClosedUnderIsomorphisms_torsorProperty :
    (torsorProperty G).IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms _ := ⟨fun e hP ↦ isTorsor_of_modIso G e hP⟩

end Local

end Sheaf

/-- The stack in groupoids of `G`-torsors over the slices of a site: over `X` its fibre is the
groupoid of torsors under the restriction of `G` to `Over X` and their equivariant isomorphisms.
For a sheaf of groups on the big fppf site of a scheme this is the stack of
[Stacks, Tag 04UK](https://stacks.math.columbia.edu/tag/04UK).

It is the moduli of objects `StackInGroupoids.ofObjectProperty` of the stack of `G`-objects,
cut out by the local property `Sheaf.IsTorsor`; its stack condition is proved from that of
sheaves of types on the slices, which holds when every covering sieve contains a `w`-small
covering family (`GrothendieckTopology.isStack_pseudofunctorOver`). -/
def torsorStack (G : Sheaf J (Type w)) [MonObj G] [(J.pseudofunctorOver (Type w)).IsStack J] :
    StackInGroupoids C J :=
  StackInGroupoids.ofObjectProperty (J.pseudofunctorModOver G) (Sheaf.torsorProperty G)

end CategoryTheory
