/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.CoversTop.Over
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Detecting local equivalences on a covering family

Local injectivity and local surjectivity of a morphism of additive presheaves can be checked
after restriction to a family covering the terminal object. Consequently, when the weak
equivalences of a site are the locally bijective morphisms, membership in the class inverted by
sheafification can be checked on such a family.

These statements use only a Grothendieck topology and additive presheaves. Scheme charts and
module-sheaf tensor products are downstream consumers.
-/

open CategoryTheory Limits

universe u u₁ v₁

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- Local injectivity is detected on a family covering the terminal object. -/
lemma isLocallyInjective_of_coversTop {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    {ι : Type*} (X : ι → C) (hX : J.CoversTop X)
    (h : ∀ i, IsLocallyInjective (J.over (X i))
      (Functor.whiskerLeft (Over.forget (X i)).op f)) :
    IsLocallyInjective J f := by
  constructor
  intro U x y hxy
  apply J.transitive (hX U.unop) (equalizerSieve x y)
  intro V k hk
  obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hk
  let Y : Over (X i) := Over.mk b
  let f' := Functor.whiskerLeft (Over.forget (X i)).op f
  let x' : ToType (((Over.forget (X i)).op ⋙ P).obj (.op Y)) := P.map k.op x
  let y' : ToType (((Over.forget (X i)).op ⋙ P).obj (.op Y)) := P.map k.op y
  have hxy' : f'.app (.op Y) x' = f'.app (.op Y) y' := by
    change f.app (.op V) (P.map k.op x) = f.app (.op V) (P.map k.op y)
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]
  letI : IsLocallyInjective (J.over (X i)) f' := h i
  have hcover := equalizerSieve_mem (J.over (X i)) f' x' y' hxy'
  rw [GrothendieckTopology.mem_over_iff] at hcover
  change Sieve.overEquiv Y (equalizerSieve x' y') ∈ J Y.left at hcover
  have heqS : Sieve.overEquiv Y (equalizerSieve x' y') =
      equalizerSieve (P.map k.op x) (P.map k.op y) := by
    ext Z a
    rw [Sieve.overEquiv_iff]
    rfl
  rw [heqS] at hcover
  have hpull : Sieve.pullback k (equalizerSieve x y) =
      equalizerSieve (P.map k.op x) (P.map k.op y) := by
    ext Z a
    simp only [Sieve.pullback_apply, equalizerSieve_apply]
    rw [op_comp, P.map_comp]
    rfl
  rw [hpull]
  exact hcover

/-- Local surjectivity is detected on a family covering the terminal object. -/
lemma isLocallySurjective_of_coversTop {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    {ι : Type*} (X : ι → C) (hX : J.CoversTop X)
    (h : ∀ i, IsLocallySurjective (J.over (X i))
      (Functor.whiskerLeft (Over.forget (X i)).op f)) :
    IsLocallySurjective J f := by
  constructor
  intro U s
  apply J.transitive (hX U) (Presheaf.imageSieve f s)
  intro V k hk
  obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff ..).mp hk
  let Z : Over (X i) := Over.mk b
  let f' := Functor.whiskerLeft (Over.forget (X i)).op f
  let s' := Q.map k.op s
  change ToType (((Over.forget (X i)).op ⋙ Q).obj (.op Z)) at s'
  letI : IsLocallySurjective (J.over (X i)) f' := h i
  have hcover := Presheaf.imageSieve_mem (J.over (X i)) f' s'
  rw [GrothendieckTopology.mem_over_iff] at hcover
  change Sieve.overEquiv Z (Presheaf.imageSieve f' s') ∈ J V at hcover
  have heq : Sieve.overEquiv Z (Presheaf.imageSieve f' s') =
      Sieve.pullback k (Presheaf.imageSieve f s) := by
    ext W a
    rw [Sieve.overEquiv_iff]
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change f.app (.op W) t = Q.map (a ≫ k).op s
      change f.app (.op W) t = Q.map a.op (Q.map k.op s) at ht
      simpa only [op_comp, Q.map_comp, ConcreteCategory.comp_apply]
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      change f.app (.op W) t = Q.map a.op (Q.map k.op s)
      rw [op_comp, Q.map_comp] at ht
      change f.app (.op W) t = Q.map a.op (Q.map k.op s) at ht
      exact ht
  rw [heq] at hcover
  exact hcover

/-- A morphism that is a local weak equivalence on a covering family is one globally. -/
lemma W_of_coversTop [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{u}} (f : P ⟶ Q)
    {ι : Type*} (X : ι → C) (hX : J.CoversTop X)
    [∀ i, (J.over (X i)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (h : ∀ i, (J.over (X i)).W (Functor.whiskerLeft (Over.forget (X i)).op f)) :
    J.W f := by
  letI : IsLocallyInjective J f :=
    isLocallyInjective_of_coversTop f X hX (fun i => (h i).isLocallyInjective)
  letI : IsLocallySurjective J f :=
    isLocallySurjective_of_coversTop f X hX (fun i => (h i).isLocallySurjective)
  exact J.W_of_isLocallyBijective f

end CategoryTheory.Presheaf
