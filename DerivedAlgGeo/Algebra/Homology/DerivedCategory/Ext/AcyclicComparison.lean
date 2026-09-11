/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Ext along an exact functor, from a fixed comparison morphism

Let `R : D ⥤ C` be an exact functor between abelian categories, `P : D`, `A : C`, and
`u : A ⟶ R.obj P`. Pushing a class along `R` and precomposing with `u` gives

`extComparisonMap u : Ext^n P B → Ext^n A (R B)`

for every `B : D` and every `n`. This file proves that the comparison is bijective in every
degree as soon as

* it is bijective in degree zero, and
* `Ext^(n+1) A (R I)` vanishes for every injective `I : D` (`R I` is *acyclic* against `A`),

provided `D` has enough injectives. The proof is dimension shifting along an injective
presentation `B ↪ I ↠ Q`, exactly as for `extAdjunctionAddEquiv` in `Ext/Adjunction.lean`;
that theorem is the special case `u := adj.unit.app A` of an adjunction `L ⊣ R` with `L`
exact, where the acyclicity hypothesis holds because `R I` is then injective. Here nothing is
assumed about a left adjoint, which is what a cohomology comparison needs when the left adjoint
is only right exact: the forgetful functor from module sheaves to abelian sheaves has the
extension-of-scalars functor as left adjoint, which is not exact, but its images of injective
module sheaves are still acyclic, because they are flasque.

## Main results

* `extComparisonMap`, `extComparisonAddHom` — the comparison and its additivity.
* `extComparisonMap_comp_mk₀`, `extComparisonMap_comp_extClass` — the comparison is a morphism
  of the two long exact `Ext` sequences.
* `surjective_extComparisonMap`, `injective_extComparisonMap`, `extComparisonAddEquiv` — the
  theorem.
-/

universe w v v' u u'

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {R : D ⥤ C} [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasExt.{w} C] [HasExt.{w} D]
  {A : C} {P : D} (u : A ⟶ R.obj P)

/-- **The comparison `Ext^n P B → Ext^n A (R B)`.** Push the class along `R`, then precompose
with `u`. -/
noncomputable def extComparisonMap {B : D} {n : ℕ} (e : Ext.{w} P B n) :
    Ext.{w} A (R.obj B) n :=
  (Ext.mk₀ u).comp (e.mapExactFunctor R) (zero_add n)

@[simp]
lemma extComparisonMap_zero {B : D} {n : ℕ} :
    extComparisonMap u (0 : Ext.{w} P B n) = 0 := by
  simp only [extComparisonMap, Ext.mapExactFunctor_zero]
  exact Ext.comp_zero _ _ _ _ _

lemma extComparisonMap_add {B : D} {n : ℕ} (e f : Ext.{w} P B n) :
    extComparisonMap u (e + f) = extComparisonMap u e + extComparisonMap u f := by
  simp only [extComparisonMap, Ext.mapExactFunctor_add]
  exact Ext.comp_add _ _ _ _

/-- The comparison as an additive map. -/
@[simps]
noncomputable def extComparisonAddHom (B : D) (n : ℕ) :
    Ext.{w} P B n →+ Ext.{w} A (R.obj B) n where
  toFun := extComparisonMap u
  map_zero' := extComparisonMap_zero u
  map_add' := extComparisonMap_add u

/-- The comparison is natural in the second variable. -/
lemma extComparisonMap_comp {Y Z : D} {a b c : ℕ} (x : Ext.{w} P Y a)
    (e : Ext.{w} Y Z b) (h : a + b = c) :
    extComparisonMap u (x.comp e h) = (extComparisonMap u x).comp (e.mapExactFunctor R) h := by
  simp only [extComparisonMap, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add a) h (by lia)).symm

/-- Naturality against a morphism: the square for the maps of the long exact sequences
induced by `S.f` and `S.g`. -/
lemma extComparisonMap_comp_mk₀ {Y Z : D} {a : ℕ} (x : Ext.{w} P Y a) (f : Y ⟶ Z) :
    extComparisonMap u (x.comp (Ext.mk₀ f) (add_zero a))
      = (extComparisonMap u x).comp (Ext.mk₀ (R.map f)) (add_zero a) := by
  simp only [extComparisonMap, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add a) (add_zero a) (by lia)).symm

/-- The connecting square: the comparison commutes with the connecting class of a short exact
sequence, because `R` carries the sequence to a short exact sequence and
`Ext.mapExactFunctor_extClass` carries the class along. -/
lemma extComparisonMap_comp_extClass {S : ShortComplex D} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (hn₁ : n₀ + 1 = n₁) (x₃ : Ext.{w} P S.X₃ n₀) :
    extComparisonMap u (x₃.comp hS.extClass hn₁)
      = (extComparisonMap u x₃).comp (hS.map_of_exact R).extClass hn₁ := by
  simp only [extComparisonMap, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n₀) hn₁ (by lia)).symm

/-- In degree zero the comparison sends `mk₀ f` to `mk₀ (u ≫ R.map f)`. -/
lemma extComparisonMap_mk₀ {B : D} (f : P ⟶ B) :
    extComparisonMap u (Ext.mk₀ f) = Ext.mk₀ (u ≫ R.map f) := by
  simp only [extComparisonMap, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- The degree-zero comparison is bijective iff `f ↦ u ≫ R.map f` is, under the
identifications `Ext⁰ = Hom`. This is how the degree-zero hypothesis of
`extComparisonAddEquiv` is checked in practice. -/
lemma bijective_extComparisonMap_zero_iff (B : D) :
    Function.Bijective (extComparisonMap u (B := B) (n := 0)) ↔
      Function.Bijective (fun f : P ⟶ B ↦ u ≫ R.map f) := by
  have : extComparisonMap u (B := B) (n := 0) =
      Ext.mk₀ ∘ (fun f : P ⟶ B ↦ u ≫ R.map f) ∘ Ext.homEquiv₀ := by
    funext e
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective P B).2 e
    have hf : Ext.homEquiv₀ (Ext.mk₀ f) = f :=
      (Equiv.ofBijective _ (Ext.mk₀_bijective P B)).symm_apply_apply f
    simp only [Function.comp, extComparisonMap_mk₀, hf]
  rw [this, (Ext.mk₀_bijective A (R.obj B)).of_comp_iff',
    Function.Bijective.of_comp_iff _ Ext.homEquiv₀.bijective]

section Bijective

variable [EnoughInjectives D]
  (h₀ : ∀ B : D, Function.Bijective (extComparisonMap u (B := B) (n := 0)))
  (hacyclic : ∀ (I : D) [Injective I] (n : ℕ), Subsingleton (Ext.{w} A (R.obj I) (n + 1)))
include h₀ hacyclic

/-- **The comparison is surjective in every degree.** Embed `B` in an injective `I` with
quotient `Q`; both connecting maps `Ext^n(-, Q) → Ext^(n+1)(-, B)` are surjective, upstairs
because `Ext^(n+1) P I` vanishes and downstairs by acyclicity of `R I`, so a class pulls back,
lifts by induction, and pushes forward. -/
theorem surjective_extComparisonMap (n : ℕ) (B : D) :
    Function.Surjective (extComparisonMap u (B := B) (n := n)) := by
  induction n generalizing B with
  | zero => exact (h₀ B).2
  | succ n ih =>
    intro y
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι B))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    have hRS := hS.map_of_exact R
    haveI : Subsingleton (Ext.{w} A (S.map R).X₂ (n + 1)) := hacyclic S.X₂ n
    have hsurj' : Function.Surjective (Ext.postcomp hRS.extClass A (rfl : n + 1 = _)) :=
      fun y₁ ↦ Ext.covariant_sequence_exact₁ A hRS y₁ (Subsingleton.elim _ _) rfl
    obtain ⟨z, hz⟩ := hsurj' y
    obtain ⟨x, hx⟩ := ih S.X₃ z
    exact ⟨x.comp hS.extClass rfl, by
      rw [extComparisonMap_comp_extClass u hS rfl x, hx]; exact hz⟩

/-- **The comparison is injective in every degree.** The successor case uses surjectivity in
degree `n` to lift the class that exactness produces, so the two theorems are not
independent. -/
theorem injective_extComparisonMap (n : ℕ) (B : D) :
    Function.Injective (extComparisonMap u (B := B) (n := n)) := by
  induction n generalizing B with
  | zero => exact (h₀ B).1
  | succ n ih =>
    have key : ∀ (B : D) (x : Ext.{w} P B (n + 1)), extComparisonMap u x = 0 → x = 0 := by
      intro B x hx
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι B))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have hRS := hS.map_of_exact R
      haveI : Injective S.X₂ := Injective.injective_under B
      obtain ⟨x', rfl⟩ : ∃ x' : Ext.{w} P S.X₃ n, x'.comp hS.extClass (rfl : n + 1 = _) = x :=
        Ext.covariant_sequence_exact₁ P hS x (Ext.eq_zero_of_injective _) rfl
      rw [extComparisonMap_comp_extClass u hS rfl x'] at hx
      obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ A hRS _ (rfl : n + 1 = _) hx
      obtain ⟨v, rfl⟩ := surjective_extComparisonMap u h₀ hacyclic n S.X₂ w
      have hv : v.comp (Ext.mk₀ S.g) (add_zero n) = x' :=
        ih S.X₃ (by rw [extComparisonMap_comp_mk₀]; exact hw)
      rw [← hv, Ext.comp_assoc _ _ _ (add_zero n) rfl (by lia),
        ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
    intro x y hxy
    have : extComparisonMap u (x - y) = 0 := by
      rw [← extComparisonAddHom_apply u, map_sub, extComparisonAddHom_apply,
        extComparisonAddHom_apply, hxy, sub_self]
    exact sub_eq_zero.1 (key B _ this)

/-- **Ext comparison from acyclicity of images of injectives.** `Ext^n P B ≃+ Ext^n A (R B)`
for every `n`, given bijectivity in degree zero and vanishing of `Ext^(n+1) A (R I)` for
injective `I`. -/
noncomputable def extComparisonAddEquiv (B : D) (n : ℕ) :
    Ext.{w} P B n ≃+ Ext.{w} A (R.obj B) n :=
  AddEquiv.ofBijective (extComparisonAddHom u B n)
    ⟨injective_extComparisonMap u h₀ hacyclic n B,
      surjective_extComparisonMap u h₀ hacyclic n B⟩

@[simp]
lemma extComparisonAddEquiv_apply (B : D) (n : ℕ) (e : Ext.{w} P B n) :
    extComparisonAddEquiv u h₀ hacyclic B n e = extComparisonMap u e :=
  rfl

end Bijective

end CategoryTheory
