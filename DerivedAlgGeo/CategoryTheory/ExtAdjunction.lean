/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Ext along an adjunction with exact left adjoint

For `L ⊣ R` between abelian categories with `L` and `R` exact, there is a comparison

`Ext^n (L A) B  →  Ext^n A (R B)`

pushing a class along `R` and precomposing with the unit. This file constructs it, proves it is
additive, and settles the two ends of the intended induction: degree zero, and positive degree on
an injective.

## Why this file exists

`Sheaf.H n F` is `Ext` out of the constant sheaf — the *derived-category* `Ext` of
`Algebra/Homology/DerivedCategory/Ext/`, not the injective-resolution `Ext R C n` of
`CategoryTheory/Abelian/Ext.lean`. So the cohomology comparison `#572` step 3 asks for,
`Hⁱ(X, F) ≅ Hⁱ(Pⁿ, ι_* F)` along a closed immersion, is an `Ext` transport along `ι⁻¹ ⊣ ι_*`
and not a Čech computation. `ConstantSheafPullback.lean` moved the constant sheaf across that
adjunction; this file is the other half.

**Nothing at the pin relates `Ext` to an adjunction.** Grepping `Algebra/Homology/` and
`CategoryTheory/Abelian/` returns nothing under any spelling, so the statement here is new to the
tree and is not specific to sheaves — it is stated for arbitrary abelian categories.

## Exactness of `R` is a real hypothesis

`Ext.mapExactFunctor` requires its functor exact, so `R` is assumed exact and not merely left
exact. That is legitimate for the intended application — `ι_*` along a closed immersion is exact —
but it is not the general shape of an adjunction, and a caller who has only a left-exact right
adjoint gets nothing from this file.

## The theorem

`extAdjunctionAddEquiv` — the comparison is an isomorphism of additive groups in every degree.
`EnoughInjectives D` is what the proof needs and the only hypothesis beyond exactness.

Both halves are inductions on the degree, and both run on the same three-step shape: embed
`B ↪ I` with `I` injective, take the cokernel `Q`, and use that `R` carries that short exact
sequence to a short exact sequence in `C` whose middle term `R I` is *again* injective — which is
`preservesInjectiveObjects_of_adj`, and is the reason the argument closes at all.

* **Surjectivity.** The connecting map `Ext^n(-, Q) → Ext^{n+1}(-, B)` is surjective on both
  sides, because the terms next to it vanish on an injective. Pull the target class back
  downstairs, lift it by the inductive hypothesis, and push it forward: the two connecting maps
  agree with the comparison by `extAdjunctionMap_comp_extClass`.
* **Injectivity.** Given `x` in the kernel, write `x = x' ∘ δ` by that same surjectivity. Then
  `φ x'` dies against `δ'`, so by exactness downstairs it factors as `w ∘ R g`. Lift `w` through
  the comparison — this is where **surjectivity in degree `n` is used to prove injectivity in
  degree `n + 1`**, so the two theorems are not independent and the order matters — and conclude
  `x' = v ∘ g` by the inductive hypothesis. Then `x = v ∘ (g ∘ δ) = 0`, because consecutive maps
  of a long exact sequence compose to zero.

The degree-zero base cases are `extAdjunctionMap_mk₀`: there the comparison *is* the adjunction's
hom-equivalence, which is bijective because `Adjunction.homEquiv` is an `Equiv`.

`bijective_extAdjunctionMap_of_injective` is not used by either induction. It is kept because it
is the statement that makes the shape *plausible* before the induction is written, and because it
is the cheap sanity check on the setup: if the comparison were wrong, it would already fail there.

## A `rw`/`simp` trap worth recording

`Ext.mk₀_comp_mk₀` is `@[simp]`, its statement matches `extAdjunctionMap`'s composite at degree
zero syntactically, and **neither `rw` nor `simp` closes the goal** — the degree-addition proof
term does not unify. `exact Ext.mk₀_comp_mk₀ _ _` does. The same shape will recur anywhere
`Ext.comp` is unfolded at a specific degree.

## Main results

* `extAdjunctionMap` — the comparison, and `extAdjunctionAddHom` packaging its additivity.
* `extAdjunctionMap_mk₀` — degree zero is the adjunction.
* `extAdjunctionMap_comp`, `extAdjunctionMap_comp_mk₀`, `extAdjunctionMap_comp_extClass` — the
  comparison is a morphism of the two long exact sequences.
* `preservesInjectiveObjects_of_adj` — `R` preserves injectives.
* `bijective_extAdjunctionMap_of_injective` — positive degree on an injective.
* `surjective_extAdjunctionMap`, `injective_extAdjunctionMap`, `extAdjunctionAddEquiv` — the
  theorem.
* `Abelian.Ext.precompAddEquiv` — transport along an isomorphism in the first variable, which a
  consumer needs whenever the comparison identifies that variable only up to isomorphism.
-/

universe w v v' u u'

open CategoryTheory Category Limits Abelian

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasExt.{w} C] [HasExt.{w} D]

/-- **The comparison `Ext^n (L A) B → Ext^n A (R B)`.**

Push the class along `R`, then precompose with the unit of the adjunction. Both steps need `R`
exact: `Ext.mapExactFunctor` is only defined for an exact functor. -/
noncomputable def extAdjunctionMap {A : C} {B : D} {n : ℕ} (e : Ext.{w} (L.obj A) B n) :
    Ext.{w} A (R.obj B) n :=
  (Ext.mk₀ (adj.unit.app A)).comp (e.mapExactFunctor R) (zero_add n)

omit [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
@[simp]
lemma extAdjunctionMap_zero {A : C} {B : D} {n : ℕ} :
    extAdjunctionMap adj (0 : Ext.{w} (L.obj A) B n) = 0 := by
  simp only [extAdjunctionMap, Ext.mapExactFunctor_zero]
  exact Ext.comp_zero _ _ _ _ _

omit [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
lemma extAdjunctionMap_add {A : C} {B : D} {n : ℕ} (e f : Ext.{w} (L.obj A) B n) :
    extAdjunctionMap adj (e + f) = extAdjunctionMap adj e + extAdjunctionMap adj f := by
  simp only [extAdjunctionMap, Ext.mapExactFunctor_add]
  exact Ext.comp_add _ _ _ _

/-- The comparison as an additive map, which is how the induction consumes it: the long exact
sequences of `Ext` are sequences of additive groups, and a bare function does not map into them. -/
@[simps]
noncomputable def extAdjunctionAddHom (A : C) (B : D) (n : ℕ) :
    Ext.{w} (L.obj A) B n →+ Ext.{w} A (R.obj B) n where
  toFun := extAdjunctionMap adj
  map_zero' := extAdjunctionMap_zero adj
  map_add' := extAdjunctionMap_add adj

omit [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
/-- **The comparison is natural in the second variable.**

Post-composing before or after the comparison gives the same class. This is the lemma the
induction step runs on: it is what makes the comparison a *morphism* of the two long exact
sequences rather than a family of unrelated maps.

The proof is `Ext.mapExactFunctor_comp` followed by associativity — no exactness of the sequences
and no injectivity is used, so it holds for arbitrary classes in arbitrary degrees. -/
lemma extAdjunctionMap_comp {A : C} {Y Z : D} {a b c : ℕ} (x : Ext.{w} (L.obj A) Y a)
    (e : Ext.{w} Y Z b) (h : a + b = c) :
    extAdjunctionMap adj (x.comp e h)
      = (extAdjunctionMap adj x).comp (e.mapExactFunctor R) h := by
  simp only [extAdjunctionMap, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add a) h (by lia)).symm

omit [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
/-- Naturality against a morphism, the `Ext.mk₀` case of `extAdjunctionMap_comp`.

This is the square for the two "easy" maps of the long exact sequences — the ones induced by
`S.f` and `S.g`. -/
lemma extAdjunctionMap_comp_mk₀ {A : C} {Y Z : D} {a : ℕ} (x : Ext.{w} (L.obj A) Y a)
    (f : Y ⟶ Z) :
    extAdjunctionMap adj (x.comp (Ext.mk₀ f) (add_zero a))
      = (extAdjunctionMap adj x).comp (Ext.mk₀ (R.map f)) (add_zero a) := by
  simp only [extAdjunctionMap, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact (Ext.comp_assoc _ _ _ (zero_add a) (add_zero a) (by lia)).symm

omit [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
/-- **The connecting square.**

The comparison commutes with the connecting class of a short exact sequence. `R` is exact, so it
carries `S` to a short exact sequence in `C`, and `Ext.mapExactFunctor_extClass` says the
connecting class goes along with it.

Together with `extAdjunctionMap_comp_mk₀` this makes the comparison a morphism of the two long
exact sequences, which is the entire structural input to the dimension-shifting induction. -/
lemma extAdjunctionMap_comp_extClass {A : C} {S : ShortComplex D} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (hn₁ : n₀ + 1 = n₁) (x₃ : Ext.{w} (L.obj A) S.X₃ n₀) :
    extAdjunctionMap adj (x₃.comp hS.extClass hn₁)
      = (extAdjunctionMap adj x₃).comp (hS.map_of_exact R).extClass hn₁ := by
  simp only [extAdjunctionMap, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc _ _ _ (zero_add n₀) hn₁ (by lia)).symm

omit [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L] in
/-- **In degree zero the comparison is the adjunction's hom-equivalence.**

Stated in `Ext.mk₀` form rather than through `Ext.homEquiv₀`, because that is the form the
induction's base case needs and it avoids a round trip through the equivalence.

The proof is three rewrites and then `exact`, not `simp` — see the module docstring on
`Ext.mk₀_comp_mk₀`. -/
lemma extAdjunctionMap_mk₀ {A : C} {B : D} (f : L.obj A ⟶ B) :
    extAdjunctionMap adj (Ext.mk₀ f) = Ext.mk₀ (adj.homEquiv A B f) := by
  rw [extAdjunctionMap, Ext.mapExactFunctor_mk₀, Adjunction.homEquiv_unit]
  exact Ext.mk₀_comp_mk₀ _ _

omit [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasExt.{w} C] [HasExt.{w} D] in
include adj in
/-- A right adjoint whose left adjoint preserves monomorphisms preserves injectives.

Not an instance: `adj` is not inferrable from `R` alone, so instance search cannot find it. Every
use is an explicit `haveI`. -/
theorem preservesInjectiveObjects_of_adj : R.PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj

section Injective

variable {A : C} {B : D} [Injective B] {n : ℕ}

omit [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] [HasExt.{w} D] in
include adj in
/-- The target vanishes in positive degree, because `R B` is injective. -/
theorem subsingleton_ext_right_of_injective :
    Subsingleton (Ext.{w} A (R.obj B) (n + 1)) := by
  haveI := preservesInjectiveObjects_of_adj adj
  exact Ext.subsingleton_of_injective _ _ _

/-- **The comparison is bijective in positive degree on an injective.**

Both sides are subsingletons — the source by `Ext.subsingleton_of_injective` directly, the target
by `subsingleton_ext_right_of_injective` — so there is nothing to check. This is the base case the
dimension shift descends to, and it is the only reason the induction terminates. -/
theorem bijective_extAdjunctionMap_of_injective :
    Function.Bijective (extAdjunctionMap adj (A := A) (B := B) (n := n + 1)) := by
  haveI : Subsingleton (Ext.{w} (L.obj A) B (n + 1)) := Ext.subsingleton_of_injective _ _ _
  haveI : Subsingleton (Ext.{w} A (R.obj B) (n + 1)) := subsingleton_ext_right_of_injective adj
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

end Injective

section Bijective

variable [EnoughInjectives D]

/-- **The comparison is surjective in every degree.**

The induction embeds `B` in an injective and compares connecting maps. Both connecting maps are
surjective — upstairs because `Ext^{n+1}(L A, I)` vanishes, downstairs because `R I` is again
injective — so a class in the target pulls back, lifts by the inductive hypothesis, and pushes
forward. -/
theorem surjective_extAdjunctionMap (n : ℕ) (A : C) (B : D) :
    Function.Surjective (extAdjunctionMap adj (A := A) (B := B) (n := n)) := by
  induction n generalizing A B with
  | zero =>
    intro y
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective A (R.obj B)).2 y
    exact ⟨Ext.mk₀ ((adj.homEquiv A B).symm g), by
      rw [extAdjunctionMap_mk₀, Equiv.apply_symm_apply]⟩
  | succ n ih =>
    intro y
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι B))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    have hRS := hS.map_of_exact R
    haveI := preservesInjectiveObjects_of_adj adj
    haveI : Injective (S.map R).X₂ := inferInstanceAs (Injective (R.obj S.X₂))
    have hsurj' : Function.Surjective (Ext.postcomp hRS.extClass A (rfl : n + 1 = _)) :=
      fun y₁ ↦ Ext.covariant_sequence_exact₁ A hRS y₁ (Ext.eq_zero_of_injective _) rfl
    obtain ⟨z, hz⟩ := hsurj' y
    obtain ⟨x, hx⟩ := ih A S.X₃ z
    exact ⟨x.comp hS.extClass rfl, by
      rw [extAdjunctionMap_comp_extClass adj hS rfl x, hx]; exact hz⟩

/-- **The comparison is injective in every degree.**

Note the dependence: the successor case calls `surjective_extAdjunctionMap` in degree `n` to lift
the class the exactness argument produces. Injectivity is therefore *not* provable independently
of surjectivity, and reordering the two theorems breaks the file. -/
theorem injective_extAdjunctionMap (n : ℕ) (A : C) (B : D) :
    Function.Injective (extAdjunctionMap adj (A := A) (B := B) (n := n)) := by
  induction n generalizing A B with
  | zero =>
    intro x y hxy
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective (L.obj A) B).2 x
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective (L.obj A) B).2 y
    rw [extAdjunctionMap_mk₀, extAdjunctionMap_mk₀] at hxy
    exact congrArg Ext.mk₀ ((adj.homEquiv A B).injective
      ((Ext.mk₀_bijective A (R.obj B)).1 hxy))
  | succ n ih =>
    have key : ∀ (A : C) (B : D) (x : Ext.{w} (L.obj A) B (n + 1)),
        extAdjunctionMap adj x = 0 → x = 0 := by
      intro A B x hx
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι B))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have hRS := hS.map_of_exact R
      haveI := preservesInjectiveObjects_of_adj adj
      haveI : Injective (S.map R).X₂ := inferInstanceAs (Injective (R.obj S.X₂))
      obtain ⟨x', rfl⟩ : ∃ x' : Ext.{w} (L.obj A) S.X₃ n,
          x'.comp hS.extClass (rfl : n + 1 = _) = x :=
        Ext.covariant_sequence_exact₁ (L.obj A) hS x (Ext.eq_zero_of_injective _) rfl
      rw [extAdjunctionMap_comp_extClass adj hS rfl x'] at hx
      obtain ⟨w, hw⟩ := Ext.covariant_sequence_exact₃ A hRS _ (rfl : n + 1 = _) hx
      obtain ⟨v, rfl⟩ := surjective_extAdjunctionMap adj n A S.X₂ w
      have hv : v.comp (Ext.mk₀ S.g) (add_zero n) = x' :=
        ih A S.X₃ (by rw [extAdjunctionMap_comp_mk₀]; exact hw)
      rw [← hv, Ext.comp_assoc _ _ _ (add_zero n) rfl (by lia),
        ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
    intro x y hxy
    have : extAdjunctionMap adj (x - y) = 0 := by
      rw [← extAdjunctionAddHom_apply adj, map_sub, extAdjunctionAddHom_apply,
        extAdjunctionAddHom_apply, hxy, sub_self]
    exact sub_eq_zero.1 (key A B _ this)

/-- **Ext along an adjunction with exact left adjoint.**

`Ext^n (L A) B ≃+ Ext^n A (R B)`, for every `n`. This is the statement the cohomology comparison
of `#572` step 3 instantiates at `L = ι⁻¹`, `R = ι_*` for a closed immersion. -/
noncomputable def extAdjunctionAddEquiv (A : C) (B : D) (n : ℕ) :
    Ext.{w} (L.obj A) B n ≃+ Ext.{w} A (R.obj B) n :=
  AddEquiv.ofBijective (extAdjunctionAddHom adj A B n)
    ⟨injective_extAdjunctionMap adj n A B, surjective_extAdjunctionMap adj n A B⟩

@[simp]
lemma extAdjunctionAddEquiv_apply (A : C) (B : D) (n : ℕ) (e : Ext.{w} (L.obj A) B n) :
    extAdjunctionAddEquiv adj A B n e = extAdjunctionMap adj e :=
  rfl

end Bijective

section Precomp

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **Precomposition with an isomorphism is an isomorphism of `Ext` groups.**

Not in Mathlib at the pin under any spelling, and needed the moment a comparison identifies the
first variable up to isomorphism rather than on the nose — which is exactly what happens when the
constant sheaf is carried across a pullback. -/
noncomputable def Abelian.Ext.precompAddEquiv {X X' : C} (e : X ≅ X') (B : C) (n : ℕ) :
    Ext.{w} X' B n ≃+ Ext.{w} X B n where
  toFun x := (Ext.mk₀ e.hom).comp x (zero_add n)
  invFun y := (Ext.mk₀ e.inv).comp y (zero_add n)
  left_inv x := by
    dsimp only
    rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by lia), Ext.mk₀_comp_mk₀,
      e.inv_hom_id, Ext.mk₀_id_comp]
  right_inv y := by
    dsimp only
    rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (by lia), Ext.mk₀_comp_mk₀,
      e.hom_inv_id, Ext.mk₀_id_comp]
  map_add' x y := Ext.comp_add _ _ _ _

end Precomp

end CategoryTheory
