/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# Dimension shifting for `Ext`

Embedding an object in an injective one shifts `Ext` down a degree: for a short
exact sequence `0 → B → I → C → 0` with `I` injective,

```
Ext^n(X, C) ≅ Ext^{n+1}(X, B)      (n ≥ 1)
```

and the isomorphism is composition with the sequence's own `extClass`.

Both directions are the covariant long exact sequence together with the
vanishing of `Ext^k(X, I)` for `k ≥ 1`:

* **injective** — a class killed by `extClass` comes from `Ext^n(X, I)`, which
  is zero because `n ≥ 1`;
* **surjective** — a class of `Ext^{n+1}(X, B)` maps into `Ext^{n+1}(X, I)`,
  which is zero because `n + 1 ≥ 1`, so it is in the image.

Only the injectivity half needs `n ≥ 1`; at `n = 0` the map is still surjective,
and `postcomp_extClass_surjective` is stated separately for that reason. This is
the shape the induction in a dimension-shifting argument actually uses: the base
case is a cokernel, not an isomorphism.

Mathlib has the long exact sequence and the vanishing but not this consequence.
-/

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- **Surjectivity half of dimension shifting**, which needs no lower bound on
the degree: everything in `Ext^{n+1}(X, B)` is a composite with `extClass`,
because its image in `Ext^{n+1}(X, I)` has nowhere to go. -/
theorem postcomp_extClass_surjective (X : C) {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂] {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁) :
    Function.Surjective (hS.extClass.postcomp X hn) := by
  subst hn
  intro x₁
  obtain ⟨x₃, hx₃⟩ := covariant_sequence_exact₁ (hS := hS) (x₁ := x₁)
    (hx₁ := eq_zero_of_injective _) (hn₀ := rfl)
  exact ⟨x₃, hx₃⟩

/-- **Dimension shifting.**  Composition with `extClass` is bijective in every
degree above zero. -/
theorem postcomp_extClass_bijective (X : C) {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂] {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    (hn₀ : 0 < n₀) :
    Function.Bijective (hS.extClass.postcomp X hn) := by
  obtain ⟨m, rfl⟩ : ∃ m, n₀ = m + 1 := ⟨n₀ - 1, by lia⟩
  refine ⟨?_, postcomp_extClass_surjective X hS hn⟩
  subst hn
  rw [injective_iff_map_eq_zero]
  intro x₃ hx
  obtain ⟨x₂, rfl⟩ := covariant_sequence_exact₃ (hS := hS) (x₃ := x₃)
    (hn₁ := rfl) (hx₃ := hx)
  rw [eq_zero_of_injective x₂, zero_comp]

/-- Dimension shifting as an isomorphism of abelian groups. -/
noncomputable def extClassAddEquiv (X : C) {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂] {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    (hn₀ : 0 < n₀) :
    Ext X S.X₃ n₀ ≃+ Ext X S.X₁ n₁ :=
  AddEquiv.ofBijective _ (postcomp_extClass_bijective X hS hn hn₀)

@[simp]
theorem extClassAddEquiv_apply (X : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Injective S.X₂] {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁) (hn₀ : 0 < n₀)
    (x : Ext X S.X₃ n₀) :
    extClassAddEquiv X hS hn hn₀ x = x.comp hS.extClass hn :=
  rfl

end CategoryTheory.Abelian.Ext
