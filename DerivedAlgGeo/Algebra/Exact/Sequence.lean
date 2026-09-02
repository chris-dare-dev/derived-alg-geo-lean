/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Exact.Sequence

/-!
# Alternating finite dimensions along a bounded long exact sequence

Mathlib's `Module.sum_neg_one_pow_finrank_eq_zero_of_exact` says that the alternating sum of
dimensions along a finite exact sequence vanishes. The long exact sequence attached to a
short exact sequence of complexes has the zig-zag shape

`0 → A 0 → B 0 → C 0 → A 1 → B 1 → C 1 → ⋯ → C n → A (n + 1) = 0`,

and this file states that theorem in that shape: the alternating sum of
`dim A i - dim B i + dim C i` over `i ≤ n` vanishes. Injectivity of `f 0` is the left end;
the right end is stated as vanishing of `A (n + 1)`, which makes the last connecting map
surjective onto zero. Geometric Euler-characteristic additivity consumes it after
constructing the long exact sequence of coherent cohomology.

The `ℤ`-indexed, boundary-free form is `GradedObject.eulerChar_eq_add_of_exact` in
`Algebra/Homology/EulerCharacteristic.lean`.
-/

namespace Module

variable {k : Type*} [DivisionRing k]
variable (A : ℕ → Type*) (B : ℕ → Type*) (C : ℕ → Type*)
  [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
  [∀ i, Module k (A i)] [∀ i, Module k (B i)] [∀ i, Module k (C i)]
  [∀ i, Module.Finite k (A i)] [∀ i, Module.Finite k (B i)] [∀ i, Module.Finite k (C i)]
  (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i)
  (δ : ∀ i, C i →ₗ[k] A (i + 1))

/-- **Alternating dimensions cancel along a bounded long exact sequence** of the zig-zag shape
`A i → B i → C i → A (i + 1)`: the form of `Module.sum_neg_one_pow_finrank_eq_zero_of_exact`
attached to a short exact sequence of complexes. The endpoint hypothesis is stated as vanishing
of the next `A` term, which makes the final connecting map surjective onto zero. -/
theorem sum_neg_one_pow_finrank_eq_zero_of_longExact
    (hinj : Function.Injective (f 0))
    (hexact₂ : ∀ i, Function.Exact (f i) (g i))
    (hexact₃ : ∀ i, Function.Exact (g i) (δ i))
    (hexact₁ : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (n : ℕ) [Subsingleton (A (n + 1))] :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
      ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) = 0 := by
  have hA₀ : Module.finrank k (A 0) = Module.finrank k (LinearMap.range (f 0)) :=
    (LinearMap.finrank_range_of_inj hinj).symm
  have hB (i : ℕ) : Module.finrank k (B i) =
      Module.finrank k (LinearMap.range (f i)) +
        Module.finrank k (LinearMap.range (g i)) :=
    (hexact₂ i).finrank_eq_finrank_range_add_finrank_range
  have hC (i : ℕ) : Module.finrank k (C i) =
      Module.finrank k (LinearMap.range (g i)) +
        Module.finrank k (LinearMap.range (δ i)) :=
    (hexact₃ i).finrank_eq_finrank_range_add_finrank_range
  have hA (i : ℕ) : Module.finrank k (A (i + 1)) =
      Module.finrank k (LinearMap.range (δ i)) +
        Module.finrank k (LinearMap.range (f (i + 1))) :=
    (hexact₁ i).finrank_eq_finrank_range_add_finrank_range
  have hδn : Module.finrank k (LinearMap.range (δ n)) = 0 := by
    letI : Subsingleton (LinearMap.range (δ n)) := inferInstance
    exact Module.finrank_zero_of_subsingleton
  have hpartial (m : ℕ) :
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) +
          Module.finrank k (C i)) =
        (-1 : ℤ) ^ m * Module.finrank k (LinearMap.range (δ m)) := by
    induction m with
    | zero =>
        simp only [Nat.reduceAdd, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul]
        have hA₀' := hA₀
        have hB' := hB 0
        have hC' := hC 0
        push_cast at hA₀' hB' hC'
        omega
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have hA' := hA m
        have hB' := hB (m + 1)
        have hC' := hC (m + 1)
        have htriple :
            (Module.finrank k (A (m + 1)) : ℤ) - Module.finrank k (B (m + 1)) +
                Module.finrank k (C (m + 1)) =
              Module.finrank k (LinearMap.range (δ m)) +
                Module.finrank k (LinearMap.range (δ (m + 1))) := by
          omega
        rw [htriple, pow_succ]
        ring
  rw [hpartial n, hδn, Int.ofNat_zero, mul_zero]

end Module
