/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.K3
import Mathlib.Tactic.LinearCombination

/-!
# The square root of a normalized graded class, and `√td(X)`

For a graded class `f` with `f 0 = 1`, the square root is the family of
components given by the coefficients of `√(1 + x)`:

```
g 0 = 1,  g 1 = f₁/2,  g 2 = f₂/2 − f₁²/8,  g 3 = f₃/2 − f₁f₂/4 + f₁³/16,
g 4 = f₄/2 − f₁f₃/4 − f₂²/8 + 3f₁²f₂/16 − 5f₁⁴/128
```

What makes the name honest is `sqrtComp_convolution`: `∑_{j ≤ i} g_j·g_{i−j} = f_i`.
Nothing in the repository could write `√td(X)` before this; `git grep sqrt` over
`AlgebraicGeometry/**` returned nothing, and Mathlib at the pin has no Chern or
Todd theory at all.

## The codimension-four ceiling is a limitation, and it is stated

`sqrtComp f i = 0` for `i > 4`, and `sqrtComp_convolution` carries an explicit
`i ≤ 4` hypothesis rather than hiding the bound behind a `decide`. This is the
same ceiling and the same reason as `Numerical/Core/CharacteristicClasses.lean`,
whose `toddComponent` stops at four: the expressions are written out, not
recursed, so they stop where they were written.

## Why the proof runs on one scalar

Every coefficient is a power of `1/2` up to an integer factor —
`1/4 = h²`, `1/8 = h³`, `1/16 = h⁴`, `3/16 = 3h⁴`, `5/128 = 5h⁷` for
`h = algebraMap ℚ A (1/2)`. Rewriting them that way leaves **one** scalar atom,
so the convolution becomes a polynomial identity in `h` and the `f`'s modulo the
single relation `h + h = 1`, and each case closes by `linear_combination` with
an explicit cofactor.

The cofactors are not guesses: `G = (2h − 1)·c` was verified symbolically for
each `i` before any of this was written. Writing the coefficients as distinct
`algebraMap` values instead leaves `ring` with five unrelated atoms and no way
to relate them, which is why the obvious `simp; ring` does not work here.

## Main results

* `sqrtComp`, with `sqrtComp_zero`, `sqrtComp_one` and
  `sqrtComp_eq_zero_of_four_lt`.
* `sqrtComp_convolution` — the identity that earns the name.
* `sqrtComp_mem` — the square root respects the grading.
* `NumericalVarietyData.sqrtToddComp` and its three companions.
* `K3.sqrtToddComp_one` and `K3.degree_sqrtToddComp_two` — together, the formal
  content of the claim `√td(X) = 1 + [pt]` that
  `Numerical/RiemannRoch/K3.lean` currently makes in prose only.
-/

open Finset

universe u v

namespace AlgebraicGeometry.Numerical

variable {A : Type u} [CommRing A] [Algebra ℚ A]

/-! ### The coefficients -/

/-- The square root of a graded class whose codimension-zero part is `1`,
component by component. Zero above codimension four; see the module docstring. -/
noncomputable def sqrtComp (f : ℕ → A) : ℕ → A
  | 0 => 1
  | 1 => algebraMap ℚ A (1 / 2) * f 1
  | 2 => algebraMap ℚ A (1 / 2) * f 2 - algebraMap ℚ A (1 / 8) * (f 1 * f 1)
  | 3 => algebraMap ℚ A (1 / 2) * f 3 - algebraMap ℚ A (1 / 4) * (f 1 * f 2)
      + algebraMap ℚ A (1 / 16) * (f 1 * f 1 * f 1)
  | 4 => algebraMap ℚ A (1 / 2) * f 4 - algebraMap ℚ A (1 / 4) * (f 1 * f 3)
      - algebraMap ℚ A (1 / 8) * (f 2 * f 2)
      + algebraMap ℚ A (3 / 16) * (f 1 * f 1 * f 2)
      - algebraMap ℚ A (5 / 128) * (f 1 * f 1 * f 1 * f 1)
  | _ + 5 => 0

@[simp]
theorem sqrtComp_zero (f : ℕ → A) : sqrtComp f 0 = 1 := rfl

theorem sqrtComp_one (f : ℕ → A) :
    sqrtComp f 1 = algebraMap ℚ A (1 / 2) * f 1 := rfl

@[simp]
theorem sqrtComp_eq_zero_of_four_lt (f : ℕ → A) {i : ℕ} (hi : 4 < i) :
    sqrtComp f i = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 5 := ⟨i - 5, by omega⟩
  rfl

/-! ### The scalar relations

Each coefficient is a power of `h = algebraMap ℚ A (1/2)` up to an integer
factor, which is what leaves the convolution with a single atom. -/

private theorem am_quarter : algebraMap ℚ A (1 / 4) = algebraMap ℚ A (1 / 2) ^ 2 := by
  rw [← map_pow]; norm_num

private theorem am_eighth : algebraMap ℚ A (1 / 8) = algebraMap ℚ A (1 / 2) ^ 3 := by
  rw [← map_pow]; norm_num

private theorem am_sixteenth : algebraMap ℚ A (1 / 16) = algebraMap ℚ A (1 / 2) ^ 4 := by
  rw [← map_pow]; norm_num

private theorem am_three_sixteenths :
    algebraMap ℚ A (3 / 16) = 3 * algebraMap ℚ A (1 / 2) ^ 4 := by
  rw [← map_pow, show (3 : A) = algebraMap ℚ A 3 from (map_ofNat _ 3).symm, ← map_mul]
  norm_num

private theorem am_five_128 :
    algebraMap ℚ A (5 / 128) = 5 * algebraMap ℚ A (1 / 2) ^ 7 := by
  rw [← map_pow, show (5 : A) = algebraMap ℚ A 5 from (map_ofNat _ 5).symm, ← map_mul]
  norm_num

private theorem am_half_add : algebraMap ℚ A (1 / 2) + algebraMap ℚ A (1 / 2) = 1 := by
  rw [← map_add]; norm_num

/-! ### The convolution -/

/-- **The identity that makes the name honest**: `∑_{j ≤ i} g_j·g_{i−j} = f_i`.

Carries `i ≤ 4` explicitly, because the coefficients stop there. -/
theorem sqrtComp_convolution (f : ℕ → A) (hf : f 0 = 1) {i : ℕ} (hi : i ≤ 4) :
    ∑ j ∈ range (i + 1), sqrtComp f j * sqrtComp f (i - j) = f i := by
  have hh := am_half_add (A := A)
  obtain _ | _ | _ | _ | _ | i := i
  · simpa [sqrtComp] using hf.symm
  · norm_num [Finset.sum_range_succ, sqrtComp]
    linear_combination (f 1) * hh
  · norm_num [Finset.sum_range_succ, sqrtComp, am_eighth]
    linear_combination (f 2 - algebraMap ℚ A (1 / 2) ^ 2 * (f 1 * f 1)) * hh
  · norm_num [Finset.sum_range_succ, sqrtComp, am_quarter, am_eighth, am_sixteenth]
    linear_combination (f 3) * hh
  · norm_num [Finset.sum_range_succ, sqrtComp, am_quarter, am_eighth, am_sixteenth,
      am_three_sixteenths, am_five_128]
    linear_combination
      (f 4 - algebraMap ℚ A (1 / 2) ^ 2 * (f 2 * f 2)
        + 2 * algebraMap ℚ A (1 / 2) ^ 3 * (f 1 * f 1 * f 2)
        - 5 * algebraMap ℚ A (1 / 2) ^ 6 * (f 1 * f 1 * f 1 * f 1)
        - 2 * algebraMap ℚ A (1 / 2) ^ 5 * (f 1 * f 1 * f 1 * f 1)) * hh
  · exact absurd hi (by omega)

/-! ### The square root respects the grading -/

/-- If every `f j` sits in codimension `j`, so does every `sqrtComp f i`. -/
theorem sqrtComp_mem {n : ℕ} (R : NumericalRingData n A) (f : ℕ → A)
    (hf : ∀ j, f j ∈ R.piece j) (i : ℕ) : sqrtComp f i ∈ R.piece i := by
  have hc : ∀ (q : ℚ) {j : ℕ} {x : A}, x ∈ R.piece j →
      algebraMap ℚ A q * x ∈ R.piece j :=
    fun q _ _ hx => by simpa using R.mul_mem_piece (R.algebraMap_mem_piece_zero q) hx
  match i with
  | 0 => simpa [sqrtComp] using R.one_mem_piece_zero
  | 1 => exact hc _ (hf 1)
  | 2 =>
    refine Submodule.sub_mem _ (hc _ (hf 2)) (hc _ ?_)
    simpa using R.mul_mem_piece (hf 1) (hf 1)
  | 3 =>
    refine Submodule.add_mem _ (Submodule.sub_mem _ (hc _ (hf 3)) (hc _ ?_)) (hc _ ?_)
    · simpa using R.mul_mem_piece (hf 1) (hf 2)
    · simpa using R.mul_mem_piece (R.mul_mem_piece (hf 1) (hf 1)) (hf 1)
  | 4 =>
    refine Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ (hc _ (hf 4)) (hc _ ?_)) (hc _ ?_)) (hc _ ?_)) (hc _ ?_)
    · simpa using R.mul_mem_piece (hf 1) (hf 3)
    · simpa using R.mul_mem_piece (hf 2) (hf 2)
    · simpa using R.mul_mem_piece (R.mul_mem_piece (hf 1) (hf 1)) (hf 2)
    · simpa using
        R.mul_mem_piece (R.mul_mem_piece (R.mul_mem_piece (hf 1) (hf 1)) (hf 1)) (hf 1)
  | _ + 5 => simp

/-! ### `√td(X)` -/

variable {N : Type v} [AddCommGroup N] {n : ℕ}

namespace NumericalVarietyData

/-- **`√td(X)`**, component by component. -/
noncomputable def sqrtToddComp (V : NumericalVarietyData n A N) : ℕ → A :=
  sqrtComp V.toddComp

@[simp]
theorem sqrtToddComp_zero (V : NumericalVarietyData n A N) : V.sqrtToddComp 0 = 1 := rfl

/-- `√td(X)` respects the grading, from `toddComp_mem`. -/
theorem sqrtToddComp_mem (V : NumericalVarietyData n A N) (i : ℕ) :
    V.sqrtToddComp i ∈ V.ring.piece i :=
  sqrtComp_mem V.ring V.toddComp V.toddComp_mem i

/-- `√td(X)` squares to `td(X)`, in every codimension up to four. -/
theorem sqrtToddComp_convolution (V : NumericalVarietyData n A N) {i : ℕ} (hi : i ≤ 4) :
    ∑ j ∈ range (i + 1), V.sqrtToddComp j * V.sqrtToddComp (i - j) = V.toddComp i :=
  sqrtComp_convolution V.toddComp V.toddComp_zero hi

end NumericalVarietyData

namespace K3

variable {V : NumericalVarietyData 2 A N}

/-- On a K3 the linear term of `√td` vanishes, because `td₁ = 0`. -/
theorem sqrtToddComp_one (hK3 : IsK3 V) : V.sqrtToddComp 1 = 0 := by
  rw [NumericalVarietyData.sqrtToddComp, sqrtComp_one, hK3.toddComp_one, mul_zero]

/-- `∫_X √td₂ = 1`: with `td₁ = 0` the quadratic term is `td₂/2`, and
`∫td₂ = χ(O_X) = 2`.

Together with `sqrtToddComp_one` and `sqrtToddComp_zero` this is the formal
content of `√td(X) = 1 + [pt]`, which `RiemannRoch/K3.lean` states in prose. -/
theorem degree_sqrtToddComp_two (hK3 : IsK3 V) :
    V.ring.degree (V.sqrtToddComp 2) = 1 := by
  show V.ring.degree (algebraMap ℚ A (1 / 2) * V.toddComp 2
    - algebraMap ℚ A (1 / 8) * (V.toddComp 1 * V.toddComp 1)) = 1
  rw [hK3.toddComp_one, mul_zero, mul_zero, sub_zero,
    NumericalRingData.degree_algebraMap_mul, hK3.degree_toddComp_two]
  norm_num

end K3

end AlgebraicGeometry.Numerical
