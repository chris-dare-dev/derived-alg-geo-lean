/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.Slope

/-!
# The `β`-twisted Chern character

For a polarised variety and a rational `β`, the twisted Chern character is
`ch^β = e^{−βH}·ch`, component by component:

```
ch^β_i(E) = ∑_{j ≤ i} ((−β)^(i−j) / (i−j)!) · ch_j(E) · H^(i−j)
```

Nothing of the sort existed in the numerical layer, so the tilt slope `ν_{α,β}`
and the BMT quantity `Q_{α,β}` could not previously be written down at all.

## What makes the name honest

The exponential notation is a claim, and `twist_add_beta` is the theorem that
earns it: twisting by `β₁ + β₂` is twisting by `β₂` and then by `β₁`. That is
`e^{−(β₁+β₂)H} = e^{−β₁H}·e^{−β₂H}` read off the graded components, and it is
the only real proof in this file.

It reduces to the scalar identity `twistCoeff_add`,

```
(x + y)^m / m! = ∑_{a ≤ m} (x^a / a!) · (y^(m−a) / (m−a)!)
```

— the binomial theorem divided through by `m!` — plus a triangular reindexing of
the double sum. The reindexing is where the work is: the two sums run in
opposite directions, so a reflection (`Finset.sum_range_reflect`) sits between
them.

## Stated on a bare graded ring first

`twistCoeff` and `twist` mention no variety, no polarisation and no Chern
character: `twist` convolves an arbitrary family `c : ℕ → A` against the
exponential coefficients of an arbitrary ring element `H`. The group law is a
fact about that convolution and is proved there. `chBetaComp` is then the
specialisation at `H = P.cls` and `c = V.chComp E`, and inherits it.

This is deliberate. The group law has nothing to do with geometry, and proving
it against `NumericalVarietyData` would have hidden that behind hypotheses it
never uses.

## Main results

* `twistCoeff`, `twistCoeff_add` — the scalar exponential coefficients.
* `twist`, `twist_add_beta` — the convolution and **the group law**.
* `chBetaComp` — `ch^β_i(E)`, with `chBetaComp_mem` placing it in codimension
  `i`, `chBetaComp_add` additive in the class, `chBetaComp_zero_beta` the
  untwisted specialisation, and `chBetaComp_add_beta` the group law.
-/

open Finset

universe u v

namespace AlgebraicGeometry.Numerical

/-! ### The scalar coefficients -/

/-- The coefficient of `H^m` in `e^{−βH}`. -/
noncomputable def twistCoeff (β : ℚ) (m : ℕ) : ℚ := (-β) ^ m / m.factorial

@[simp]
theorem twistCoeff_zero_beta (m : ℕ) : twistCoeff 0 m = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · simp [twistCoeff, hm]
  · simp [twistCoeff, hm, zero_pow hm]

/-- **The exponential functional equation, at the level of coefficients.** The
binomial theorem divided through by `m!`. -/
theorem twistCoeff_add (β₁ β₂ : ℚ) (m : ℕ) :
    twistCoeff (β₁ + β₂) m
      = ∑ a ∈ range (m + 1), twistCoeff β₁ a * twistCoeff β₂ (m - a) := by
  simp only [twistCoeff]
  have hneg : -(β₁ + β₂) = (-β₁) + (-β₂) := by ring
  rw [hneg, add_pow, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ham : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have key : (m.choose a : ℚ) * ((a.factorial : ℚ) * ((m - a).factorial : ℚ))
      = (m.factorial : ℚ) := by
    have h := Nat.choose_mul_factorial_mul_factorial ham
    push_cast [← h]; ring
  have h1 : (a.factorial : ℚ) ≠ 0 := by positivity
  have h2 : ((m - a).factorial : ℚ) ≠ 0 := by positivity
  have h3 : (m.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linear_combination ((-β₁) ^ a * (-β₂) ^ (m - a)) * key

/-! ### The twist on a bare graded ring -/

variable {A : Type u} [CommRing A] [Algebra ℚ A]

/-- **Convolution against `e^{−βH}`**, for an arbitrary family `c : ℕ → A` and
an arbitrary `H : A`. No variety and no polarisation appear. -/
noncomputable def twist (H : A) (β : ℚ) (c : ℕ → A) (i : ℕ) : A :=
  ∑ j ∈ range (i + 1), algebraMap ℚ A (twistCoeff β (i - j)) * c j * H ^ (i - j)

/-- **The group law**: `e^{−(β₁+β₂)H} = e^{−β₁H}·e^{−β₂H}`, read on components.

This is what makes the exponential notation honest rather than decorative. -/
theorem twist_add_beta (H : A) (β₁ β₂ : ℚ) (c : ℕ → A) (i : ℕ) :
    twist H (β₁ + β₂) c i = twist H β₁ (twist H β₂ c) i := by
  simp only [twist]
  have expand : ∀ k ∈ range (i + 1),
      algebraMap ℚ A (twistCoeff β₁ (i - k)) * (∑ j ∈ range (k + 1),
          algebraMap ℚ A (twistCoeff β₂ (k - j)) * c j * H ^ (k - j)) * H ^ (i - k)
        = ∑ j ∈ range (k + 1),
          algebraMap ℚ A (twistCoeff β₁ (i - k) * twistCoeff β₂ (k - j))
            * c j * H ^ (i - j) := by
    intro k hk
    have hki : k ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : H ^ (k - j) * H ^ (i - k) = H ^ (i - j) := by
      rw [← pow_add]; congr 1; omega
    rw [map_mul]
    calc algebraMap ℚ A (twistCoeff β₁ (i - k))
          * (algebraMap ℚ A (twistCoeff β₂ (k - j)) * c j * H ^ (k - j)) * H ^ (i - k)
        = algebraMap ℚ A (twistCoeff β₁ (i - k)) * algebraMap ℚ A (twistCoeff β₂ (k - j))
            * c j * (H ^ (k - j) * H ^ (i - k)) := by ring
      _ = _ := by rw [hpow]
  rw [Finset.sum_congr rfl expand]
  rw [Finset.sum_comm' (t' := range (i + 1)) (s' := fun j => Finset.Ico j (i + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  -- The two inner sums run in opposite directions; this is the reflection between them.
  have hrefl : ∑ a ∈ range (i - j + 1), twistCoeff β₁ (i - j - a) * twistCoeff β₂ a
      = ∑ a ∈ range (i - j + 1), twistCoeff β₁ a * twistCoeff β₂ (i - j - a) :=
    calc ∑ a ∈ range (i - j + 1), twistCoeff β₁ (i - j - a) * twistCoeff β₂ a
        = ∑ a ∈ range (i - j + 1),
            (fun b : ℕ => twistCoeff β₁ b * twistCoeff β₂ (i - j - b))
              (i - j + 1 - 1 - a) := by
          refine Finset.sum_congr rfl fun a ha => ?_
          have hai : a < i - j + 1 := Finset.mem_range.mp ha
          simp only
          congr 2
          omega
      _ = ∑ a ∈ range (i - j + 1), twistCoeff β₁ a * twistCoeff β₂ (i - j - a) :=
          Finset.sum_range_reflect
            (fun b : ℕ => twistCoeff β₁ b * twistCoeff β₂ (i - j - b)) (i - j + 1)
  have hscalar : ∑ k ∈ Finset.Ico j (i + 1), twistCoeff β₁ (i - k) * twistCoeff β₂ (k - j)
      = twistCoeff (β₁ + β₂) (i - j) := by
    rw [twistCoeff_add β₁ β₂ (i - j), Finset.sum_Ico_eq_sum_range]
    have hlen : i + 1 - j = i - j + 1 := by omega
    rw [hlen]
    refine Eq.trans ?_ hrefl
    refine Finset.sum_congr rfl fun a ha => ?_
    have hai : a < i - j + 1 := Finset.mem_range.mp ha
    congr 2 <;> omega
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← map_sum, hscalar]

/-! ### The twisted Chern character -/

variable {N : Type v} [AddCommGroup N] {n : ℕ}
variable (V : NumericalVarietyData n A N) (P : Polarization V.ring)

/-- **The `β`-twisted Chern character** `ch^β_i(E)`. -/
noncomputable def chBetaComp (β : ℚ) (E : N) (i : ℕ) : A :=
  twist P.cls β (V.chComp E) i

theorem chBetaComp_eq (β : ℚ) (E : N) (i : ℕ) :
    chBetaComp V P β E i
      = ∑ j ∈ range (i + 1),
        algebraMap ℚ A (twistCoeff β (i - j)) * V.chComp E j * P.cls ^ (i - j) := rfl

/-- `ch^β_i(E)` lives in codimension `i`, like `ch_i(E)`: each summand is
`piece 0 · piece j · piece (i−j)`, and `j + (i−j) = i` inside the sum's range. -/
theorem chBetaComp_mem (β : ℚ) (E : N) (i : ℕ) :
    chBetaComp V P β E i ∈ V.ring.piece i := by
  rw [chBetaComp_eq]
  refine Submodule.sum_mem _ fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h0 : algebraMap ℚ A (twistCoeff β (i - j)) * V.chComp E j ∈ V.ring.piece j := by
    have := V.ring.mul_mem_piece (V.ring.algebraMap_mem_piece_zero (twistCoeff β (i - j)))
      (V.chComp_mem E j)
    simpa using this
  have := V.ring.mul_mem_piece h0 (P.pow_mem (i - j))
  rwa [Nat.add_sub_cancel' hji] at this

/-- The twisted Chern character is additive in the class, because `ch` is. -/
theorem chBetaComp_add (β : ℚ) (E F : N) (i : ℕ) :
    chBetaComp V P β (E + F) i = chBetaComp V P β E i + chBetaComp V P β F i := by
  simp only [chBetaComp_eq, V.chComp_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- At `β = 0` the twist is the identity: `ch^0 = ch`. -/
theorem chBetaComp_zero_beta (E : N) (i : ℕ) :
    chBetaComp V P 0 E i = V.chComp E i := by
  rw [chBetaComp_eq, Finset.sum_eq_single i]
  · simp
  · intro j hj hne
    have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have : i - j ≠ 0 := by omega
    simp [twistCoeff_zero_beta, this]
  · intro h
    exact absurd (Finset.self_mem_range_succ i) h

/-- **The group law on the twisted Chern character**, inherited from `twist`. -/
theorem chBetaComp_add_beta (β₁ β₂ : ℚ) (E : N) (i : ℕ) :
    chBetaComp V P (β₁ + β₂) E i = twist P.cls β₁ (chBetaComp V P β₂ E) i :=
  twist_add_beta P.cls β₁ β₂ (V.chComp E) i

end AlgebraicGeometry.Numerical
