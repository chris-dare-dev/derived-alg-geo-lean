/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Exponential.Kernel

/-!
# The exponential twist on compressed degrees

`twist m β` acts on `HDeg m` by convolution with `(-β)^j / j!`.
Its group law and the identity `charge m w (twist m β d) = charge m (w + β) d`
come from the same finite exponential convolution, over the reals and complexes
respectively. The truncation degree is arbitrary and no geometric hypothesis
is needed. Comparisons with tuple and geometric presentations live downstream.
-/

open Finset

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Exp

noncomputable section

private def expCoeff {K : Type*} [Field K] (x : K) (i : ℕ) : K :=
  (-x) ^ i / (i.factorial : K)

private theorem expCoeff_add {K : Type*} [Field K] [CharZero K] (x y : K) (i : ℕ) :
    expCoeff (x + y) i =
      ∑ j ∈ range (i + 1), expCoeff x j * expCoeff y (i - j) := by
  simp only [expCoeff, neg_add, add_pow, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≤ i := by simpa using hj
  have key : (i.choose j : K) * ((j.factorial : K) * ((i - j).factorial : K)) =
      (i.factorial : K) := by
    have h := Nat.choose_mul_factorial_mul_factorial hji
    push_cast [← h]
    ring
  have h1 : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have h2 : ((i - j).factorial : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (i - j))
  have h3 : (i.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  field_simp
  linear_combination ((-x) ^ j * (-y) ^ (i - j)) * key

private def convolution {K : Type*} [Field K] (x : K) (d : ℕ → K) (i : ℕ) : K :=
  ∑ j ∈ range (i + 1), expCoeff x (i - j) * d j

private theorem convolution_convolution {K : Type*} [Field K] [CharZero K]
    (x y : K) (d : ℕ → K) (i : ℕ) :
    convolution x (convolution y d) i = convolution (x + y) d i := by
  simp only [convolution, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm' (t' := range (i + 1)) (s' := fun j => Finset.Ico j (i + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≤ i := by simpa using hj
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : i + 1 - j = i - j + 1 := by omega
  rw [hlen, expCoeff_add]
  calc
    ∑ a ∈ range (i - j + 1), expCoeff x (i - (j + a)) * expCoeff y (j + a - j) =
        ∑ a ∈ range (i - j + 1),
          (fun b => expCoeff x b * expCoeff y (i - j - b)) (i - j + 1 - 1 - a) := by
      refine Finset.sum_congr rfl fun a ha => ?_
      have ha' : a < i - j + 1 := Finset.mem_range.mp ha
      congr 2 <;> omega
    _ = _ := Finset.sum_range_reflect
      (fun b : ℕ => expCoeff x b * expCoeff y (i - j - b)) (i - j + 1)

private def degrees (m : ℕ) (d : HDeg m) (j : ℕ) : ℝ :=
  if h : j < m + 1 then d ⟨j, h⟩ else 0

/-- The truncated `e^{-βH}` action on the weighted `H`-degrees. -/
def twist (m : ℕ) (β : ℝ) (d : HDeg m) : HDeg m :=
  fun i => convolution β (degrees m d) i

/-- The component formula, with the bound carried by the summation index. -/
theorem twist_apply (m : ℕ) (β : ℝ) (d : HDeg m) (i : Fin (m + 1)) :
    twist m β d i = ∑ j : Fin (i.val + 1),
      (-β) ^ (i.val - j.val) / ((i.val - j.val).factorial : ℝ) *
        d ⟨j.val, by have := j.isLt; have := i.isLt; omega⟩ := by
  rw [twist, convolution, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  have h : j.val < m + 1 := by have := j.isLt; have := i.isLt; omega
  simp only [expCoeff, degrees, dif_pos h]

/-- The coefficientwise identity `e^{-βH} e^{-γH} = e^{-(β+γ)H}`.
The finite Vandermonde convolution involves only lower degrees, so truncation
does not discard any term needed by the group law. -/
theorem twist_twist (m : ℕ) (β γ : ℝ) (d : HDeg m) :
    twist m β (twist m γ d) = twist m (β + γ) d := by
  funext i
  change convolution β (degrees m (twist m γ d)) i =
    convolution (β + γ) (degrees m d) i
  rw [← convolution_convolution β γ (degrees m d) i]
  unfold convolution
  refine Finset.sum_congr rfl fun j hj => ?_
  have h : j < m + 1 := by have := i.isLt; simp only [Finset.mem_range] at hj; omega
  simp only [degrees, dif_pos h, twist]
  rfl

/-- The zero parameter acts as the identity. -/
@[simp] theorem twist_zero (m : ℕ) (d : HDeg m) : twist m 0 d = d := by
  funext i
  simp only [twist, convolution]
  rw [Finset.sum_eq_single i.val]
  · simp [expCoeff, degrees, i.isLt]
  · intro j hj hne
    have h : i.val - j ≠ 0 := by simp only [Finset.mem_range] at hj; omega
    simp [expCoeff, zero_pow h]
  · simp

private theorem charge_convolution (m : ℕ) (w : ℂ) (d : HDeg m) :
    charge m w d = -convolution w (fun j => (degrees m d j : ℂ)) m := by
  rw [charge_apply, ofMoments, convolution,
    ← Finset.sum_range_reflect
      (fun j => expCoeff w (m - j) * (degrees m d j : ℂ)) (m + 1)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjm : j ≤ m := by simpa using hj
  have hsub : m - (m + 1 - 1 - j) = j := by omega
  have hlt : m + 1 - 1 - j < m + 1 := by omega
  simp only [moments, dif_pos hjm, degrees, dif_pos hlt, hsub, expCoeff, coeff]
  simp only [Nat.add_sub_cancel]
  rw [neg_pow]
  ring

/-- The Cauchy product of the charge exponential and the real twist exponential.
The parameter shifts by `+β`: both exponentials carry the same negative sign.
This identity holds on the entire complex parameter plane. -/
theorem charge_twist (m : ℕ) (w : ℂ) (β : ℝ) (d : HDeg m) :
    charge m w (twist m β d) = charge m (w + β) d := by
  rw [charge_convolution, charge_convolution,
    ← convolution_convolution w (β : ℂ) (fun j => (degrees m d j : ℂ)) m]
  congr 1
  unfold convolution
  refine Finset.sum_congr rfl fun j hj => ?_
  have h : j < m + 1 := Finset.mem_range.mp hj
  simp only [degrees, dif_pos h, twist, convolution, expCoeff]
  push_cast
  rfl

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Exp
