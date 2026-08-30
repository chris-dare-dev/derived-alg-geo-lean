/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.RelativePhase

/-!
# Phase control under near-identity perturbations

This file develops the complex-analytic estimate that converts a norm-small
relative change of central charge into a small change of its selected phase.
It is independent of categories and of the retained deformation library.
-/

noncomputable section

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

/-- The imaginary coordinate is bounded by the product of the distance from
one and the norm. -/
theorem im_sq_le_norm_sub_one_sq_mul (z : ℂ) :
    z.im ^ 2 ≤ ‖z - 1‖ ^ 2 * ‖z‖ ^ 2 := by
  rw [Complex.sq_norm (z - 1), Complex.sq_norm z]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im, sub_zero]
  nlinarith [sq_nonneg (z.re * z.re + z.im * z.im - z.re)]

/-- The sine of the argument of a nonzero complex number is controlled by
its distance from one. -/
theorem abs_sin_arg_le_norm_sub_one {z : ℂ} (hz : z ≠ 0) :
    |Real.sin (Complex.arg z)| ≤ ‖z - 1‖ := by
  rw [Complex.sin_arg, abs_div, abs_of_pos (norm_pos_iff.mpr hz),
    div_le_iff₀ (norm_pos_iff.mpr hz)]
  exact le_of_sq_le_sq
    (by rw [sq_abs, mul_pow]; exact im_sq_le_norm_sub_one_sq_mul z)
    (by positivity)

/-- On the central half-period, taking sine commutes with absolute value. -/
theorem sin_abs_eq_abs_sin {x : ℝ} (hx : |x| < Real.pi / 2) :
    Real.sin |x| = |Real.sin x| := by
  rcases le_or_gt 0 x with h | h
  · have hx' : x < Real.pi / 2 := by rwa [abs_of_nonneg h] at hx
    rw [abs_of_nonneg h, abs_of_nonneg
      (Real.sin_nonneg_of_nonneg_of_le_pi h
        (by linarith [Real.pi_pos]))]
  · have hx' : -x < Real.pi / 2 := by rwa [abs_of_neg h] at hx
    have hsin : Real.sin x < 0 := by
      have : 0 < Real.sin (-x) :=
        Real.sin_pos_of_pos_of_lt_pi (neg_pos.mpr h)
          (by linarith [Real.pi_pos])
      linarith [Real.sin_neg x]
    rw [abs_of_neg h, Real.sin_neg, abs_of_neg hsin]

/-- A perturbation smaller than `sin (π ε)` changes the argument of one by
less than `π ε`. -/
theorem abs_arg_one_add_lt {u : ℂ} {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hu : ‖u‖ < Real.sin (Real.pi * ε)) :
    |Complex.arg (1 + u)| < Real.pi * ε := by
  have hπ := Real.pi_pos
  have hπε2 : Real.pi * ε ≤ Real.pi / 2 := by nlinarith
  have hu1 : ‖u‖ < 1 := lt_of_lt_of_le hu (Real.sin_le_one _)
  have hz : (1 : ℂ) + u ≠ 0 := by
    intro h
    have hnorm : ‖(1 : ℂ)‖ = ‖u‖ := by
      rw [eq_neg_of_add_eq_zero_left h, norm_neg]
    rw [norm_one] at hnorm
    linarith
  have hre : 0 < ((1 : ℂ) + u).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith [neg_le_of_abs_le (Complex.abs_re_le_norm u)]
  have harg_lt : |Complex.arg ((1 : ℂ) + u)| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  have hsin_le :
      |Real.sin (Complex.arg ((1 : ℂ) + u))| ≤ ‖u‖ := by
    calc
      |Real.sin (Complex.arg ((1 : ℂ) + u))| ≤ ‖(1 : ℂ) + u - 1‖ :=
        abs_sin_arg_le_norm_sub_one hz
      _ = ‖u‖ := by congr 1; ring
  have hsin_abs := sin_abs_eq_abs_sin harg_lt
  by_contra h
  push Not at h
  have hmono : Real.sin (Real.pi * ε) ≤
      Real.sin |Complex.arg ((1 : ℂ) + u)| :=
    Real.monotoneOn_sin
      ⟨by linarith [mul_pos hπ hε], hπε2⟩
      ⟨by linarith [abs_nonneg (Complex.arg ((1 : ℂ) + u))],
        harg_lt.le⟩ h
  linarith

/-- A norm-small multiplicative perturbation changes the selected relative
phase by less than `ε`. -/
theorem relativePhase_perturbation {m φ α ε : ℝ} {u : ℂ}
    (hm : 0 < m) (hφ : φ ∈ Set.Ioo (α - 1 / 2) (α + 1 / 2))
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hu : ‖u‖ < Real.sin (Real.pi * ε)) :
    |relativePhase ((m : ℂ) *
      Complex.exp (↑(Real.pi * φ) * Complex.I) * ((1 : ℂ) + u)) α - φ| < ε := by
  have hπ := Real.pi_pos
  have hu1 : ‖u‖ < 1 := lt_of_lt_of_le hu (Real.sin_le_one _)
  have hz₂ : (1 : ℂ) + u ≠ 0 := by
    intro h
    have hnorm := congrArg norm (eq_neg_of_add_eq_zero_left h)
    rw [norm_neg, norm_one] at hnorm
    linarith
  have harg_u := abs_arg_one_add_lt hε hε2 hu
  have hreassoc : (m : ℂ) *
      Complex.exp (↑(Real.pi * φ) * Complex.I) * ((1 : ℂ) + u) *
        Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
      ((m : ℂ) * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I)) *
        ((1 : ℂ) + u) := by
    have hexp : Complex.exp (↑(Real.pi * φ) * Complex.I) *
        Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
        Complex.exp (↑(Real.pi * (φ - α)) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    calc
      (m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I) *
          ((1 : ℂ) + u) * Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
        (m : ℂ) * (Complex.exp (↑(Real.pi * φ) * Complex.I) *
          Complex.exp (-(↑(Real.pi * α) * Complex.I))) * ((1 : ℂ) + u) := by
            ring
      _ = _ := by rw [hexp]
  let z₁ := (m : ℂ) * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I)
  let z₂ := (1 : ℂ) + u
  have hz₁ : z₁ ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hm.ne') (Complex.exp_ne_zero _)
  have harg₁ : Complex.arg z₁ = Real.pi * (φ - α) := by
    rw [Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I, toIocMod_eq_self]
    have hlower : (0 : ℝ) < 1 + (φ - α) := by linarith [hφ.1]
    have hupper : (0 : ℝ) < 1 - (φ - α) := by linarith [hφ.2]
    exact ⟨by linarith [mul_pos hπ hlower],
      by linarith [mul_pos hπ hupper]⟩
  have hsum_mem : Complex.arg z₁ + Complex.arg z₂ ∈
      Set.Ioc (-Real.pi) Real.pi := by
    rw [harg₁]
    obtain ⟨h₁, h₂⟩ := abs_lt.mp harg_u
    exact ⟨by nlinarith [hφ.1], by nlinarith [hφ.2]⟩
  unfold relativePhase
  rw [hreassoc, Complex.arg_mul hz₁ hz₂ hsum_mem, harg₁,
    show α + (Real.pi * (φ - α) + Complex.arg z₂) / Real.pi - φ =
      Complex.arg z₂ / Real.pi by field_simp; ring,
    abs_div, abs_of_pos hπ, div_lt_iff₀ hπ]
  linarith

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation
