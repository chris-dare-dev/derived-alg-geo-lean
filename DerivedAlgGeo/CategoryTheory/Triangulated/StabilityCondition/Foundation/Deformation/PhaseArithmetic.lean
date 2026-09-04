/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.RelativePhase

/-!
# Relative-phase arithmetic

This module develops the rotated imaginary-part calculations behind the
phase see-saw argument.  It is purely analytic: later categorical deformation
modules can use these results through the repository-owned foundation.
-/

noncomputable section

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

/-- The imaginary part of a complex number after rotating phase `ψ` to the
real axis. -/
def rotatedIm (w : ℂ) (ψ : ℝ) : ℝ :=
  (w * Complex.exp (-(↑(Real.pi * ψ) * Complex.I))).im

/-- Rotating a polar vector subtracts its phases inside the sine. -/
theorem rotatedIm_polar (m φ ψ : ℝ) :
    rotatedIm ((m : ℂ) *
      Complex.exp (↑(Real.pi * φ) * Complex.I)) ψ =
      m * Real.sin (Real.pi * (φ - ψ)) := by
  unfold rotatedIm
  rw [mul_assoc, ← Complex.exp_add,
    show ↑(Real.pi * φ) * Complex.I +
        -(↑(Real.pi * ψ) * Complex.I) =
      ↑(Real.pi * (φ - ψ)) * Complex.I by push_cast; ring,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    zero_mul, add_zero]

/-- Rotated imaginary part expressed through the selected relative phase. -/
theorem rotatedIm_eq_norm_mul_sin (w : ℂ) (α ψ : ℝ) :
    rotatedIm w ψ =
      ‖w‖ * Real.sin (Real.pi * (relativePhase w α - ψ)) := by
  conv_lhs => rw [relativePhase_polar w α]
  exact rotatedIm_polar ‖w‖ (relativePhase w α) ψ

/-- A vector has zero rotated imaginary part at its selected phase. -/
theorem rotatedIm_eq_zero_of_relativePhase_eq {w : ℂ} {α ψ : ℝ}
    (h : relativePhase w α = ψ) : rotatedIm w ψ = 0 := by
  rw [rotatedIm_eq_norm_mul_sin w α ψ, h, sub_self, mul_zero,
    Real.sin_zero, mul_zero]

/-- A nonzero vector whose selected phase lies strictly below the rotation
phase by less than one has negative rotated imaginary part. -/
theorem rotatedIm_neg_of_relativePhase_lt {w : ℂ} {α ψ : ℝ}
    (hw : w ≠ 0) (hlo : ψ - 1 < relativePhase w α)
    (hlt : relativePhase w α < ψ) : rotatedIm w ψ < 0 := by
  rw [rotatedIm_eq_norm_mul_sin w α ψ]
  apply mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw)
  apply Real.sin_neg_of_neg_of_neg_pi_lt
  · nlinarith [Real.pi_pos, hlt]
  · nlinarith [Real.pi_pos, hlo]

/-- A nonzero vector whose selected phase lies strictly above the rotation
phase by less than one has positive rotated imaginary part. -/
theorem rotatedIm_pos_of_relativePhase_gt {w : ℂ} {α ψ : ℝ}
    (hw : w ≠ 0) (hgt : ψ < relativePhase w α)
    (hhi : relativePhase w α < ψ + 1) : 0 < rotatedIm w ψ := by
  rw [rotatedIm_eq_norm_mul_sin w α ψ]
  apply mul_pos (norm_pos_iff.mpr hw)
  apply Real.sin_pos_of_pos_of_lt_pi
  · nlinarith [Real.pi_pos, hgt]
  · nlinarith [Real.pi_pos, hhi]

/-- Positive rotated imaginary part forces a relative phase above the rotation
phase, provided the selected branch does not wrap around it. -/
theorem relativePhase_gt_of_rotatedIm_pos {w : ℂ} {α ψ : ℝ}
    (him : 0 < rotatedIm w ψ)
    (hrange : relativePhase w α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ < relativePhase w α := by
  by_contra h
  push Not at h
  have hd : relativePhase w α - ψ ∈ Set.Ioc (-1) 0 :=
    ⟨by linarith [hrange.1], by linarith⟩
  have hsin : Real.sin (Real.pi * (relativePhase w α - ψ)) ≤ 0 :=
    Real.sin_nonpos_of_nonpos_of_neg_pi_le
      (by nlinarith [Real.pi_pos, hd.2])
      (by nlinarith [Real.pi_pos, hd.1])
  rw [rotatedIm_eq_norm_mul_sin w α ψ] at him
  linarith [mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w) hsin]

/-- Negative rotated imaginary part forces a relative phase below the rotation
phase on the same branch window. -/
theorem relativePhase_lt_of_rotatedIm_neg {w : ℂ} {α ψ : ℝ}
    (him : rotatedIm w ψ < 0)
    (hrange : relativePhase w α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    relativePhase w α < ψ := by
  by_contra h
  push Not at h
  have hd : relativePhase w α - ψ ∈ Set.Ico 0 1 :=
    ⟨by linarith, by linarith [hrange.2]⟩
  have hsin : 0 ≤ Real.sin (Real.pi * (relativePhase w α - ψ)) :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos, hd.1])
      (by nlinarith [Real.pi_pos, hd.2])
  rw [rotatedIm_eq_norm_mul_sin w α ψ] at him
  linarith [mul_nonneg (norm_nonneg w) hsin]

/-- Phase see-saw: if a total vector has phase `ψ` and the first summand is at
most `ψ`, then a nonzero second summand on the same branch is at least `ψ`. -/
theorem relativePhase_seesaw {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hψ : relativePhase w α = ψ)
    (hw₁_range : relativePhase w₁ α ∈ Set.Ioc (ψ - 1) ψ)
    (hw₂_ne : w₂ ≠ 0)
    (hw₂_range : relativePhase w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ ≤ relativePhase w₂ α := by
  by_contra h
  push Not at h
  have him_w : rotatedIm w ψ = 0 :=
    rotatedIm_eq_zero_of_relativePhase_eq hψ
  have him_w₁ : rotatedIm w₁ ψ ≤ 0 := by
    rw [rotatedIm_eq_norm_mul_sin w₁ α ψ]
    exact mul_nonpos_of_nonneg_of_nonpos (norm_nonneg w₁)
      (Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (by nlinarith [Real.pi_pos, hw₁_range.2])
        (by nlinarith [Real.pi_pos, hw₁_range.1]))
  have him_w₂ : rotatedIm w₂ ψ < 0 := by
    rw [rotatedIm_eq_norm_mul_sin w₂ α ψ]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, h])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  have him_sum : rotatedIm w ψ = rotatedIm w₁ ψ + rotatedIm w₂ ψ := by
    unfold rotatedIm
    rw [← hsum, add_mul, Complex.add_im]
  linarith

/-- Strict phase see-saw: a below-phase nonzero second summand forces the first
summand strictly above the phase of the total. -/
theorem relativePhase_seesaw_strict {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hψ : relativePhase w α = ψ)
    (hw₂_lt : relativePhase w₂ α < ψ)
    (hw₂_ne : w₂ ≠ 0)
    (hw₂_range : relativePhase w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₁_range : relativePhase w₁ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ < relativePhase w₁ α := by
  have him_w : rotatedIm w ψ = 0 :=
    rotatedIm_eq_zero_of_relativePhase_eq hψ
  have him_w₂ : rotatedIm w₂ ψ < 0 := by
    rw [rotatedIm_eq_norm_mul_sin w₂ α ψ]
    exact mul_neg_of_pos_of_neg (norm_pos_iff.mpr hw₂_ne)
      (Real.sin_neg_of_neg_of_neg_pi_lt
        (by nlinarith [Real.pi_pos, hw₂_lt])
        (by nlinarith [Real.pi_pos, hw₂_range.1]))
  have him_w₁ : 0 < rotatedIm w₁ ψ := by
    have him_sum : rotatedIm w ψ = rotatedIm w₁ ψ + rotatedIm w₂ ψ := by
      unfold rotatedIm
      rw [← hsum, add_mul, Complex.add_im]
    linarith
  exact relativePhase_gt_of_rotatedIm_pos him_w₁ hw₁_range

/-- Dual strict phase see-saw: an above-phase nonzero first summand forces the
second summand strictly below the phase of the total. -/
theorem relativePhase_seesaw_dual {w w₁ w₂ : ℂ} {α ψ : ℝ}
    (hsum : w₁ + w₂ = w)
    (hψ : relativePhase w α = ψ)
    (hw₁_gt : ψ < relativePhase w₁ α)
    (hw₁_ne : w₁ ≠ 0)
    (hw₁_range : relativePhase w₁ α ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hw₂_range : relativePhase w₂ α ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    relativePhase w₂ α < ψ := by
  by_contra h
  push Not at h
  have him_w : rotatedIm w ψ = 0 :=
    rotatedIm_eq_zero_of_relativePhase_eq hψ
  have him_w₁ : 0 < rotatedIm w₁ ψ := by
    rw [rotatedIm_eq_norm_mul_sin w₁ α ψ]
    exact mul_pos (norm_pos_iff.mpr hw₁_ne)
      (Real.sin_pos_of_pos_of_lt_pi
        (by nlinarith [Real.pi_pos, hw₁_gt])
        (by nlinarith [Real.pi_pos, hw₁_range.2]))
  have him_w₂ : 0 ≤ rotatedIm w₂ ψ := by
    rw [rotatedIm_eq_norm_mul_sin w₂ α ψ]
    exact mul_nonneg (norm_nonneg w₂)
      (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos, h])
        (by nlinarith [Real.pi_pos, hw₂_range.2]))
  have him_sum : rotatedIm w ψ = rotatedIm w₁ ψ + rotatedIm w₂ ψ := by
    unfold rotatedIm
    rw [← hsum, add_mul, Complex.add_im]
  linarith

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation
