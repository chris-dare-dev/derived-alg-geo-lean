/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.Continuous
import Mathlib.Tactic

/-!
# Coercivity and level-set bounds for positive-definite quadratic forms

A positive-definite quadratic form on a finite-dimensional real normed space
dominates a positive multiple of the squared norm.  Its level sets are
therefore bounded.  The returned coercivity constant is useful to consumers
that need uniform quantitative bounds.
-/

open Bornology QuadraticMap

namespace QuadraticMap

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

/-- A positive definite form on a finite-dimensional real space is coercive. -/
theorem PosDef.exists_pos_mul_norm_sq_le {Q : QuadraticForm ℝ M} (hQ : Q.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : M, c * ‖x‖ ^ 2 ≤ Q x := by
  rcases subsingleton_or_nontrivial M with _ | _
  · refine ⟨1, one_pos, fun x => ?_⟩
    rw [Subsingleton.elim x 0]
    simp
  · obtain ⟨x₀, hx₀, hmin⟩ :=
      (isCompact_sphere (0 : M) 1).exists_isMinOn (NormedSpace.sphere_nonempty.mpr zero_le_one)
        (continuous_of_finiteDimensional Q).continuousOn
    have hx₀0 : x₀ ≠ 0 := by
      intro h
      rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hx₀
      exact zero_ne_one hx₀
    refine ⟨Q x₀, hQ x₀ hx₀0, fun x => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hnx : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
      have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : M) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
        field_simp
      have hkey : Q x₀ ≤ (‖x‖⁻¹ * ‖x‖⁻¹) * Q x := by
        have h := isMinOn_iff.mp hmin _ hmem
        rwa [QuadraticMap.map_smul, smul_eq_mul] at h
      have h2 := mul_le_mul_of_nonneg_right hkey (sq_nonneg ‖x‖)
      rwa [show (‖x‖⁻¹ * ‖x‖⁻¹) * Q x * ‖x‖ ^ 2 = Q x by field_simp] at h2

/-- A positive definite form has bounded level sets. -/
theorem PosDef.isBounded_setOf_eq {Q : QuadraticForm ℝ M} (hQ : Q.PosDef) (r : ℝ) :
    IsBounded {x : M | Q x = r} := by
  obtain ⟨c, hc, hle⟩ := hQ.exists_pos_mul_norm_sq_le
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt (r / c), fun x hx => ?_⟩
  have h := hle x
  rw [Set.mem_setOf_eq] at hx
  rw [hx] at h
  have hr : 0 ≤ r := le_trans (mul_nonneg hc.le (sq_nonneg _)) h
  have hsq : ‖x‖ ^ 2 ≤ r / c := by
    rw [le_div_iff₀ hc]
    linarith
  exact (Real.le_sqrt (norm_nonneg x) (div_nonneg hr hc.le)).mpr hsq

end QuadraticMap
