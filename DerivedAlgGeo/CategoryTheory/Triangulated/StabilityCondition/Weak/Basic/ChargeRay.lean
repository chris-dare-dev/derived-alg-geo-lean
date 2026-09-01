/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Heart.EquivalenceReverse

/-!
# Charge rays from normalized weak slopes

This module proves the analytic compatibility omitted from the reverse weak
heart--slicing construction.  The normalization

`weakPhaseOfSlope μ = arctan μ / π + 1 / 2`

puts every weak upper-half-plane charge on its corresponding phase ray.  The
finite-slope case has positive radius.  At the infinite-slope boundary the
charge lies on the nonpositive real axis and the radius may vanish, exactly
as allowed at integer phases by `WeakPreStabilityCondition`.

The heart-level identity is then transported through arbitrary integer
shifts.  This supplies charge-ray compatibility for the ambient phase family
constructed from any weak stability function, independently of tilting.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

/-- A complex number in the open upper half-plane lies on the ray determined
by its normalized weak slope, with positive radius. -/
theorem complex_eq_pos_mul_exp_weakPhaseOfSlope (z : ℂ) (him : 0 < z.im) :
    ∃ m : ℝ, 0 < m ∧
      z = (m : ℂ) * Complex.exp
        ((Real.pi * weakPhaseOfSlope
          ((-z.re / z.im : ℝ) : WithTop ℝ) : ℂ) * Complex.I) := by
  let mu : ℝ := -z.re / z.im
  let s : ℝ := Real.sqrt (1 + mu ^ 2)
  let m : ℝ := z.im * s
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hmpos : 0 < m := mul_pos him hspos
  refine ⟨m, hmpos, ?_⟩
  rw [weakPhaseOfSlope_coe]
  have hangle : Real.pi * (Real.arctan mu / Real.pi + 1 / 2) =
      Real.arctan mu + Real.pi / 2 := by
    field_simp [ne_of_gt Real.pi_pos]
  rw [show -z.re / z.im = mu by rfl, ← Complex.ofReal_mul, hangle,
    Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one]
    rw [Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Real.sin_arctan]
    dsimp [m, s, mu]
    have hsne : Real.sqrt (1 + (-z.re / z.im) ^ 2) ≠ 0 := by positivity
    field_simp [ne_of_gt him, hsne]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      add_zero, mul_one]
    rw [Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two,
      Real.cos_arctan]
    dsimp [m, s, mu]
    have hsne : Real.sqrt (1 + (-z.re / z.im) ^ 2) ≠ 0 := by positivity
    field_simp [ne_of_gt him, hsne]
    ring

omit [IsTriangulated C] in
/-- The charge of every nonzero heart object lies on the ray determined by
its normalized weak phase.  The radius is positive away from integer phases;
at the phase-`1` boundary it is merely nonnegative. -/
theorem WeakStabilityFunction.charge_ray_of_mem_heart
    {t : TStructure C} (W : WeakStabilityFunction t) (E : C)
    (hEheart : t.heart E) (hE0 : ¬IsZero E) :
    ∃ m : ℝ, 0 ≤ m ∧
      ((∀ n : ℤ, W.phase E ≠ (n : ℝ)) → 0 < m) ∧
      W.charge E = (m : ℂ) *
        Complex.exp ((Real.pi * W.phase E : ℂ) * Complex.I) := by
  rcases W.upper E hEheart hE0 with him | ⟨him, hre⟩
  · obtain ⟨m, hm, hcharge⟩ :=
      complex_eq_pos_mul_exp_weakPhaseOfSlope (W.charge E) him
    refine ⟨m, hm.le, fun _ ↦ hm, ?_⟩
    rw [WeakStabilityFunction.phase, W.slope_of_im_pos him]
    exact hcharge
  · refine ⟨-(W.charge E).re, neg_nonneg.mpr hre, ?_, ?_⟩
    · intro hnotint
      exfalso
      apply hnotint 1
      rw [WeakStabilityFunction.phase, W.slope_of_im_nonpos (by simp [him])]
      simp
    · rw [WeakStabilityFunction.phase, W.slope_of_im_nonpos (by simp [him]),
        weakPhaseOfSlope_top]
      norm_num
      apply Complex.ext <;> simp [him]

/-- Multiplication by the shift-parity sign advances a phase ray by the
corresponding integer. -/
theorem negOnePow_mul_exp_pi_eq_exp_add_int (psi : ℝ) (n : ℤ) :
    ((((-1 : ℤ) ^ Int.natAbs n : ℤ) : ℂ) *
        Complex.exp ((Real.pi * psi : ℂ) * Complex.I)) =
      Complex.exp ((Real.pi * (psi + (n : ℝ)) : ℂ) * Complex.I) := by
  push_cast
  rw [← Int.coe_negOnePow ℂ, Int.cast_negOnePow]
  have hexp : Complex.exp ((n : ℂ) * ((Real.pi : ℂ) * Complex.I)) =
      Complex.exp ((Real.pi : ℂ) * Complex.I) ^ n :=
    Complex.exp_int_mul ((Real.pi : ℂ) * Complex.I) n
  rw [Complex.exp_pi_mul_I] at hexp
  calc
    (-1 : ℂ) ^ n * Complex.exp ((Real.pi * psi : ℂ) * Complex.I) =
        Complex.exp (((n : ℂ) * (Real.pi : ℂ)) * Complex.I) *
          Complex.exp ((Real.pi * psi : ℂ) * Complex.I) := by
            rw [← hexp]
            congr 2
            ring
    _ = Complex.exp ((((n : ℂ) * (Real.pi : ℂ)) * Complex.I) +
          ((Real.pi * psi : ℂ) * Complex.I)) := by rw [Complex.exp_add]
    _ = Complex.exp ((Real.pi * (psi + (n : ℝ)) : ℂ) * Complex.I) := by
      congr 1
      push_cast
      ring

omit [IsTriangulated C] in
/-- The integer-normalized ambient phase predicate constructed from a weak
stability function satisfies the charge-ray axiom of a weak prestability
condition. -/
theorem WeakStabilityFunction.ambientPhasePredicate_charge_ray
    {t : TStructure C} (W : WeakStabilityFunction t)
    (phi : ℝ) (E : C) (hP : W.ambientPhasePredicate phi E)
    (hE0 : ¬IsZero E) :
    ∃ m : ℝ, 0 ≤ m ∧
      ((∀ n : ℤ, phi ≠ (n : ℝ)) → 0 < m) ∧
      W.charge E = (m : ℂ) *
        Complex.exp ((Real.pi * phi : ℂ) * Complex.I) := by
  let n : ℤ := phaseIndex phi
  let psi : ℝ := phaseBase phi
  let H : C := E⟦(-n : ℤ)⟧
  have hshifted : W.shiftedHeartPhasePredicate psi n E := by
    simpa [WeakStabilityFunction.ambientPhasePredicate, psi, n] using hP
  rcases hshifted with hEzero | ⟨hHss, hHphase⟩
  · exact False.elim (hE0 hEzero)
  · let e : H⟦n⟧ ≅ E :=
      (shiftFunctorCompIsoId C (-n : ℤ) n (by simp)).app E
    have hH0 : ¬IsZero H := by
      intro hHzero
      apply hE0
      exact ((shiftFunctor C n).map_isZero hHzero).of_iso e.symm
    obtain ⟨m, hm, hmpos, hHcharge⟩ :=
      W.charge_ray_of_mem_heart H hHss.1 hH0
    refine ⟨m, hm, ?_, ?_⟩
    · intro hphiNotInt
      apply hmpos
      intro k hk
      apply hphiNotInt (k + n)
      calc
        phi = psi + (n : ℝ) := by
          simpa [psi, n] using (phaseBase_add_phaseIndex phi).symm
        _ = (k + n : ℤ) := by rw [← hHphase, hk]; push_cast; rfl
    · have hclass : K₀.of C E =
          ((-1 : ℤ) ^ Int.natAbs n) • K₀.of C H := by
        calc
          K₀.of C E = K₀.of C (H⟦n⟧) := (K₀.of_iso C e).symm
          _ = ((-1 : ℤ) ^ Int.natAbs n) • K₀.of C H :=
            CategoryTheory.Triangulated.K₀.of_shift_int C H n
      have hEcharge : W.charge E =
          ((((-1 : ℤ) ^ Int.natAbs n : ℤ) : ℂ) * W.charge H) := by
        rw [WeakStabilityFunction.charge, hclass, map_zsmul]
        push_cast
        simp [zsmul_eq_mul]
      rw [hEcharge, hHcharge, hHphase]
      calc
        ((((-1 : ℤ) ^ Int.natAbs n : ℤ) : ℂ) *
              ((m : ℂ) * Complex.exp ((Real.pi * psi : ℂ) * Complex.I))) =
            (m : ℂ) * (((((-1 : ℤ) ^ Int.natAbs n : ℤ) : ℂ) *
              Complex.exp ((Real.pi * psi : ℂ) * Complex.I))) := by ring
        _ = (m : ℂ) * Complex.exp
              ((Real.pi * (psi + (n : ℝ)) : ℂ) * Complex.I) := by
            rw [negOnePow_mul_exp_pi_eq_exp_add_int]
        _ = (m : ℂ) * Complex.exp ((Real.pi * phi : ℂ) * Complex.I) := by
          have hpsi : psi + (n : ℝ) = phi := by
            simpa [psi, n] using phaseBase_add_phaseIndex phi
          rw [← hpsi]
          push_cast
          rfl

end

end CategoryTheory.Triangulated.WeakStabilityCondition
