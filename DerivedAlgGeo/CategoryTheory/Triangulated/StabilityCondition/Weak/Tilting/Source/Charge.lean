/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.PreStability
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.SourceSlope

/-!
# The source central charge of Proposition 14.16

The phase-tilt implementation rotates a charge by the unit complex number
`exp (-pi * slopeCutPhase b * I)`.  Proposition 14.16 is instead stated with
the charge

`Z_b = Z / (I - b)`.

These differ by the positive real factor `1 / sqrt (1 + b^2)`.  This file
proves that identity exactly and packages the resulting weak prestability
condition with the source-facing charge, rather than merely an equivalent
unit rotation.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {V : Type*} [NormedAddCommGroup V]
variable {v : K₀ C →+ V}

namespace WeakPreStabilityCondition

/-- The positive scale relating the source charge to the unit phase
rotation. -/
noncomputable def sourceTiltScale (b : ℝ) : ℝ :=
  (Real.sqrt (1 + b ^ 2))⁻¹

theorem sourceTiltScale_pos (b : ℝ) : 0 < sourceTiltScale b := by
  exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

/-- The exact analytic normalization behind Proposition 14.16:
`1 / (i-b)` is a positive rescaling of the unit rotation through the phase
corresponding to slope `b`. -/
theorem sourceTilt_multiplier (b : ℝ) :
    ((Complex.I - (b : ℂ))⁻¹) =
      (sourceTiltScale b : ℂ) *
        Complex.exp (-(Real.pi * slopeCutPhase b : ℂ) * Complex.I) := by
  let s : ℝ := Real.sqrt (1 + b ^ 2)
  have hden : 0 < 1 + b ^ 2 := by positivity
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs_sq : s ^ 2 = 1 + b ^ 2 := Real.sq_sqrt (by positivity)
  dsimp [s] at hspos hs_sq
  have hangle : Real.pi * slopeCutPhase b =
      Real.arctan b + Real.pi / 2 := by
    rw [slopeCutPhase, weakPhaseOfSlope_coe]
    field_simp [Real.pi_ne_zero]
  have hexp :
      Complex.exp (-(Real.pi * slopeCutPhase b : ℂ) * Complex.I) =
        Complex.exp
          (((-(Real.pi * slopeCutPhase b) : ℝ) : ℂ) * Complex.I) := by
    congr 2
    push_cast
    ring
  simp only [sourceTiltScale]
  rw [hexp, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · simp only [Complex.inv_re, Complex.sub_re, Complex.I_re,
      Complex.ofReal_re, zero_sub, Complex.normSq_apply,
      Complex.sub_im, Complex.I_im, Complex.ofReal_im, sub_zero,
      Complex.mul_re, Complex.add_re,
      Complex.add_im, Complex.mul_im, mul_zero, sub_zero,
      add_zero, mul_one]
    rw [Real.cos_neg, hangle, Real.cos_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Real.sin_arctan]
    simp only [mul_zero]
    field_simp [hspos.ne', hden.ne']
    ring_nf
    rw [hs_sq] at *
    nlinarith [hs_sq]
  · simp only [Complex.inv_im, Complex.sub_im, Complex.I_im,
      Complex.ofReal_im, sub_zero, Complex.normSq_apply,
      Complex.sub_re, Complex.I_re, Complex.ofReal_re, zero_sub,
      Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, mul_zero, zero_mul, add_zero,
      mul_one]
    rw [Real.sin_neg, hangle, Real.sin_add, Real.cos_pi_div_two,
      Real.sin_pi_div_two, Real.cos_arctan]
    simp only [mul_zero]
    field_simp [hspos.ne', hden.ne']
    ring_nf
    rw [hs_sq] at *
    nlinarith [hs_sq]

/-- Division by `I-b`, as an additive endomorphism of the complex plane. -/
noncomputable def sourceTiltRotation (b : ℝ) : ℂ →+ ℂ where
  toFun z := z / (Complex.I - (b : ℂ))
  map_zero' := by simp
  map_add' z w := by rw [add_div]

@[simp]
theorem sourceTiltRotation_apply (b : ℝ) (z : ℂ) :
    sourceTiltRotation b z = z / (Complex.I - (b : ℂ)) := rfl

/-- Source division is the phase rotation followed by its positive real
normalization. -/
theorem sourceTiltRotation_eq_scale_phaseTiltRotation (b : ℝ) (z : ℂ) :
    sourceTiltRotation b z =
      (sourceTiltScale b : ℂ) * phaseTiltRotation (slopeCutPhase b) z := by
  rw [sourceTiltRotation_apply, div_eq_mul_inv, sourceTilt_multiplier,
    phaseTiltRotation_apply]
  ring

/-- The lattice-level central charge `Z/(I-b)` from Proposition 14.16. -/
noncomputable def sourceTiltLatticeCharge
    (sigma : WeakPreStabilityCondition v) (b : ℝ) : V →+ ℂ :=
  (sourceTiltRotation b).comp sigma.Z

omit [IsTriangulated C] in
@[simp]
theorem sourceTiltLatticeCharge_apply
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (x : V) :
    sigma.sourceTiltLatticeCharge b x =
      sigma.Z x / (Complex.I - (b : ℂ)) := rfl

omit [IsTriangulated C] in
theorem sourceTiltLatticeCharge_eq_scale_phaseTiltLatticeCharge
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (x : V) :
    sigma.sourceTiltLatticeCharge b x =
      (sourceTiltScale b : ℂ) *
        sigma.phaseTiltLatticeCharge (slopeCutPhase b) x := by
  exact sourceTiltRotation_eq_scale_phaseTiltRotation b (sigma.Z x)

/-- The source charge on the ambient Grothendieck group. -/
noncomputable def sourceTiltCharge
    (sigma : WeakPreStabilityCondition v) (b : ℝ) : K₀ C →+ ℂ :=
  (sourceTiltRotation b).comp (sigma.Z.comp v)

omit [IsTriangulated C] in
@[simp]
theorem sourceTiltCharge_apply
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    sigma.sourceTiltCharge b (K₀.of C E) =
      sigma.Z (v (K₀.of C E)) / (Complex.I - (b : ℂ)) := rfl

omit [IsTriangulated C] in
theorem sourceTiltCharge_eq_scale_phaseTiltCharge
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    sigma.sourceTiltCharge b (K₀.of C E) =
      (sourceTiltScale b : ℂ) *
        sigma.phaseTiltCharge (slopeCutPhase b) (K₀.of C E) := by
  exact sourceTiltRotation_eq_scale_phaseTiltRotation b
    (sigma.Z (v (K₀.of C E)))

/-- The weak stability function on the source tilted heart with the exact
charge `Z/(I-b)`. -/
noncomputable def sourceTiltWeakStabilityFunction
    (sigma : WeakPreStabilityCondition v) (b : ℝ) :
    WeakStabilityFunction (sigma.slopeTorsionPair b).tilt where
  Z := sigma.sourceTiltCharge b
  nonzero_mem E hmem := by
    obtain ⟨hE, _⟩ := hmem
    show 0 < ((sigma.sourceTiltCharge b) (K₀.of C E)).im ∨
      (((sigma.sourceTiltCharge b) (K₀.of C E)).im = 0 ∧
        ((sigma.sourceTiltCharge b) (K₀.of C E)).re ≤ 0)
    let theta := slopeCutPhase b
    let c := sourceTiltScale b
    let W := sigma.phaseTiltWeakStabilityFunction theta
      (slopeCutPhase_mem_Ioo b).1.le (slopeCutPhase_mem_Ioo b).2
    have hc : 0 < c := sourceTiltScale_pos b
    have hrel : sigma.sourceTiltCharge b (K₀.of C E) =
        (c : ℂ) * W.charge E := by
      simpa [W, theta] using sigma.sourceTiltCharge_eq_scale_phaseTiltCharge b E
    have hE' :
        ((slicingTorsionPair sigma.slicing
          (slopeCutPhase_mem_Ioo b).1.le
          (slopeCutPhase_mem_Ioo b).2.le).tilt).heart E := by
      simpa [W, slopeTorsionPair, theta] using hE
    rcases W.upper E hE' (by assumption) with him | ⟨him, hre⟩
    · left
      rw [hrel]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      exact mul_pos hc him
    · right
      rw [hrel]
      constructor
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, him, mul_zero]
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        exact mul_nonpos_of_nonneg_of_nonpos hc.le hre

@[simp]
theorem sourceTiltWeakStabilityFunction_Z
    (sigma : WeakPreStabilityCondition v) (b : ℝ) :
    (sigma.sourceTiltWeakStabilityFunction b).Z = sigma.sourceTiltCharge b := rfl

@[simp]
theorem sourceTiltWeakStabilityFunction_charge
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    (sigma.sourceTiltWeakStabilityFunction b).charge E =
      sigma.Z (v (K₀.of C E)) / (Complex.I - (b : ℂ)) := rfl

theorem sourceTiltWeakStabilityFunction_charge_eq_scale_phaseTilt
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    (sigma.sourceTiltWeakStabilityFunction b).charge E =
      (sourceTiltScale b : ℂ) *
        (sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
          (slopeCutPhase_mem_Ioo b).1.le
          (slopeCutPhase_mem_Ioo b).2).charge E := by
  exact sigma.sourceTiltCharge_eq_scale_phaseTiltCharge b E

theorem sourceTiltWeakStabilityFunction_slope_eq_phaseTilt
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    (sigma.sourceTiltWeakStabilityFunction b).slope E =
      (sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
        (slopeCutPhase_mem_Ioo b).1.le
        (slopeCutPhase_mem_Ioo b).2).slope E := by
  let Ws := sigma.sourceTiltWeakStabilityFunction b
  let Wp := sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
    (slopeCutPhase_mem_Ioo b).1.le (slopeCutPhase_mem_Ioo b).2
  let c := sourceTiltScale b
  have hc : 0 < c := sourceTiltScale_pos b
  have hrel : Ws.charge E = (c : ℂ) * Wp.charge E := by
    simpa [Ws, Wp, c] using
      sigma.sourceTiltWeakStabilityFunction_charge_eq_scale_phaseTilt b E
  by_cases him : 0 < (Wp.charge E).im
  · have hims : 0 < (Ws.charge E).im := by
      rw [hrel]
      simpa using mul_pos hc him
    rw [Ws.slope_of_im_pos hims, Wp.slope_of_im_pos him]
    simp only [hrel, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    congr 1
    field_simp [hc.ne']
  · have himp : (Wp.charge E).im ≤ 0 := le_of_not_gt him
    have hims : ¬0 < (Ws.charge E).im := by
      rw [hrel]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hc.le himp)
    rw [Ws.slope_of_im_nonpos hims, Wp.slope_of_im_nonpos him]

theorem sourceTiltWeakStabilityFunction_isSemistable_iff_phaseTilt
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    (sigma.sourceTiltWeakStabilityFunction b).IsSemistable E ↔
      (sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
        (slopeCutPhase_mem_Ioo b).1.le
        (slopeCutPhase_mem_Ioo b).2).IsSemistable E := by
  constructor <;> intro hE
  · refine ⟨by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hE.1, ?_⟩
    intro A B hA hB hA0 hB0 f g d hdist
    rw [← sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt b A,
      ← sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt b B]
    exact hE.2 (by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hA)
      (by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hB)
      hA0 hB0 f g d hdist
  · refine ⟨by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hE.1, ?_⟩
    intro A B hA hB hA0 hB0 f g d hdist
    rw [sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt b A,
      sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt b B]
    exact hE.2 (by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hA)
      (by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hB)
      hA0 hB0 f g d hdist

theorem sourceTiltWeakStabilityFunction_isStable_iff_phaseTilt
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    (sigma.sourceTiltWeakStabilityFunction b).IsStable E ↔
      (sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
        (slopeCutPhase_mem_Ioo b).1.le
        (slopeCutPhase_mem_Ioo b).2).IsStable E := by
  constructor <;> intro hE
  · refine ⟨by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hE.1, ?_⟩
    intro A B hA hB hA0 hB0 f g d hdist
    rw [← sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt b A,
      ← sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt b B]
    exact hE.2 (by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hA)
      (by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hB)
      hA0 hB0 f g d hdist
  · refine ⟨by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hE.1, ?_⟩
    intro A B hA hB hA0 hB0 f g d hdist
    rw [sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt b A,
      sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt b B]
    exact hE.2 (by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hA)
      (by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hB)
      hA0 hB0 f g d hdist

theorem sourceTiltWeakStabilityFunction_zeroCharge_iff
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    (sigma.sourceTiltWeakStabilityFunction b).zeroCharge E ↔
      (sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
        (slopeCutPhase_mem_Ioo b).1.le
        (slopeCutPhase_mem_Ioo b).2).zeroCharge E := by
  let c := sourceTiltScale b
  have hc : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sourceTiltScale_pos b).ne'
  constructor
  · rintro ⟨hheart, hcharge⟩
    refine ⟨by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hheart, ?_⟩
    have hrel := sigma.sourceTiltWeakStabilityFunction_charge_eq_scale_phaseTilt b E
    rw [hrel, mul_eq_zero] at hcharge
    exact hcharge.resolve_left hc
  · rintro ⟨hheart, hcharge⟩
    refine ⟨by simpa [sourceTiltWeakStabilityFunction, slopeTorsionPair] using hheart, ?_⟩
    rw [sigma.sourceTiltWeakStabilityFunction_charge_eq_scale_phaseTilt b E,
      hcharge, mul_zero]

/-- Positive rescaling preserves the integer-normalized ambient phase
family, not just heart semistability. -/
theorem sourceTiltWeakStabilityFunction_ambientPhasePredicate_eq_phaseTilt
    (sigma : WeakPreStabilityCondition v) (b : ℝ) :
    WeakStabilityFunction.ambientPhasePredicate
        (sigma.sourceTiltWeakStabilityFunction b) =
      WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
          (slopeCutPhase_mem_Ioo b).1.le
          (slopeCutPhase_mem_Ioo b).2) := by
  funext phi E
  apply propext
  change IsZero E ∨
      ((sigma.sourceTiltWeakStabilityFunction b).IsSemistable
          (E⟦(-phaseIndex phi : ℤ)⟧) ∧
        (sigma.sourceTiltWeakStabilityFunction b).phase
          (E⟦(-phaseIndex phi : ℤ)⟧) = phaseBase phi) ↔
    IsZero E ∨
      ((sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
          (slopeCutPhase_mem_Ioo b).1.le
          (slopeCutPhase_mem_Ioo b).2).IsSemistable
            (E⟦(-phaseIndex phi : ℤ)⟧) ∧
        (sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
          (slopeCutPhase_mem_Ioo b).1.le
          (slopeCutPhase_mem_Ioo b).2).phase
            (E⟦(-phaseIndex phi : ℤ)⟧) = phaseBase phi)
  constructor
  · rintro (hzero | ⟨hss, hphase⟩)
    · exact Or.inl hzero
    · right
      refine ⟨(sigma.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseTilt
        b _).mp hss, ?_⟩
      rw [← hphase]
      unfold WeakStabilityFunction.phase
      rw [sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt]
  · rintro (hzero | ⟨hss, hphase⟩)
    · exact Or.inl hzero
    · right
      refine ⟨(sigma.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseTilt
        b _).mpr hss, ?_⟩
      rw [← hphase]
      unfold WeakStabilityFunction.phase
      rw [sigma.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt]

/-- The weak upper tilt with the exact source charge `Z/(I-b)`.  Its slicing
is unchanged from the phase-tilt construction because the two charges differ
by a positive real scale. -/
noncomputable def sourceTiltWeakPreStabilityConditionOfTiltingProperty
    (sigma : WeakPreStabilityCondition v) (b : ℝ)
    (htilt : sigma.TiltingProperty) : WeakPreStabilityCondition v := by
  let theta := slopeCutPhase b
  have htheta := slopeCutPhase_mem_Ioo b
  let tau := sigma.phaseTiltWeakPreStabilityConditionOfTiltingProperty
    theta htheta.1 htheta.2 htilt
  let c := sourceTiltScale b
  have hc : 0 < c := sourceTiltScale_pos b
  exact
    { slicing := tau.slicing
      Z := sigma.sourceTiltLatticeCharge b
      compat' := by
        intro phi E hP hE
        obtain ⟨m, hm, hm_strict, hmZ⟩ := tau.compat' phi E hP hE
        refine ⟨c * m, mul_nonneg hc.le hm, ?_, ?_⟩
        · intro hn
          exact mul_pos hc (hm_strict hn)
        · have hsource :=
            sigma.sourceTiltLatticeCharge_eq_scale_phaseTiltLatticeCharge b
              (v (K₀.of C E))
          have htau : tau.Z = sigma.phaseTiltLatticeCharge theta := by
            exact sigma.phaseTiltWeakPreStabilityConditionOfTiltingProperty_Z
              theta htheta.1 htheta.2 htilt
          rw [hsource, ← htau, hmZ]
          push_cast
          ring }

@[simp]
theorem sourceTiltWeakPreStabilityConditionOfTiltingProperty_Z
    (sigma : WeakPreStabilityCondition v) (b : ℝ)
    (htilt : sigma.TiltingProperty) :
    (sigma.sourceTiltWeakPreStabilityConditionOfTiltingProperty b htilt).Z =
      sigma.sourceTiltLatticeCharge b := rfl

@[simp]
theorem sourceTiltWeakPreStabilityConditionOfTiltingProperty_P
    (sigma : WeakPreStabilityCondition v) (b : ℝ)
    (htilt : sigma.TiltingProperty) :
    (sigma.sourceTiltWeakPreStabilityConditionOfTiltingProperty b htilt).slicing.P =
      WeakStabilityFunction.ambientPhasePredicate
        (sigma.phaseTiltWeakStabilityFunction (slopeCutPhase b)
          (slopeCutPhase_mem_Ioo b).1.le (slopeCutPhase_mem_Ioo b).2) := rfl

/-- The slicing of the exact source-normalized weak condition is the ambient
phase family of its exact tilted heart function. -/
theorem sourceTiltWeakPreStabilityConditionOfTiltingProperty_P_source
    (sigma : WeakPreStabilityCondition v) (b : ℝ)
    (htilt : sigma.TiltingProperty) :
    (sigma.sourceTiltWeakPreStabilityConditionOfTiltingProperty b htilt).slicing.P =
      WeakStabilityFunction.ambientPhasePredicate
        (sigma.sourceTiltWeakStabilityFunction b) := by
  rw [sourceTiltWeakPreStabilityConditionOfTiltingProperty_P]
  exact (sigma.sourceTiltWeakStabilityFunction_ambientPhasePredicate_eq_phaseTilt b).symm

end WeakPreStabilityCondition

end

end CategoryTheory.Triangulated.WeakStabilityCondition
