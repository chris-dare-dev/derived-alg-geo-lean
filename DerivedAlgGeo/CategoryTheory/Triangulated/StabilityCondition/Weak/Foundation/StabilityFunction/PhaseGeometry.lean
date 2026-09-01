/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.Subobject
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Phase geometry for owner stability functions

The argument of a sum of two nonzero vectors in the semi-closed upper
half-plane lies between their arguments.  We prove this directly from the
oriented planar determinant.  The resulting phase see-saw bounds are the
analytic input for Harder--Narasimhan arguments.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex Real

universe u v

namespace CategoryTheory.Triangulated

theorem im_nonneg_of_mem_semiClosedUpperHalfPlane {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : 0 ≤ z.im := by
  rcases hz with him | ⟨him, _⟩
  · exact him.le
  · exact him.symm ▸ le_rfl

theorem add_mem_semiClosedUpperHalfPlane {z w : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane)
    (hw : w ∈ semiClosedUpperHalfPlane) :
    z + w ∈ semiClosedUpperHalfPlane := by
  have hz_im := im_nonneg_of_mem_semiClosedUpperHalfPlane hz
  have hw_im := im_nonneg_of_mem_semiClosedUpperHalfPlane hw
  by_cases hz_pos : 0 < z.im
  · exact Or.inl (by simpa using add_pos_of_pos_of_nonneg hz_pos hw_im)
  by_cases hw_pos : 0 < w.im
  · exact Or.inl (by simpa using add_pos_of_nonneg_of_pos hz_im hw_pos)
  right
  have hz_zero : z.im = 0 := le_antisymm (not_lt.mp hz_pos) hz_im
  have hw_zero : w.im = 0 := le_antisymm (not_lt.mp hw_pos) hw_im
  have hz_re : z.re < 0 := by
    rcases hz with h | ⟨_, h⟩
    · exact absurd hz_zero h.ne'
    · exact h
  have hw_re : w.re < 0 := by
    rcases hw with h | ⟨_, h⟩
    · exact absurd hw_zero h.ne'
    · exact h
  exact ⟨by simp [hz_zero, hw_zero], by simpa using add_neg hz_re hw_re⟩

/-- The oriented determinant of two complex vectors. -/
def phaseCross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re

theorem phaseCross_eq_norm_mul_sin (z w : ℂ) :
    phaseCross z w = ‖z‖ * ‖w‖ * Real.sin (arg w - arg z) := by
  simp only [phaseCross]
  rw [← norm_mul_cos_arg z, ← norm_mul_sin_arg z,
    ← norm_mul_cos_arg w, ← norm_mul_sin_arg w, Real.sin_sub]
  ring

theorem phaseCross_nonneg_of_arg_le {z w : ℂ}
    (hz_im : 0 ≤ z.im) (hz : z ≠ 0) (hw : w ≠ 0)
    (harg : arg z ≤ arg w) : 0 ≤ phaseCross z w := by
  have hnorm : 0 < ‖z‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  rw [phaseCross_eq_norm_mul_sin, mul_nonneg_iff_right_nonneg_of_pos hnorm]
  exact Real.sin_nonneg_of_mem_Icc
    ⟨sub_nonneg.mpr harg,
      by linarith [arg_le_pi w, arg_nonneg_iff.mpr hz_im]⟩

theorem arg_le_of_phaseCross_nonneg {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) (hw_arg : 0 < arg w)
    (hcross : 0 ≤ phaseCross z w) : arg z ≤ arg w := by
  have hnorm : 0 < ‖z‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  rw [phaseCross_eq_norm_mul_sin, mul_nonneg_iff_right_nonneg_of_pos hnorm] at hcross
  by_contra h
  have hneg : arg w - arg z < 0 := sub_neg.mpr (lt_of_not_ge h)
  have hneg_pi : -Real.pi < arg w - arg z := by
    linarith [arg_le_pi z]
  exact (not_lt_of_ge hcross)
    (Real.sin_neg_of_neg_of_neg_pi_lt hneg hneg_pi)

theorem phaseCross_pos_of_arg_lt {z w : ℂ}
    (hz_arg : 0 < arg z) (hz : z ≠ 0) (hw : w ≠ 0)
    (harg : arg z < arg w) : 0 < phaseCross z w := by
  have hnorm : 0 < ‖z‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  rw [phaseCross_eq_norm_mul_sin]
  exact mul_pos hnorm (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr harg)
    (by linarith [arg_le_pi w]))

theorem arg_lt_of_phaseCross_pos {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) (hw_arg : 0 < arg w)
    (hcross : 0 < phaseCross z w) : arg z < arg w := by
  have hnorm : 0 < ‖z‖ * ‖w‖ :=
    mul_pos (norm_pos_iff.mpr hz) (norm_pos_iff.mpr hw)
  rw [phaseCross_eq_norm_mul_sin] at hcross
  have hsin : 0 < Real.sin (arg w - arg z) :=
    ((mul_pos_iff.mp hcross).elim id
      (fun h => absurd h.1 (not_lt.mpr hnorm.le))).2
  by_contra h
  have hwz : arg w ≤ arg z := le_of_not_gt h
  rcases hwz.eq_or_lt with heq | hlt
  · rw [heq, sub_self, Real.sin_zero] at hsin
    exact (lt_irrefl 0) hsin
  · have hneg : arg w - arg z < 0 := sub_neg.mpr hlt
    have hneg_pi : -Real.pi < arg w - arg z := by
      linarith [arg_le_pi z]
    exact (not_lt_of_ge (Real.sin_neg_of_neg_of_neg_pi_lt hneg hneg_pi).le) hsin

theorem arg_add_le_max {z w : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane)
    (hw : w ∈ semiClosedUpperHalfPlane) :
    arg (z + w) ≤ max (arg z) (arg w) := by
  have hz0 := semiClosedUpperHalfPlane_ne_zero hz
  have hw0 := semiClosedUpperHalfPlane_ne_zero hw
  have hsum := add_mem_semiClosedUpperHalfPlane hz hw
  have hsum0 := semiClosedUpperHalfPlane_ne_zero hsum
  rcases le_total (arg z) (arg w) with h | h
  · rw [max_eq_right h]
    apply arg_le_of_phaseCross_nonneg hsum0 hw0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hw)
    have hcross := phaseCross_nonneg_of_arg_le
      (im_nonneg_of_mem_semiClosedUpperHalfPlane hz) hz0 hw0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith
  · rw [max_eq_left h]
    apply arg_le_of_phaseCross_nonneg hsum0 hz0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hz)
    have hcross := phaseCross_nonneg_of_arg_le
      (im_nonneg_of_mem_semiClosedUpperHalfPlane hw) hw0 hz0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith

theorem min_arg_le_arg_add {z w : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane)
    (hw : w ∈ semiClosedUpperHalfPlane) :
    min (arg z) (arg w) ≤ arg (z + w) := by
  have hz0 := semiClosedUpperHalfPlane_ne_zero hz
  have hw0 := semiClosedUpperHalfPlane_ne_zero hw
  have hsum := add_mem_semiClosedUpperHalfPlane hz hw
  have hsum0 := semiClosedUpperHalfPlane_ne_zero hsum
  rcases le_total (arg z) (arg w) with h | h
  · rw [min_eq_left h]
    apply arg_le_of_phaseCross_nonneg hz0 hsum0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hsum)
    have hcross := phaseCross_nonneg_of_arg_le
      (im_nonneg_of_mem_semiClosedUpperHalfPlane hz) hz0 hw0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith
  · rw [min_eq_right h]
    apply arg_le_of_phaseCross_nonneg hw0 hsum0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hsum)
    have hcross := phaseCross_nonneg_of_arg_le
      (im_nonneg_of_mem_semiClosedUpperHalfPlane hw) hw0 hz0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith

theorem arg_add_lt_max {z w : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane)
    (hw : w ∈ semiClosedUpperHalfPlane) (hne : arg z ≠ arg w) :
    arg (z + w) < max (arg z) (arg w) := by
  have hz0 := semiClosedUpperHalfPlane_ne_zero hz
  have hw0 := semiClosedUpperHalfPlane_ne_zero hw
  have hsum := add_mem_semiClosedUpperHalfPlane hz hw
  have hsum0 := semiClosedUpperHalfPlane_ne_zero hsum
  rcases hne.lt_or_gt with h | h
  · rw [max_eq_right h.le]
    apply arg_lt_of_phaseCross_pos hsum0 hw0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hw)
    have hcross := phaseCross_pos_of_arg_lt
      (arg_pos_of_mem_semiClosedUpperHalfPlane hz) hz0 hw0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith
  · rw [max_eq_left h.le]
    apply arg_lt_of_phaseCross_pos hsum0 hz0
      (arg_pos_of_mem_semiClosedUpperHalfPlane hz)
    have hcross := phaseCross_pos_of_arg_lt
      (arg_pos_of_mem_semiClosedUpperHalfPlane hw) hw0 hz0 h
    simp only [phaseCross, Complex.add_re, Complex.add_im] at hcross ⊢
    linarith

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace StabilityFunction

/-- Upper phase see-saw for a short exact sequence. -/
theorem phase_le_max_of_shortExact (Z : StabilityFunction A)
    (S : ShortComplex A) (hS : S.ShortExact)
    (h₁ : ¬IsZero S.X₁) (h₃ : ¬IsZero S.X₃) :
    Z.phase S.X₂ ≤ max (Z.phase S.X₁) (Z.phase S.X₃) := by
  rw [phase, phase, phase, Z.additive S hS]
  have h := arg_add_le_max (Z.nonzero_mem S.X₁ h₁) (Z.nonzero_mem S.X₃ h₃)
  rw [max_div_div_right Real.pi_pos.le]
  exact (div_le_div_iff_of_pos_right Real.pi_pos).2 h

/-- Lower phase see-saw for a short exact sequence. -/
theorem min_phase_le_of_shortExact (Z : StabilityFunction A)
    (S : ShortComplex A) (hS : S.ShortExact)
    (h₁ : ¬IsZero S.X₁) (h₃ : ¬IsZero S.X₃) :
    min (Z.phase S.X₁) (Z.phase S.X₃) ≤ Z.phase S.X₂ := by
  rw [phase, phase, phase, Z.additive S hS]
  rw [min_div_div_right Real.pi_pos.le]
  exact (div_le_div_iff_of_pos_right Real.pi_pos).2
    (min_arg_le_arg_add (Z.nonzero_mem S.X₁ h₁) (Z.nonzero_mem S.X₃ h₃))

/-- A nonzero quotient of a semistable object has phase at least the source
phase. -/
theorem phase_le_of_epi (Z : StabilityFunction A) {E Q : A}
    (p : E ⟶ Q) [Epi p] (hE : Z.IsSemistable E) (hQ : ¬IsZero Q) :
    Z.phase E ≤ Z.phase Q := by
  by_cases hker : IsZero (kernel p)
  · haveI : Mono p := Preadditive.mono_of_kernel_zero
      (zero_of_source_iso_zero _ hker.isoZero)
    haveI : IsIso p := isIso_of_mono_of_epi p
    exact le_of_eq (Z.phase_eq_of_iso (asIso p))
  · have hker_le : Z.phase (kernel p) ≤ Z.phase E := by
      calc Z.phase (kernel p)
          = Z.phase (kernelSubobject p : A) :=
            Z.phase_eq_of_iso (kernelSubobjectIso p).symm
        _ ≤ Z.phase E := hE.2 _ fun hzero =>
            hker (hzero.of_iso (kernelSubobjectIso p).symm)
    by_contra h
    have hQ_lt : Z.phase Q < Z.phase E := lt_of_not_ge h
    have hshort : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
      ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel p) inferInstance inferInstance
    have hsum := Z.additive _ hshort
    have hker_mem := Z.nonzero_mem (kernel p) hker
    have hQ_mem := Z.nonzero_mem Q hQ
    have harg_ker : arg (Z.charge (kernel p)) ≤ arg (Z.charge E) := by
      exact (div_le_div_iff_of_pos_right Real.pi_pos).1 hker_le
    have harg_Q : arg (Z.charge Q) < arg (Z.charge E) := by
      exact (div_lt_div_iff_of_pos_right Real.pi_pos).1 hQ_lt
    rw [hsum] at harg_ker harg_Q
    have hub := arg_add_le_max hker_mem hQ_mem
    have hQ_lt_max := lt_of_lt_of_le harg_Q hub
    have hker_gt_Q : arg (Z.charge Q) < arg (Z.charge (kernel p)) := by
      simpa only [lt_max_iff, lt_irrefl, or_false, abelianDatum_cl] using hQ_lt_max
    have hstrict := arg_add_lt_max hker_mem hQ_mem (ne_of_gt hker_gt_Q)
    simp only [abelianDatum_cl] at hstrict
    rw [max_eq_left hker_gt_Q.le] at hstrict
    exact (not_lt_of_ge harg_ker) hstrict

/-- Hom-vanishing between semistable objects of decreasing phase. -/
theorem hom_eq_zero_of_semistable_phase_gt (Z : StabilityFunction A)
    {E F : A} (hE : Z.IsSemistable E) (hF : Z.IsSemistable F)
    (hphase : Z.phase F < Z.phase E) (f : E ⟶ F) : f = 0 := by
  by_contra hf
  have himage : ¬IsZero (image f) := by
    intro hzero
    apply hf
    have hι : image.ι f = 0 := zero_of_source_iso_zero _ hzero.isoZero
    rw [← image.fac f, hι, comp_zero]
  have hsource := Z.phase_le_of_epi (factorThruImage f) hE himage
  have htarget : Z.phase (image f) ≤ Z.phase F := by
    calc Z.phase (image f)
        = Z.phase (imageSubobject f : A) :=
          Z.phase_eq_of_iso (imageSubobjectIso f).symm
      _ ≤ Z.phase F := hF.2 _ fun hzero =>
          himage (hzero.of_iso (imageSubobjectIso f).symm)
  exact (not_lt_of_ge (hsource.trans htarget)) hphase

end StabilityFunction

end CategoryTheory.Triangulated
