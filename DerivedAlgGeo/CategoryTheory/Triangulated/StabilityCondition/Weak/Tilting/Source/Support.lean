/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Source.Charge
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support.Basic

/-!
# Support property for the source-normalized weak tilt

The source charge `Z/(I-b)` is a positive rescaling of the unit phase
rotation.  Positive rescaling preserves weak (semi)stability and rescales
the support estimate by an explicit positive constant.  Thus the support
property proved for the phase tilt transports to the exact charge appearing
in Proposition 14.16.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {v : K₀ C →+ V}

/-- The real-linear realization of the exact source charge `Z/(I-b)`. -/
noncomputable def sourceTiltLinearCharge (b : ℝ)
    (Zlin : V →ₗ[ℝ] ℂ) : V →ₗ[ℝ] ℂ :=
  (LinearMap.mulLeft ℝ ((Complex.I - (b : ℂ))⁻¹)).comp Zlin

omit [FiniteDimensional ℝ V] in
@[simp]
theorem sourceTiltLinearCharge_apply (b : ℝ)
    (Zlin : V →ₗ[ℝ] ℂ) (x : V) :
    sourceTiltLinearCharge b Zlin x =
      Zlin x / (Complex.I - (b : ℂ)) := by
  simp [sourceTiltLinearCharge, div_eq_mul_inv, mul_comm]

omit [FiniteDimensional ℝ V] in
theorem sourceTiltLinearCharge_eq_scale_phaseTiltLinearCharge
    (b : ℝ) (Zlin : V →ₗ[ℝ] ℂ) (x : V) :
    sourceTiltLinearCharge b Zlin x =
      (WeakPreStabilityCondition.sourceTiltScale b : ℂ) *
        phaseTiltLinearCharge
          (WeakPreStabilityCondition.slopeCutPhase b) Zlin x := by
  rw [sourceTiltLinearCharge_apply, div_eq_mul_inv,
    WeakPreStabilityCondition.sourceTilt_multiplier,
    phaseTiltLinearCharge_apply]
  ring

omit [FiniteDimensional ℝ V] in
/-- The exact source normalization scales the norm of the unit phase
rotation by `sourceTiltScale b`. -/
theorem norm_sourceTiltLinearCharge (b : ℝ)
    (Zlin : V →ₗ[ℝ] ℂ) (x : V) :
    ‖sourceTiltLinearCharge b Zlin x‖ =
      WeakPreStabilityCondition.sourceTiltScale b * ‖Zlin x‖ := by
  rw [sourceTiltLinearCharge_eq_scale_phaseTiltLinearCharge, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg
      (WeakPreStabilityCondition.sourceTiltScale_pos b).le,
    norm_phaseTiltLinearCharge]

namespace WeakPreStabilityCondition

omit [FiniteDimensional ℝ V] in
/-- Support-property transport for the exact source charge. -/
theorem sourceTilt_hasSupportProperty
    (sigma : WeakPreStabilityCondition v) (b : ℝ)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin) :
    (sigma.sourceTiltWeakStabilityFunction b).HasSupportProperty v
      (sourceTiltLinearCharge b Zlin) := by
  let theta := slopeCutPhase b
  let c := sourceTiltScale b
  have htheta := slopeCutPhase_mem_Ioo b
  have hc : 0 < c := sourceTiltScale_pos b
  have hc0 : sourceTiltScale b ≠ 0 := (sourceTiltScale_pos b).ne'
  have hphase := sigma.phaseTilt_hasSupportProperty theta htheta.1 htheta.2
    Zlin hcompat hsupport
  obtain ⟨K, hK, hbound⟩ := hphase
  refine ⟨K / c, div_pos hK hc, ?_⟩
  intro x hx
  obtain ⟨E, hEss, hE0, rfl⟩ := hx
  have hEss' :
      (sigma.phaseTiltWeakStabilityFunction theta htheta.1.le htheta.2).IsSemistable E :=
    (sigma.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseTilt b E).mp hEss
  have hb := hbound (v (K₀.of C E)) ⟨E, hEss', hE0, rfl⟩
  calc
    ‖v (K₀.of C E)‖ ≤ K * ‖phaseTiltLinearCharge theta Zlin
        (v (K₀.of C E))‖ := hb
    _ = (K / c) * ‖sourceTiltLinearCharge b Zlin
        (v (K₀.of C E))‖ := by
      rw [norm_sourceTiltLinearCharge, norm_phaseTiltLinearCharge]
      dsimp [c, theta]
      field_simp [hc0]

end WeakPreStabilityCondition

end

end CategoryTheory.Triangulated.WeakStabilityCondition
