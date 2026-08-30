/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.ChargePerturbation
import Mathlib.Data.ENNReal.Real

/-!
# The owner stability seminorm

The stability seminorm of a charge homomorphism is the supremum of its norm
relative to the central charge over all nonzero semistable objects.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

/-- The extended nonnegative stability seminorm of a charge homomorphism. -/
def stabilitySeminorm (σ : StabilityCondition.WithClassMap C κ)
    (U : Λ →+ ℂ) : ℝ≥0∞ :=
  ⨆ (E : C) (φ : ℝ) (_ : σ.slicing.P φ E) (_ : ¬IsZero E),
    ENNReal.ofReal (‖U (classOf C κ E)‖ / ‖σ.charge E‖)

/-- The central charge of a nonzero semistable object has positive norm. -/
theorem charge_norm_pos (σ : StabilityCondition.WithClassMap C κ)
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    0 < ‖σ.charge E‖ := by
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E hP hE
  rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hm, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact hm

/-- Every semistable ratio is bounded by the stability seminorm. -/
theorem ratio_le_stabilitySeminorm
    (σ : StabilityCondition.WithClassMap C κ) (U : Λ →+ ℂ)
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ENNReal.ofReal (‖U (classOf C κ E)‖ / ‖σ.charge E‖) ≤
      stabilitySeminorm C σ U :=
  le_iSup_of_le E (le_iSup_of_le φ
    (le_iSup_of_le hP (le_iSup_of_le hE le_rfl)))

/-- The stability seminorm is nonnegative. -/
theorem stabilitySeminorm_nonneg
    (σ : StabilityCondition.WithClassMap C κ) (U : Λ →+ ℂ) :
    0 ≤ stabilitySeminorm C σ U :=
  zero_le

/-- The zero charge homomorphism has zero stability seminorm. -/
@[simp]
theorem stabilitySeminorm_zero
    (σ : StabilityCondition.WithClassMap C κ) :
    stabilitySeminorm C σ 0 = 0 := by
  simp [stabilitySeminorm]

/-- Negation preserves the stability seminorm. -/
@[simp]
theorem stabilitySeminorm_neg
    (σ : StabilityCondition.WithClassMap C κ) (U : Λ →+ ℂ) :
    stabilitySeminorm C σ (-U) = stabilitySeminorm C σ U := by
  simp [stabilitySeminorm]

/-- The owner stability seminorm satisfies the triangle inequality. -/
theorem stabilitySeminorm_add_le
    (σ : StabilityCondition.WithClassMap C κ) (U V : Λ →+ ℂ) :
    stabilitySeminorm C σ (U + V) ≤
      stabilitySeminorm C σ U + stabilitySeminorm C σ V := by
  apply iSup_le
  intro E
  apply iSup_le
  intro φ
  apply iSup_le
  intro hP
  apply iSup_le
  intro hE
  calc
    ENNReal.ofReal (‖(U + V) (classOf C κ E)‖ / ‖σ.charge E‖) ≤
        ENNReal.ofReal (‖U (classOf C κ E)‖ / ‖σ.charge E‖ +
          ‖V (classOf C κ E)‖ / ‖σ.charge E‖) := by
      apply ENNReal.ofReal_le_ofReal
      rw [AddMonoidHom.add_apply, ← add_div]
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)
    _ = ENNReal.ofReal (‖U (classOf C κ E)‖ / ‖σ.charge E‖) +
        ENNReal.ofReal (‖V (classOf C κ E)‖ / ‖σ.charge E‖) :=
      ENNReal.ofReal_add
        (div_nonneg (norm_nonneg _) (norm_nonneg _))
        (div_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ stabilitySeminorm C σ U + stabilitySeminorm C σ V :=
      add_le_add
        (ratio_le_stabilitySeminorm C σ U hP hE)
        (ratio_le_stabilitySeminorm C σ V hP hE)

/-- A real upper bound on the stability seminorm supplies the corresponding
pointwise relative norm bound. -/
theorem semistableChargeBound_of_stabilitySeminorm_le
    (σ : StabilityCondition.WithClassMap C κ) (W : Λ →+ ℂ) {r : ℝ}
    (hr : 0 ≤ r)
    (h : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r) :
    SemistableChargeBound C σ W r := by
  intro φ E hP hE
  have hratio :
      ENNReal.ofReal
          (‖(W - σ.Z) (classOf C κ E)‖ / ‖σ.charge E‖) ≤
        ENNReal.ofReal r :=
    (ratio_le_stabilitySeminorm C σ (W - σ.Z) hP hE).trans h
  have hreal :
      ‖(W - σ.Z) (classOf C κ E)‖ / ‖σ.charge E‖ ≤ r :=
    (ENNReal.ofReal_le_ofReal_iff hr).mp hratio
  rwa [div_le_iff₀ (charge_norm_pos C σ hP hE)] at hreal

/-- A finite stability seminorm supplies its `toReal` as a pointwise bound on
semistable charge perturbations. -/
theorem semistableChargeBound_toReal
    (σ : StabilityCondition.WithClassMap C κ) (W : Λ →+ ℂ)
    (hfinite : stabilitySeminorm C σ (W - σ.Z) ≠ ⊤) :
    SemistableChargeBound C σ W
      (stabilitySeminorm C σ (W - σ.Z)).toReal := by
  apply semistableChargeBound_of_stabilitySeminorm_le C σ W
    ENNReal.toReal_nonneg
  rw [ENNReal.ofReal_toReal hfinite]

/-- A stability-seminorm bound below one produces skewed stability data on
every nonempty interval. -/
def skewedStabilityFunctionOfSeminormLtOne
    (σ : StabilityCondition.WithClassMap C κ) (W : Λ →+ ℂ)
    {r a b : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    (hab : a < b) : SkewedStabilityFunction C κ σ.slicing a b :=
  skewedStabilityFunctionOfBound C σ W hr1
    (semistableChargeBound_of_stabilitySeminorm_le C σ W hr0 h) hab

/-- A strict stability-seminorm bound by `sin (π ε)` strictly controls the
selected phase of every old semistable object on a compatible branch. -/
theorem relativePhase_perturbation_of_stabilitySeminorm
    (σ : StabilityCondition.WithClassMap C κ) (W : Λ →+ ℂ)
    {E : C} {φ α ε : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (hφα : φ ∈ Set.Ioo (α - 1 / 2) (α + 1 / 2))
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (h : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    |relativePhase (W (classOf C κ E)) α - φ| < ε := by
  have hsin : 0 < Real.sin (Real.pi * ε) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos Real.pi_pos hε
    · nlinarith [Real.pi_pos]
  have hratio : ENNReal.ofReal
      (‖(W - σ.Z) (classOf C κ E)‖ / ‖σ.charge E‖) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)) :=
    lt_of_le_of_lt
      (ratio_le_stabilitySeminorm C σ (W - σ.Z) hP hE) h
  have hreal :
      ‖(W - σ.Z) (classOf C κ E)‖ / ‖σ.charge E‖ <
        Real.sin (Real.pi * ε) := by
    exact (ENNReal.ofReal_lt_ofReal_iff hsin).mp hratio
  have hbd : ‖(W - σ.Z) (classOf C κ E)‖ <
      Real.sin (Real.pi * ε) * ‖σ.charge E‖ := by
    rwa [div_lt_iff₀ (charge_norm_pos C σ hP hE)] at hreal
  exact relativePhase_perturbation_of_charge C σ W hP hE hφα hε hε2 hbd

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation
