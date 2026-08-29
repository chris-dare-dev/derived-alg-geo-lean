/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.NearIdentity
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.SkewedStability

/-!
# Pointwise perturbation of semistable charges

This module connects the pure relative-phase estimates to owner stability
conditions. It packages the pointwise relative norm bound that a future
stability seminorm will supply, proves nonvanishing below one, and constructs
the skewed stability data used on thin intervals.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

/-- A uniform pointwise relative norm bound on all nonzero semistable
objects. The bound is deliberately independent of any chosen global norm on
the target lattice. -/
def SemistableChargeBound (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) (r : ℝ) : Prop :=
  ∀ φ E, σ.slicing.P φ E → ¬IsZero E →
    ‖(W - σ.Z) (classOf C κ E)‖ ≤ r * ‖σ.charge E‖

/-- The old central charge has the selected relative phase of a semistable
object on every compatible branch. -/
theorem relativePhase_charge_eq (σ : StabilityCondition.WithClassMap C κ)
    {E : C} {φ α : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (hφ : φ ∈ Set.Ioc (α - 1) (α + 1)) :
    relativePhase (σ.charge E) α = φ := by
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E hP hE
  rw [hmZ]
  exact relativePhase_of_ray hm hφ

/-- A pointwise norm bound below one prevents the perturbed charge of a
nonzero semistable object from vanishing. -/
theorem perturbedCharge_ne_zero (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r φ : ℝ} (hr : r < 1)
    (hbound : SemistableChargeBound C σ W r) {E : C}
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    W (classOf C κ E) ≠ 0 := by
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E hP hE
  have hZpos : 0 < ‖σ.charge E‖ := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hm
  have hle := hbound φ E hP hE
  intro hW
  rw [AddMonoidHom.sub_apply, hW, zero_sub, norm_neg] at hle
  nlinarith

/-- A pointwise semistable-charge bound below one induces owner skewed
stability data on every nonempty interval. -/
def skewedStabilityFunctionOfBound
    (σ : StabilityCondition.WithClassMap C κ) (W : Λ →+ ℂ)
    {r a b : ℝ} (hr : r < 1) (hbound : SemistableChargeBound C σ W r)
    (hab : a < b) : SkewedStabilityFunction C κ σ.slicing a b where
  W := W
  α := (a + b) / 2
  centre_mem := ⟨by linarith, by linarith⟩
  nonzero E φ _ _ hP hE :=
    perturbedCharge_ne_zero C σ W hr hbound hP hE

/-- Pointwise charge control by `sin (π ε)` gives the corresponding strict
phase control for an old semistable object. -/
theorem relativePhase_perturbation_of_charge
    (σ : StabilityCondition.WithClassMap C κ) (W : Λ →+ ℂ)
    {E : C} {φ α ε : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (hφα : φ ∈ Set.Ioo (α - 1 / 2) (α + 1 / 2))
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hbd : ‖(W - σ.Z) (classOf C κ E)‖ <
      Real.sin (Real.pi * ε) * ‖σ.charge E‖) :
    |relativePhase (W (classOf C κ E)) α - φ| < ε := by
  obtain ⟨m, hm, hmZ⟩ := σ.compat φ E hP hE
  let δ := (W - σ.Z) (classOf C κ E)
  have hδ : δ = W (classOf C κ E) - σ.charge E :=
    AddMonoidHom.sub_apply W σ.Z _
  have hZnorm : ‖σ.charge E‖ = m := by
    rw [hmZ, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm, Complex.norm_exp_ofReal_mul_I, mul_one]
  let u := δ / ((m : ℂ) *
    Complex.exp (↑(Real.pi * φ) * Complex.I))
  have hZne : (m : ℂ) *
      Complex.exp (↑(Real.pi * φ) * Complex.I) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hm.ne') (Complex.exp_ne_zero _)
  have hWfactor : W (classOf C κ E) =
      (m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I) *
        ((1 : ℂ) + u) := by
    rw [show u = δ / ((m : ℂ) *
      Complex.exp (↑(Real.pi * φ) * Complex.I)) from rfl]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hZne, hδ, ← hmZ]
    ring
  have hu : ‖u‖ < Real.sin (Real.pi * ε) := by
    rw [show u = δ / ((m : ℂ) *
      Complex.exp (↑(Real.pi * φ) * Complex.I)) from rfl,
      norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hm, Complex.norm_exp_ofReal_mul_I, mul_one,
      div_lt_iff₀ hm]
    rwa [hZnorm] at hbd
  rw [hWfactor]
  exact relativePhase_perturbation hm hφα hε hε2 hu

end CategoryTheory.Triangulated.Deformation
