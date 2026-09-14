/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic

/-!
# Continuity of quadratic forms in finite dimension

The polar form of an arbitrary quadratic form on a finite-dimensional real
normed space is jointly continuous, hence so is the quadratic form itself.
These statements have no wall, lattice, or stability hypotheses.
-/

open QuadraticMap

namespace QuadraticMap

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

/-- The polar form is jointly continuous on a finite-dimensional real normed
space. -/
theorem continuous_polar (Q : QuadraticForm ℝ M) :
    Continuous fun p : M × M => polar (⇑Q) p.1 p.2 := by
  set f : M →ₗ[ℝ] (M →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (M →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (M →L[ℝ] ℝ)).toLinearMap.comp
      Q.polarBilin with hf
  exact isBoundedBilinearMap_apply.continuous.comp
    (((LinearMap.continuous_of_finiteDimensional f).comp continuous_fst).prodMk continuous_snd)

/-- A quadratic form on a finite-dimensional real normed space is continuous:
it is half the diagonal of its polar form. -/
theorem continuous_of_finiteDimensional (Q : QuadraticForm ℝ M) : Continuous ⇑Q := by
  have hdiag : Continuous fun x : M => polar (⇑Q) x x :=
    (Q.continuous_polar).comp (continuous_id.prodMk continuous_id)
  have hEq : (fun x : M => (polar (⇑Q) x x) / 2) = ⇑Q := by
    funext x
    rw [polar_self, two_nsmul]
    ring
  rw [← hEq]
  exact hdiag.div_const 2

end QuadraticMap
