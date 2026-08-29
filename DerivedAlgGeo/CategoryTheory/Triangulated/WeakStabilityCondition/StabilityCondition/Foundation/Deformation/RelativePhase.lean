/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Relative phases of complex numbers

The deformation construction must choose a real lift of the argument of a
complex charge. `relativePhase w α` is the unique lift in `(α - 1, α + 1]`.
Keeping this branch-control layer independent of categories makes the later
stability-condition deformation API depend on an owner-controlled analytic
primitive rather than the retained package.
-/

noncomputable section

namespace CategoryTheory.Triangulated.Deformation

/-- The lift of the phase of `w` whose branch is centred at `α`. -/
def relativePhase (w : ℂ) (α : ℝ) : ℝ :=
  α + Complex.arg (w * Complex.exp (-(↑(Real.pi * α) * Complex.I))) /
    Real.pi

/-- The relative phase lies on its selected branch. -/
theorem relativePhase_mem_Ioc (w : ℂ) (α : ℝ) :
    relativePhase w α ∈ Set.Ioc (α - 1) (α + 1) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  let z := w * Complex.exp (-(↑(Real.pi * α) * Complex.I))
  constructor
  · suffices -1 < Complex.arg z / Real.pi by
      change α - 1 < α + Complex.arg z / Real.pi
      linarith
    rw [lt_div_iff₀ hπ]
    simpa only [neg_one_mul] using Complex.neg_pi_lt_arg z
  · suffices Complex.arg z / Real.pi ≤ 1 by
      change α + Complex.arg z / Real.pi ≤ α + 1
      linarith
    rw [div_le_iff₀ hπ, one_mul]
    exact Complex.arg_le_pi z

/-- Polar reconstruction using the selected relative phase. -/
theorem relativePhase_polar (w : ℂ) (α : ℝ) :
    w = (‖w‖ : ℂ) *
      Complex.exp (↑(Real.pi * relativePhase w α) * Complex.I) := by
  let z := w * Complex.exp (-(↑(Real.pi * α) * Complex.I))
  have hwz : w = z * Complex.exp (↑(Real.pi * α) * Complex.I) := by
    dsimp [z]
    rw [mul_assoc, ← Complex.exp_add]
    simp
  have hnorm : ‖z‖ = ‖w‖ := by
    dsimp [z]
    rw [norm_mul]
    have hexp : -(↑(Real.pi * α) * Complex.I) =
        ↑(-(Real.pi * α)) * Complex.I := by
      push_cast
      ring
    rw [hexp, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hangle :
      (Complex.arg z : ℂ) * Complex.I +
          ↑(Real.pi * α) * Complex.I =
        ↑(Real.pi * relativePhase w α) * Complex.I := by
    have hreal : Complex.arg z + Real.pi * α =
        Real.pi * relativePhase w α := by
      dsimp [relativePhase, z]
      field_simp
      ring
    calc
      (Complex.arg z : ℂ) * Complex.I +
          ↑(Real.pi * α) * Complex.I =
        (↑(Complex.arg z + Real.pi * α) : ℂ) * Complex.I := by
          push_cast
          ring
      _ = (↑(Real.pi * relativePhase w α) : ℂ) * Complex.I := by
          rw [hreal]
  calc
    w = z * Complex.exp (↑(Real.pi * α) * Complex.I) := hwz
    _ = (↑‖z‖ * Complex.exp (↑(Complex.arg z) * Complex.I)) *
        Complex.exp (↑(Real.pi * α) * Complex.I) := by
          rw [Complex.norm_mul_exp_arg_mul_I]
    _ = (‖z‖ : ℂ) * Complex.exp
        ((Complex.arg z : ℂ) * Complex.I +
          ↑(Real.pi * α) * Complex.I) := by
          rw [mul_assoc, Complex.exp_add]
    _ = (‖w‖ : ℂ) *
        Complex.exp (↑(Real.pi * relativePhase w α) * Complex.I) := by
          rw [hnorm, hangle]

/-- A positive point on a ray is recognized on every compatible branch. -/
theorem relativePhase_of_ray {m φ α : ℝ} (hm : 0 < m)
    (hφ : φ ∈ Set.Ioc (α - 1) (α + 1)) :
    relativePhase ((m : ℂ) *
      Complex.exp (↑(Real.pi * φ) * Complex.I)) α = φ := by
  unfold relativePhase
  have harg : Complex.arg
      ((m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I) *
        Complex.exp (-(↑(Real.pi * α) * Complex.I))) =
      Real.pi * (φ - α) := by
    have hexp : (m : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I) *
        Complex.exp (-(↑(Real.pi * α) * Complex.I)) =
        (m : ℂ) * Complex.exp (↑(Real.pi * (φ - α)) * Complex.I) := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    rw [hexp, Complex.arg_real_mul _ hm, Complex.arg_exp_mul_I,
      toIocMod_eq_self]
    constructor <;> nlinarith [Real.pi_pos, hφ.1, hφ.2]
  rw [harg]
  field_simp
  ring

@[simp]
theorem relativePhase_zero (α : ℝ) : relativePhase 0 α = α := by
  simp [relativePhase, Complex.arg_zero]

/-- Negating a nonzero charge and moving the branch centre by one shifts its
relative phase by one. -/
theorem relativePhase_neg {w : ℂ} (hw : w ≠ 0) (α : ℝ) :
    relativePhase (-w) (α + 1) = relativePhase w α + 1 := by
  let φ := relativePhase w α
  have hφ := relativePhase_mem_Ioc w α
  have hbranch : φ + 1 ∈ Set.Ioc ((α + 1) - 1) ((α + 1) + 1) := by
    constructor <;> linarith [hφ.1, hφ.2]
  have hneg : -w = (‖w‖ : ℂ) *
      Complex.exp (↑(Real.pi * (φ + 1)) * Complex.I) := by
    calc
      -w = -((‖w‖ : ℂ) *
          Complex.exp (↑(Real.pi * φ) * Complex.I)) := by
            rw [← relativePhase_polar w α]
      _ = (‖w‖ : ℂ) *
          (-Complex.exp (↑(Real.pi * φ) * Complex.I)) := by ring
      _ = (‖w‖ : ℂ) *
          (Complex.exp (↑Real.pi * Complex.I) *
            Complex.exp (↑(Real.pi * φ) * Complex.I)) := by
            rw [Complex.exp_pi_mul_I]
            ring
      _ = (‖w‖ : ℂ) * Complex.exp
          (↑Real.pi * Complex.I + ↑(Real.pi * φ) * Complex.I) := by
            rw [Complex.exp_add]
      _ = (‖w‖ : ℂ) *
          Complex.exp (↑(Real.pi * (φ + 1)) * Complex.I) := by
            congr 1
            push_cast
            ring_nf
  rw [hneg]
  exact relativePhase_of_ray (norm_pos_iff.mpr hw) hbranch

/-- Moving the branch centre by a full period moves the phase by that period. -/
theorem relativePhase_add_two {w : ℂ} (hw : w ≠ 0) (α : ℝ) :
    relativePhase w (α + 2) = relativePhase w α + 2 := by
  have h₁ := relativePhase_neg hw α
  have h₂ := relativePhase_neg (neg_ne_zero.mpr hw) (α + 1)
  rw [neg_neg, show (α + 1 : ℝ) + 1 = α + 2 by ring] at h₂
  exact h₂.trans (by rw [h₁]; ring)

/-- Relative phase is independent of the branch centre once one chosen lift
also lies on the other branch. -/
theorem relativePhase_eq_of_mem {w : ℂ} (hw : w ≠ 0) (α β : ℝ)
    (h : relativePhase w α ∈ Set.Ioc (β - 1) (β + 1)) :
    relativePhase w α = relativePhase w β := by
  let φ := relativePhase w α
  have hpolar := relativePhase_polar w α
  have hrecognize : relativePhase
      ((‖w‖ : ℂ) * Complex.exp (↑(Real.pi * φ) * Complex.I)) β = φ :=
    relativePhase_of_ray (norm_pos_iff.mpr hw) h
  rw [← hpolar] at hrecognize
  exact hrecognize.symm

end CategoryTheory.Triangulated.Deformation
