/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.Complex.Trigonometric

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The complex representation of real two-dimensional linear maps

The repository's central charge is `Z : Λ →+ ℂ` — it lands in `ℂ`. `GLTilde.mat`
acts on `Fin 2 → ℝ`. These do not compose directly, so the two coordinate
conventions must agree.

They do, and `cplxCoord_exp` is the proof: under `Complex.basisOneI` (whose
`repr` is `![z.re, z.im]`), the canonical ray `exp (i π φ)` has coordinates
`![cos (π φ), sin (π φ)]`, which is exactly `rayVec φ`.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.GroupAction

open Matrix

/-- `ℂ` as a real coordinate plane, via the basis `1, I`. -/
noncomputable def cplxCoord : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  Complex.basisOneI.equivFun

/-- **The conventions agree.** The stability foundation writes its rays as
`exp (i π φ)` (`WeakStabilityCondition/StabilityCondition/Foundation/PreStabilityCondition.lean`); in
`basisOneI` coordinates that is `rayVec φ`.

Proved through `Complex.basisOneI.repr` rather than `Basis.equivFun_apply`:
the two are definitionally equal, and the `repr` route avoids `simp`
normalising `↑(π * φ)` into `↑π * ↑φ`, which stops
`Complex.exp_ofReal_mul_I_re` from matching. -/
theorem cplxCoord_exp (φ : ℝ) :
    cplxCoord (Complex.exp (↑(Real.pi * φ) * Complex.I)) = rayVec φ := by
  show ⇑(Complex.basisOneI.repr (Complex.exp (↑(Real.pi * φ) * Complex.I))) = _
  rw [Complex.coe_basisOneI_repr, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  rfl

/-- `Compatible`, restated on the stability foundation's rays.

It says `T` carries the charge-ray at phase `φ` to the charge-ray at phase
`f φ`, entirely in the `exp (i π ·)` vocabulary of
`WeakStabilityCondition/StabilityCondition/Foundation/PreStabilityCondition.lean`. -/
theorem compat_exp {T : Matrix.GLPos (Fin 2) ℝ} {f : NormalizedShift}
    (h : Compatible T f) (φ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      toMat T *ᵥ cplxCoord (Complex.exp (↑(Real.pi * φ) * Complex.I))
        = r • cplxCoord (Complex.exp (↑(Real.pi * f.toOrderIso φ) * Complex.I)) := by
  obtain ⟨r, hr, hry⟩ := h φ
  exact ⟨r, hr, by rw [cplxCoord_exp, cplxCoord_exp, hry]⟩

/-! ## The matrix factor acting on `ℂ`

The central charge lands in `ℂ`, so this is the form in which the matrix factor
of `G̃L⁺(2, ℝ)` has to act. Everything below is `GLTilde.mat`
transported across `cplxCoord`.
-/

/-- `T` acting `ℝ`-linearly on `ℂ`, through the coordinate bridge. -/
noncomputable def actC (T : Matrix.GLPos (Fin 2) ℝ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := cplxCoord.symm (toMat T *ᵥ cplxCoord z)
  map_add' z w := by simp [Matrix.mulVec_add]
  map_smul' c z := by
    change cplxCoord.symm (toMat T *ᵥ cplxCoord (c • z)) =
      c • cplxCoord.symm (toMat T *ᵥ cplxCoord z)
    simp only [map_smul, Matrix.mulVec_smul]

@[simp]
theorem actC_apply (T : Matrix.GLPos (Fin 2) ℝ) (z : ℂ) :
    actC T z = cplxCoord.symm (toMat T *ᵥ cplxCoord z) := rfl

/-- `actC 1` is the identity map.

Deliberately **not** `@[simp]`. `actC_apply` is the simp lemma that unfolds
`actC`, and once it fires `toMat_one`, `Matrix.one_mulVec` and
`LinearEquiv.symm_apply_apply` finish the job — so a `@[simp]` here is
redundant and `simpNF` rejects it. Stated in applied form to match `actC_mul`,
which is not `@[simp]` either. -/
theorem actC_one (z : ℂ) : actC 1 z = z := by
  simp [toMat_one, Matrix.one_mulVec]

theorem actC_mul (T U : Matrix.GLPos (Fin 2) ℝ) (z : ℂ) :
    actC (T * U) z = actC T (actC U z) := by
  simp [toMat_mul, ← Matrix.mulVec_mulVec]

/-- `Compatible`, as a statement about `actC` on the charge rays.

The map `T` carries the charge ray at phase `φ` to the charge ray at phase
`f φ`, scaled by some `r > 0`. -/
theorem actC_exp {T : Matrix.GLPos (Fin 2) ℝ} {f : NormalizedShift}
    (h : Compatible T f) (φ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      actC T (Complex.exp (↑(Real.pi * φ) * Complex.I))
        = r • Complex.exp (↑(Real.pi * f.toOrderIso φ) * Complex.I) := by
  obtain ⟨r, hr, hry⟩ := compat_exp h φ
  refine ⟨r, hr, ?_⟩
  rw [actC_apply, hry, map_smul, LinearEquiv.symm_apply_apply]

end CategoryTheory.Triangulated.StabilityCondition.GroupAction
