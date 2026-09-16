/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Complex.Coordinates
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.UniversalCover.Basic
import Mathlib.Analysis.Complex.Trigonometric

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Compatibility, restated on the complex rays

A central charge is `Z : Λ →+ ℂ` -- it lands in `ℂ`. `GLTilde.mat` acts on
`Fin 2 → ℝ`. These do not compose directly, so the two coordinate conventions
must agree.

They do, and `cplxCoord_exp` is the proof: under `Complex.basisOneI` (whose
`repr` is `![z.re, z.im]`), the canonical ray `exp (i π φ)` has coordinates
`![cos (π φ), sin (π φ)]`, which is exactly `rayVec φ`.

The neutral half of the bridge -- `cplxCoord`, `actC` and the two action laws,
whose public types mention the general-linear group and not its cover -- is in
`LinearAlgebra/Complex/Coordinates.lean`. The three statements here are the
ones that mention `rayVec`, `Compatible` and `NormalizedShift`, so they are
comparisons and stay with the cover (MO1.12, #1323; cutover-ledger row 08).
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open Matrix

/-- **The conventions agree.** The stability foundation writes its rays as
`exp (i π φ)`
(`CategoryTheory/Triangulated/StabilityCondition/Foundation/PreStabilityCondition.lean`);
in `basisOneI` coordinates that is `rayVec φ`.

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
`CategoryTheory/Triangulated/StabilityCondition/Foundation/PreStabilityCondition.lean`. -/
theorem compat_exp {T : Matrix.GLPos (Fin 2) ℝ} {f : NormalizedShift}
    (h : Compatible T f) (φ : ℝ) :
    ∃ r : ℝ, 0 < r ∧
      toMat T *ᵥ cplxCoord (Complex.exp (↑(Real.pi * φ) * Complex.I))
        = r • cplxCoord (Complex.exp (↑(Real.pi * f.toOrderIso φ) * Complex.I)) := by
  obtain ⟨r, hr, hry⟩ := h φ
  exact ⟨r, hr, by rw [cplxCoord_exp, cplxCoord_exp, hry]⟩

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

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
