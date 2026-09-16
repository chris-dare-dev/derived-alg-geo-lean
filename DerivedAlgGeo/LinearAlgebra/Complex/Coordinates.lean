/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.Positive
import Mathlib.LinearAlgebra.Complex.Module

/-!
# `ℂ` as a real coordinate plane, and real linear maps on it

`Complex.basisOneI` presents `ℂ` as `ℝ²`. `cplxCoord` is that presentation as a
linear equivalence, and `actC` transports a real `2 × 2` matrix of positive
determinant across it, so that a map defined on `Fin 2 → ℝ` can be applied to a
`ℂ`-valued quantity.

## Placement

MO1.12 (#1323), cutover-ledger row 08, comparison-owner column: a
complex-coordinate linear-map adapter moves near the complex linear-algebra
owner **once its public type is independent of the cover**. These five
declarations meet that condition -- `cplxCoord` mentions only `ℂ` and
`Fin 2 → ℝ`, and `actC` takes a `Matrix.GLPos (Fin 2) ℝ`, which is the
general-linear group and not its cover. The three declarations that do not meet
it -- `cplxCoord_exp`, `compat_exp` and `actC_exp`, whose statements mention
`rayVec`, `Compatible` and `NormalizedShift` -- stay with the cover in
`LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover/ComplexRepresentation.lean`.

Independent consumers: the cover's own complex restatements and its
surjectivity argument on one side, and the stability action's continuous
linear map `actCCLM` under
`CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/Action/` on the
other.

Declaration names are unchanged by the move, so the namespace is the one they
were introduced in; see the ledger's first standing decision.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open Matrix

/-- `ℂ` as a real coordinate plane, via the basis `1, I`. -/
noncomputable def cplxCoord : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  Complex.basisOneI.equivFun

/-- Coordinates of a complex number in the `1, I` basis. -/
theorem cplxCoord_apply (z : ℂ) : cplxCoord z = ![z.re, z.im] := by
  show ⇑(Complex.basisOneI.repr z) = _
  rw [Complex.coe_basisOneI_repr]

/-! ## The matrix factor acting on `ℂ`

A central charge lands in `ℂ`, so this is the form in which a real plane map
has to act. Everything below is the matrix transported across `cplxCoord`.
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
`LinearEquiv.symm_apply_apply` finish the job -- so a `@[simp]` here is
redundant and `simpNF` rejects it. Stated in applied form to match `actC_mul`,
which is not `@[simp]` either. -/
theorem actC_one (z : ℂ) : actC 1 z = z := by
  simp [toMat_one, Matrix.one_mulVec]

theorem actC_mul (T U : Matrix.GLPos (Fin 2) ℝ) (z : ℂ) :
    actC (T * U) z = actC T (actC U z) := by
  simp [toMat_mul, ← Matrix.mulVec_mulVec]

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
