/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The underlying matrix of a positive-determinant invertible matrix

`Matrix.GLPos n R` is a subgroup of `GL n R`, which is a group of units, so
reading off the matrix takes two coercions. `toMat` is that composite, together
with the two lemmas saying it is a monoid map.

Neutral general-linear-group API: it mentions no cover, no phase and no
stability condition, and it is consumed independently by the universal cover of
`GL⁺(2, ℝ)` under `UniversalCover/`, by the complex-coordinate adapter in
`LinearAlgebra/Complex/Coordinates.lean`, and by the stability action under
`CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/Action/`.
Extracted by MO1.12 (#1323) from the cover's `Basic.lean`, where it was
declared; the fully qualified names are unchanged, per the cutover ledger's
first standing decision.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

/-- The matrix underlying an element of `GL⁺(2, ℝ)`. -/
def toMat (T : Matrix.GLPos (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((T : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)

@[simp]
theorem toMat_mul (T U : Matrix.GLPos (Fin 2) ℝ) :
    toMat (T * U) = toMat T * toMat U := rfl

@[simp]
theorem toMat_one : toMat 1 = 1 := rfl

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
