/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The underlying matrix of a positive-determinant invertible matrix

`Matrix.GLPos n R` is a subgroup of `GL n R`, which is a group of units, so
reading off the matrix takes two coercions. `toMat` is that composite, together
with the two lemmas saying it is a monoid map.

## Main definitions

* `CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.toMat` —
  the matrix underlying an element of `GL⁺(2, ℝ)`.

## Main results

* `toMat_mul` and `toMat_one` — `toMat` is multiplicative and unital, both by `rfl`.

## Implementation notes

Neutral general-linear-group API: it mentions no cover, no phase and no
stability condition, and it is consumed independently by the universal cover of
`GL⁺(2, ℝ)` under `UniversalCover/`, by the complex-coordinate adapter in
`LinearAlgebra/Complex/Coordinates.lean`, and by the stability action under
`CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/Action/`.
The declarations live in the namespace of the stability action, which keeps
their fully qualified names fixed.

## References

Mathlib's `Matrix.GLPos` and `Matrix.GeneralLinearGroup`.

## Tags

general linear group, positive determinant, matrix
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
