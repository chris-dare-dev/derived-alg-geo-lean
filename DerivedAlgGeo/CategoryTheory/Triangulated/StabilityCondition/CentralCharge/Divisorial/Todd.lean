/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic

/-!
# Supplied surface Todd-correction data

On a surface, a Mukai vector uses only the codimension-one component of
`√td` and the integrated codimension-two component.  `SqrtTodd` stores exactly
those two supplied values.  This file makes no claim that they arise from a
scheme; the geometric constructor remains under `AlgebraicGeometry/Numerical`.
-/

universe w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

variable {D : Type w} [AddCommGroup D] [Module ℝ D]

/-- The part of `√td_X` visible to a surface Mukai vector. -/
structure SqrtTodd (D : Type w) [AddCommGroup D] [Module ℝ D] where
  /-- The codimension-one component `√td₁`. -/
  divisor : D
  /-- The integrated codimension-two component `∫√td₂`. -/
  number : ℝ

namespace SqrtTodd

/-- The trivial correction. -/
def trivial : SqrtTodd D := ⟨0, 0⟩

/-- The K3 correction `√td = 1 + [pt]`. -/
def k3 : SqrtTodd D := ⟨0, 1⟩

@[simp] theorem trivial_divisor : (trivial : SqrtTodd D).divisor = 0 := rfl

@[simp] theorem trivial_number : (trivial : SqrtTodd D).number = 0 := rfl

@[simp] theorem k3_divisor : (k3 : SqrtTodd D).divisor = 0 := rfl

@[simp] theorem k3_number : (k3 : SqrtTodd D).number = 1 := rfl

end SqrtTodd


end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
