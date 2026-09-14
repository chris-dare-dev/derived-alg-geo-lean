/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Numerical.SurfaceFamily
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.ChargeFamily
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical.Basic

/-!
# The surface charge family and its wall equation

The compressed charge and family are owned upstream by `CentralCharge/`.
This module identifies their determinant-alignment locus with the established
surface wall polynomial.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

/-- The generic determinant specializes exactly to the surface wall
expression. -/
@[simp]
theorem stChargeFamily_wallValue (p : ℝ × ℝ) (v w : NumClass) :
    stChargeFamily.wallValue p v w = wallExpr p.1 p.2 v w := by
  simp [stChargeFamily, ChargeFamily.wallValue, ChargeFamily.re,
    ChargeFamily.im, wallExpr]

/-- The generic alignment wall is the zero locus of the surface wall
expression. -/
theorem mem_stChargeFamily_wall (p : ℝ × ℝ) (v w : NumClass) :
    p ∈ stChargeFamily.wall v w ↔ wallExpr p.1 p.2 v w = 0 := by
  simp

end


end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
