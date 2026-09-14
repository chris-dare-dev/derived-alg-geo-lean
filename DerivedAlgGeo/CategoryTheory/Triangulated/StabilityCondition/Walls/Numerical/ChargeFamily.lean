/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Numerical.SurfaceFamily
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Alignment
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
theorem stChargeFamily_alignmentValue (p : ℝ × ℝ) (v w : NumClass) :
    stChargeFamily.alignmentValue p v w = wallExpr p.1 p.2 v w := by
  simp [stChargeFamily, ChargeFamily.alignmentValue, ChargeFamily.re,
    ChargeFamily.im, wallExpr]

/-- The generic alignment wall is the zero locus of the surface wall
expression. -/
theorem mem_stChargeFamily_alignmentLocus (p : ℝ × ℝ) (v w : NumClass) :
    p ∈ stChargeFamily.alignmentLocus v w ↔ wallExpr p.1 p.2 v w = 0 := by
  simp

end


end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
