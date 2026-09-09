/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.ChargeFamily
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical.Basic

/-!
# The `(s, t)` numerical charge as a generic charge family

`Walls.ChargeFamily` defines wall loci for an arbitrary parameterized family
of additive complex charges.  This file packages the older three-coordinate
surface model from `Walls.Numerical.Basic` as one child of that abstraction.

The specialization is deliberately thin: its parameter space is `ℝ × ℝ`, its
class carrier is `NumClass = ℝ × ℝ × ℝ`, and its universal determinant is
proved to be the existing `wallExpr`.  Consequently the circle, line,
disjointness, and nesting results remain arithmetic theorems about this child;
they do not become assumptions of the dimension-independent wall root.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

/-- The complex charge whose real and imaginary parts are the `(s,t)`
polynomials `reZ` and `imZ`. -/
def stCharge (s t : ℝ) : NumClass →+ ℂ :=
  AddMonoidHom.mk'
    (fun v => Complex.ofReal (reZ s t v) +
      Complex.I * Complex.ofReal (imZ s t v))
    (by
      intro v w
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
        simp [reZ, NumClass.rk, NumClass.deg, NumClass.ch2]
        ring
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        simp [imZ, NumClass.rk, NumClass.deg]
        ring)

@[simp]
theorem stCharge_re (s t : ℝ) (v : NumClass) :
    (stCharge s t v).re = reZ s t v := by
  simp [stCharge]

@[simp]
theorem stCharge_im (s t : ℝ) (v : NumClass) :
    (stCharge s t v).im = imZ s t v := by
  simp [stCharge]

/-- The old half-plane model, represented as a child of `ChargeFamily`.

No positivity condition is built into the parameter type: the hypotheses
`t > 0` or `t ≠ 0` remain attached to precisely the geometric consequences
that need them. -/
def stChargeFamily : ChargeFamily (ℝ × ℝ) NumClass where
  charge p := stCharge p.1 p.2

@[simp]
theorem stChargeFamily_charge (p : ℝ × ℝ) (v : NumClass) :
    stChargeFamily.charge p v =
      Complex.ofReal (reZ p.1 p.2 v) +
        Complex.I * Complex.ofReal (imZ p.1 p.2 v) := rfl

/-- The generic determinant specializes exactly to the established numerical
wall expression. -/
@[simp]
theorem stChargeFamily_wallValue (p : ℝ × ℝ) (v w : NumClass) :
    stChargeFamily.wallValue p v w = wallExpr p.1 p.2 v w := by
  simp [stChargeFamily, ChargeFamily.wallValue, ChargeFamily.re,
    ChargeFamily.im, wallExpr]

/-- The generic wall locus is the zero locus used by the older numerical wall
development. -/
theorem mem_stChargeFamily_wall (p : ℝ × ℝ) (v w : NumClass) :
    p ∈ stChargeFamily.wall v w ↔ wallExpr p.1 p.2 v w = 0 := by
  simp

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
