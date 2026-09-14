/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Numerical.Threefold
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.ChargeFamily

/-!
# Threefold wall equations and BMT numerical quantities

The threefold class, twist, and charge are owned upstream by
`CentralCharge/Numerical/Threefold.lean`. This file adds only the determinant
wall equation and the numerical quantities used by downstream tilt-wall work.

No nonnegativity of `Q` is asserted here; geometric hypotheses belong
downstream.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

namespace Threefold

/-- The universal determinant of the threefold family, written out in the two
polynomials. -/
theorem chargeFamily_wallValue (p : ℝ × ℝ) (v w : NumClass) :
    chargeFamily.wallValue p v w =
      reZ p.1 p.2 v * imZ p.1 p.2 w - imZ p.1 p.2 v * reZ p.1 p.2 w := by
  simp [ChargeFamily.wallValue, ChargeFamily.re, ChargeFamily.im]

/-- Dropping the outer `α` from the imaginary part rescales every wall
expression by `α`, so it moves no wall off `α = 0`.  This is why the two
normalisations of the threefold charge found in the literature agree about
walls. -/
theorem wallValue_div_alpha (α β : ℝ) (v w : NumClass) :
    reZ α β v * imZ α β w - imZ α β v * reZ α β w =
      α * (reZ α β v * (imZ α β w / α) - (imZ α β v / α) * reZ α β w) ∨ α = 0 := by
  by_cases hα : α = 0
  · exact Or.inr hα
  · refine Or.inl ?_
    field_simp

/-! ### The Bayer--Macrì--Toda quantities, as definitions -/

/-- The `H`-discriminant of a compressed threefold class,
`Δ_H = (∫H²ch₁)² − 2(∫H³ch₀)(∫H·ch₂)`. -/
def discr (v : NumClass) : ℝ := v.deg1 ^ 2 - 2 * v.deg0 * v.deg2

/-- **The tilt slope** `ν_{α,β}`, junk where the denominator vanishes — the same
convention the surface slope uses at rank zero. -/
def nu (α β : ℝ) (v : NumClass) : ℝ :=
  ((betaTwist β v).deg2 - α ^ 2 / 2 * v.deg0) / (betaTwist β v).deg1

/-- **The Bayer--Macrì--Toda quantity**
`Q_{α,β} = α²Δ_H + 4(∫H·ch₂^β)² − 6(∫H²ch₁^β)(∫ch₃^β)`.

Defining it is all this does.  Its nonnegativity on tilt-semistable objects is
the BMT conjecture, which is **false in general**; see the module docstring and
`AlgebraicGeometry/Numerical/Stability/BMT.lean`. -/
def Q (α β : ℝ) (v : NumClass) : ℝ :=
  α ^ 2 * discr (betaTwist β v) + 4 * (betaTwist β v).deg2 ^ 2
    - 6 * (betaTwist β v).deg1 * (betaTwist β v).deg3

/-- At `α = 0` the quantity loses its discriminant term. -/
theorem Q_zero_alpha (β : ℝ) (v : NumClass) :
    Q 0 β v = 4 * (betaTwist β v).deg2 ^ 2
      - 6 * (betaTwist β v).deg1 * (betaTwist β v).deg3 := by
  rw [Q]
  ring

/-- At `β = 0` the twist disappears. -/
@[simp]
theorem Q_zero_beta (α : ℝ) (v : NumClass) :
    Q α 0 v = α ^ 2 * discr v + 4 * v.deg2 ^ 2 - 6 * v.deg1 * v.deg3 := by
  rw [Q, betaTwist_zero]

/-- At `α = 0` the tilt slope is the plain ratio of the two twisted degrees. -/
theorem nu_zero_alpha (β : ℝ) (v : NumClass) :
    nu 0 β v = (betaTwist β v).deg2 / (betaTwist β v).deg1 := by
  rw [nu]
  norm_num


end Threefold

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
