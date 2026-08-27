/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Threefold.LinearSection
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Threefold

/-!
# The numerical model of `ℙ³`

The first model of `NumericalVarietyData` in dimension three. Before it, every statement in
`DerivedAlgGeo/AlgebraicGeometry/Numerical/Specializations/Threefold.lean` was conditional on
a `NumericalVarietyData 3 A N` existing at all.

`ℙ³` is the threefold analogue of `Examples/Surface/ProjectivePlane.lean`, and it is here for
the same reason: **every** Todd coefficient is nonzero, so it is the model that can detect a
sign or index error anywhere in `Threefold.chi_eq`. A Calabi–Yau model cannot — two of the
four terms are multiplied by zero there.

The data: `Pic ℙ³ = ℤ·H` with `∫H³ = 1`, and

`td(ℙ³) = 1 + 2H + (11/6)H² + H³`,

whose components are `td₁ = −K/2 = 2H` from `K = −4H`, `td₂ = (c₁² + c₂)/12 = (16 + 6)/12`,
and `td₃ = c₁c₂/24 = 24/24 = 1`, giving `χ(O) = 1`.

## Main definitions

* `p3NumericalVariety` — the model.

## Main results

* `p3ChiStructureSheaf` — `∫_{ℙ³} td₃ = χ(O_{ℙ³}) = 1`.
* `p3Chi_lineBundle` — Riemann–Roch on this model reproduces
  `χ(O(m)) = (m+1)(m+2)(m+3)/6`.
* `p3ChCoeff_lineBundle_two`, `p3ChCoeff_lineBundle_three` — the class used there really is
  `O(m)`: its Chern character is `e^{mH}` in codimensions two and three.
-/

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- The Todd coefficients of `ℙ³` against the powers of `H`. -/
def p3Todd : ℕ → ℚ
  | 0 => 1
  | 1 => 2
  | 2 => 11 / 6
  | 3 => 1
  | _ + 4 => 0

/-- The Euler characteristic on `ℙ³` in linear-section coordinates.

Every generator is the structure sheaf of a linear subspace, and `χ(O_{ℙᵏ}) = 1` for each of
them, so `χ` is the plain sum of the coordinates. That this agrees with Riemann–Roch is the
`hchi` obligation discharged in `p3NumericalVariety`. -/
def p3Chi : ThreefoldNum →+ ℤ where
  toFun E := E 0 + E 1 + E 2 + E 3
  map_zero' := rfl
  map_add' E F := by
    show (E 0 + F 0) + (E 1 + F 1) + (E 2 + F 2) + (E 3 + F 3)
      = (E 0 + E 1 + E 2 + E 3) + (F 0 + F 1 + F 2 + F 3)
    ring

/-- **The model.** `ℙ³`, with `∫H³ = 1` and `td = 1 + 2H + (11/6)H² + H³`. -/
@[reducible]
noncomputable def p3NumericalVariety : NumericalVarietyData 3 (RankOneRing 3) ThreefoldNum :=
  rankOneNumericalVariety 3 1 threefoldRank p3Chi (threefoldChCoeff 1) p3Todd
    (threefoldChCoeff_zero 1) (threefoldChCoeff_add 1) rfl

/-- The explicit projective-three-space presentation satisfies HRR. -/
theorem p3NumericalVariety_satisfiesHRR : p3NumericalVariety.SatisfiesHRR :=
  rankOneNumericalVariety_satisfiesHRR 3 1 threefoldRank p3Chi (threefoldChCoeff 1) p3Todd
    (threefoldChCoeff_zero 1) (threefoldChCoeff_add 1) rfl (fun E => by
    rw [threefoldChi_sum]
    show ((E 0 + E 1 + E 2 + E 3 : ℤ) : ℚ)
      = 1 * ((E 0 : ℚ) * 1 + (E 1 : ℚ) * (11 / 6)
        + (-(E 1 : ℚ) / 2 + (E 2 : ℚ)) * 2
        + ((E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ) / 1) * 1)
    push_cast
    ring)

/-- `∫_{ℙ³} td₃ = χ(O_{ℙ³}) = 1`. -/
theorem p3ChiStructureSheaf :
    Threefold.chiStructureSheaf p3NumericalVariety = 1 := by
  show rankOneDegree 3 1 (rankOneTodd 3 p3Todd 3) = 1
  rw [rankOneTodd, rankOneDegree_algebraMap_mul_pow]
  norm_num [p3Todd]

/-- **Riemann–Roch on `ℙ³` reproduces `χ(O(m)) = (m+1)(m+2)(m+3)/6`.**

`O(mH)` is the class `(1, m, c, e)` with `2c = m(m+1)` and `6e = m(m+1)(m+2)`; those are the
binomial coefficients `C(m+1,2)` and `C(m+2,3)`, so the class is integral for every `m`,
including negative `m`. Stated cleared of denominators to stay in `ℤ`. -/
theorem p3Chi_lineBundle (m c e : ℤ) (hc : 2 * c = m * (m + 1))
    (he : 6 * e = m * (m + 1) * (m + 2)) :
    6 * p3Chi ![1, m, c, e] = (m + 1) * (m + 2) * (m + 3) := by
  show 6 * (1 + m + c + e) = (m + 1) * (m + 2) * (m + 3)
  linear_combination 3 * hc + he

/-- The class of `p3Chi_lineBundle` really has `ch₂ = m²/2`. Without this and its
codimension-three companion, `p3Chi_lineBundle` would only be arithmetic about a quadruple. -/
theorem p3ChCoeff_lineBundle_two (m c e : ℤ) (hc : 2 * c = m * (m + 1)) :
    threefoldChCoeff 1 ![1, m, c, e] 2 = (m : ℚ) ^ 2 / 2 := by
  show -(m : ℚ) / 2 + (c : ℚ) = (m : ℚ) ^ 2 / 2
  have h : (2 : ℚ) * (c : ℚ) = (m : ℚ) * ((m : ℚ) + 1) := by exact_mod_cast hc
  linarith

/-- The class of `p3Chi_lineBundle` really has `ch₃ = m³/6`. -/
theorem p3ChCoeff_lineBundle_three (m c e : ℤ) (hc : 2 * c = m * (m + 1))
    (he : 6 * e = m * (m + 1) * (m + 2)) :
    threefoldChCoeff 1 ![1, m, c, e] 3 = (m : ℚ) ^ 3 / 6 := by
  show (m : ℚ) / 6 - (c : ℚ) + (e : ℚ) / 1 = (m : ℚ) ^ 3 / 6
  have hc' : (2 : ℚ) * (c : ℚ) = (m : ℚ) * ((m : ℚ) + 1) := by exact_mod_cast hc
  have he' : (6 : ℚ) * (e : ℚ) = (m : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) + 2) := by exact_mod_cast he
  field_simp
  linarith [hc', he']

end Examples

end AlgebraicGeometry.Numerical
