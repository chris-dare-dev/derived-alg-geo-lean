/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Fourfold.LinearSection
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Fourfold

/-!
# The numerical model of `ℙ⁴`

The first model of `NumericalVarietyData` in dimension four, and the one that exercises every
term of `Fourfold.chi_eq`: all five Todd coefficients of `ℙ⁴` are nonzero, so no term is
multiplied by zero and an error anywhere in the display formula is visible here.

The data: `Pic ℙ⁴ = ℤ·H` with `∫H⁴ = 1`, and

`td(ℙ⁴) = 1 + (5/2)H + (35/12)H² + (25/12)H³ + H⁴`,

from `c₁ = 5H` and `c₂ = 10H²`: `td₁ = c₁/2`, `td₂ = (c₁² + c₂)/12 = (25 + 10)/12`,
`td₃ = c₁c₂/24 = 50/24`, and `td₄` normalised by `χ(O) = 1`.

## Main definitions

* `p4NumericalVariety` — the model.

## Main results

* `p4ChiStructureSheaf` — `∫_{ℙ⁴} td₄ = χ(O_{ℙ⁴}) = 1`.
* `p4Chi_lineBundle` — Riemann–Roch on this model reproduces
  `χ(O(m)) = (m+1)(m+2)(m+3)(m+4)/24`.
* `p4ChCoeff_lineBundle_four` — the class used there really is `O(m)`: its Chern character is
  `e^{mH}` in codimension four, which is the only check on the `7/12` and `−3/2` of
  `Examples/Fourfold/LinearSection.lean`.
-/

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- The Todd coefficients of `ℙ⁴` against the powers of `H`. -/
def p4Todd : ℕ → ℚ
  | 0 => 1
  | 1 => 5 / 2
  | 2 => 35 / 12
  | 3 => 25 / 12
  | 4 => 1
  | _ + 5 => 0

/-- The Euler characteristic on `ℙ⁴` in linear-section coordinates. Every generator is the
structure sheaf of a linear subspace, with `χ(O_{ℙᵏ}) = 1`, so `χ` is the sum of the
coordinates. -/
def p4Chi : FourfoldNum →+ ℤ where
  toFun E := E 0 + E 1 + E 2 + E 3 + E 4
  map_zero' := rfl
  map_add' E F := by
    show (E 0 + F 0) + (E 1 + F 1) + (E 2 + F 2) + (E 3 + F 3)
        + (E 4 + F 4)
      = (E 0 + E 1 + E 2 + E 3 + E 4)
        + (F 0 + F 1 + F 2 + F 3 + F 4)
    ring

/-- **The model.** `ℙ⁴`, with `∫H⁴ = 1` and `td = 1 + (5/2)H + (35/12)H² + (25/12)H³ + H⁴`. -/
@[reducible]
noncomputable def p4NumericalVariety : NumericalVarietyData 4 (RankOneRing 4) FourfoldNum :=
  rankOneNumericalVariety 4 1 fourfoldRank p4Chi (fourfoldChCoeff 1) p4Todd
    (fourfoldChCoeff_zero 1) (fourfoldChCoeff_add 1) rfl

/-- The explicit projective-four-space presentation satisfies HRR. -/
theorem p4NumericalVariety_satisfiesHRR : p4NumericalVariety.SatisfiesHRR :=
  rankOneNumericalVariety_satisfiesHRR 4 1 fourfoldRank p4Chi (fourfoldChCoeff 1) p4Todd
    (fourfoldChCoeff_zero 1) (fourfoldChCoeff_add 1) rfl (fun E => by
    rw [fourfoldChi_sum]
    show ((E 0 + E 1 + E 2 + E 3 + E 4 : ℤ) : ℚ)
      = 1 * ((E 0 : ℚ) * 1 + (E 1 : ℚ) * (25 / 12)
        + (-(E 1 : ℚ) / 2 + (E 2 : ℚ)) * (35 / 12)
        + ((E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ)) * (5 / 2)
        + (-(E 1 : ℚ) / 24 + 7 * (E 2 : ℚ) / 12 - 3 * (E 3 : ℚ) / 2
            + (E 4 : ℚ) / 1) * 1)
    push_cast
    ring)

/-- `∫_{ℙ⁴} td₄ = χ(O_{ℙ⁴}) = 1`. -/
theorem p4ChiStructureSheaf :
    Fourfold.chiStructureSheaf p4NumericalVariety = 1 := by
  show rankOneDegree 4 1 (rankOneTodd 4 p4Todd 4) = 1
  rw [rankOneTodd, rankOneDegree_algebraMap_mul_pow]
  norm_num [p4Todd]

/-- **Riemann–Roch on `ℙ⁴` reproduces `χ(O(m)) = (m+1)(m+2)(m+3)(m+4)/24`.**

`O(mH)` is the class `(1, m, c, e, f)` whose coordinates are the binomial coefficients
`C(m+1,2)`, `C(m+2,3)` and `C(m+3,4)`; the hypotheses state them cleared of denominators, so
the class is integral for every `m`. -/
theorem p4Chi_lineBundle (m c e f : ℤ) (hc : 2 * c = m * (m + 1))
    (he : 6 * e = m * (m + 1) * (m + 2))
    (hf : 24 * f = m * (m + 1) * (m + 2) * (m + 3)) :
    24 * p4Chi ![1, m, c, e, f] = (m + 1) * (m + 2) * (m + 3) * (m + 4) := by
  show 24 * (1 + m + c + e + f) = (m + 1) * (m + 2) * (m + 3) * (m + 4)
  linear_combination 12 * hc + 4 * he + hf

/-- The class of `p4Chi_lineBundle` really has `ch₄ = m⁴/24`, the top Chern-character
component of `e^{mH}`. This is the coefficient the `7/12` and `−3/2` of
`Examples/Fourfold/LinearSection.lean` feed into, so it is where a transcription error in
those numbers would surface. -/
theorem p4ChCoeff_lineBundle_four (m c e f : ℤ) (hc : 2 * c = m * (m + 1))
    (he : 6 * e = m * (m + 1) * (m + 2))
    (hf : 24 * f = m * (m + 1) * (m + 2) * (m + 3)) :
    fourfoldChCoeff 1 ![1, m, c, e, f] 4 = (m : ℚ) ^ 4 / 24 := by
  show -(m : ℚ) / 24 + 7 * (c : ℚ) / 12 - 3 * (e : ℚ) / 2 + (f : ℚ) / 1 = (m : ℚ) ^ 4 / 24
  have hc' : (2 : ℚ) * (c : ℚ) = (m : ℚ) * ((m : ℚ) + 1) := by exact_mod_cast hc
  have he' : (6 : ℚ) * (e : ℚ) = (m : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) + 2) := by exact_mod_cast he
  have hf' : (24 : ℚ) * (f : ℚ)
      = (m : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) := by exact_mod_cast hf
  field_simp
  linarith [hc', he', hf']

end Examples

end AlgebraicGeometry.Numerical
