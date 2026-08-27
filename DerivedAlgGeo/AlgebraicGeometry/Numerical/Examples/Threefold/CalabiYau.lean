/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Threefold.LinearSection
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Threefold

/-!
# The quintic Calabi–Yau threefold

A smooth quintic hypersurface `X ⊂ ℙ⁴`, and the model that makes
`AlgebraicGeometry.Numerical.CalabiYauThreefold` inhabited. Until this file,
`CalabiYauThreefold.chi_eq` and `CalabiYauThreefold.chi_eq_of_chComp_eq` were conditional on
a `NumericalVarietyData 3 A N` satisfying `IsCalabiYau` existing at all, which the module
docstring of `Numerical/Specializations/Threefold.lean` recorded as the outstanding gap.

The data: `∫_X H³ = 5`, `K_X = 0`, and `∫_X c₂(X)·H = 50`, so

`td(X) = 1 + 0 + (5/6)H² + 0`.

The `(5/6)` is forced: `td₂ = c₂/12` must satisfy `∫_X H·td₂ = 50/12`, and `∫_X H³ = 5`
turns that into the coefficient `50/(12·5) = 5/6`. The top coefficient is zero because
`td₃ = c₁c₂/24 = 0`, i.e. `χ(O_X) = 0` — the numerical signature of a Calabi–Yau threefold.

## The lattice, and why its Euler characteristics are the check

Linear-section coordinates (see `Examples/Threefold/LinearSection.lean`) make `χ` an integer
by construction, and here they also make it *verifiable*, because each generator is a
classical variety with a classical Euler characteristic:

| generator | what it is | `χ` |
|---|---|---|
| `[O_X]` | the Calabi–Yau threefold | `0` |
| `[O_{X∩H}]` | a smooth quintic surface in `ℙ³` | `5` |
| `[O_{X∩H²}]` | a plane quintic curve, genus `6` | `−5` |
| `[O_pt]` | a point | `1` |

Those four numbers are computed independently of this file — `C(d−1,3) + 1 = 5` for a degree
`d = 5` surface in `ℙ³`, and `1 − g = 1 − 6` for a plane quintic — and they are exactly what
`quinticChi` returns. That agreement is what makes the Todd coefficient above a checked
number rather than a chosen one.

## Main definitions

* `quinticNumericalVariety` — the model.

## Main results

* `quintic_isCalabiYau` — the model satisfies `CalabiYauThreefold.IsCalabiYau`.
* `quinticChi_lineBundle` — `χ(O_X(m)) = 5m(m² + 5)/6`, which is `5` at `m = 1` and `0` at
  `m = 0`, as the quintic's embedding in `ℙ⁴` by the complete system `|H|`, with
  `h⁰(O_X(1)) = 5`, requires.

## References

* Hartshorne, *Algebraic Geometry*, I.7 and V.1
* Griffiths–Harris, *Principles of Algebraic Geometry*, ch. 4
-/

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- The Todd coefficients of a quintic Calabi–Yau threefold against the powers of `H`. -/
def quinticTodd : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | 2 => 5 / 6
  | 3 => 0
  | _ + 4 => 0

/-- The Euler characteristic on the quintic in linear-section coordinates. See the module
docstring for the four generator values this encodes. -/
def quinticChi : ThreefoldNum →+ ℤ where
  toFun E := 5 * E 1 - 5 * E 2 + E 3
  map_zero' := rfl
  map_add' E F := by
    show 5 * (E 1 + F 1) - 5 * (E 2 + F 2) + (E 3 + F 3)
      = (5 * E 1 - 5 * E 2 + E 3) + (5 * F 1 - 5 * F 2 + F 3)
    ring

/-- **The model.** A smooth quintic threefold in `ℙ⁴`: `∫H³ = 5`, `td = 1 + (5/6)H²`. -/
@[reducible]
noncomputable def quinticNumericalVariety :
    NumericalVarietyData 3 (RankOneRing 3) ThreefoldNum :=
  rankOneNumericalVariety 3 5 threefoldRank quinticChi (threefoldChCoeff 5) quinticTodd
    (threefoldChCoeff_zero 5) (threefoldChCoeff_add 5) rfl

/-- Substituting the quintic Todd coefficients into the rank-one HRR polynomial recovers the
integer-valued Euler formula in linear-section coordinates. -/
theorem quinticNumericalVariety_satisfiesHRR : quinticNumericalVariety.SatisfiesHRR :=
  rankOneNumericalVariety_satisfiesHRR 3 5 threefoldRank quinticChi (threefoldChCoeff 5)
    quinticTodd (threefoldChCoeff_zero 5) (threefoldChCoeff_add 5) rfl (fun E => by
    rw [threefoldChi_sum]
    show ((5 * E 1 - 5 * E 2 + E 3 : ℤ) : ℚ)
      = 5 * ((E 0 : ℚ) * 0 + (E 1 : ℚ) * (5 / 6)
        + (-(E 1 : ℚ) / 2 + (E 2 : ℚ)) * 0
        + ((E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ) / 5) * 1)
    push_cast
    ring)

/-- The model really is a Calabi–Yau threefold: `td₁ = 0` and `∫_X td₃ = χ(O_X) = 0`.

With this presentation and its property witnesses, every theorem in the
`CalabiYauThreefold` namespace — in particular
`chi_eq_of_chComp_eq`, that `χ` cannot see the rank — is a statement about an object that
exists. -/
theorem quintic_isCalabiYau :
    CalabiYauThreefold.IsCalabiYau quinticNumericalVariety := by
  constructor
  · show algebraMap ℚ (RankOneRing 3) (quinticTodd 1) * rankOneH 3 ^ 1 = 0
    show algebraMap ℚ (RankOneRing 3) 0 * rankOneH 3 ^ 1 = 0
    rw [map_zero, zero_mul]
  · show rankOneDegree 3 5 (algebraMap ℚ (RankOneRing 3) (quinticTodd 3) * rankOneH 3 ^ 3) = 0
    rw [rankOneDegree_algebraMap_mul_pow]
    norm_num [quinticTodd]

/-- `χ(O_X) = 0` — the Calabi–Yau signature, read off the coordinates. -/
theorem quinticChi_structureSheaf : quinticChi ![1, 0, 0, 0] = 0 := rfl

/-- `χ(O_{X∩H}) = 5`: a hyperplane section of the quintic is a smooth quintic surface in
`ℙ³`, and a degree-`d` surface in `ℙ³` has `χ(O) = C(d−1,3) + 1`, which is `5` at `d = 5`. -/
theorem quinticChi_hyperplaneSection : quinticChi ![0, 1, 0, 0] = 5 := rfl

/-- `χ(O_{X∩H²}) = −5`: a codimension-two linear section of the quintic is a plane quintic
curve, of genus `(5−1)(5−2)/2 = 6`, so `χ(O) = 1 − 6`. -/
theorem quinticChi_curveSection : quinticChi ![0, 0, 1, 0] = -5 := rfl

/-- `χ(O_pt) = 1`. -/
theorem quinticChi_point : quinticChi ![0, 0, 0, 1] = 1 := rfl

/-- **Riemann–Roch on the quintic reproduces `χ(O_X(m)) = 5m(m² + 5)/6`.**

`O(mH)` is the class `(1, m, c, e)` with `2c = m(m+1)` and `6e = 5m(m+1)(m+2)`; the extra
factor of `5` relative to `ℙ³` is the point class `[pt] = H³/5`. Stated cleared of
denominators to stay in `ℤ`.

At `m = 1` this gives `5`, which is `h⁰(O_X(1)) = 5` for the quintic embedded in `ℙ⁴`; at
`m = 0` it gives `0 = χ(O_X)`. Both are independent checks on the Todd coefficient. -/
theorem quinticChi_lineBundle (m c e : ℤ) (hc : 2 * c = m * (m + 1))
    (he : 6 * e = 5 * (m * (m + 1) * (m + 2))) :
    6 * quinticChi ![1, m, c, e] = 5 * (m * (m ^ 2 + 5)) := by
  show 6 * (5 * m - 5 * c + e) = 5 * (m * (m ^ 2 + 5))
  linear_combination (-15) * hc + he

end Examples

end AlgebraicGeometry.Numerical
