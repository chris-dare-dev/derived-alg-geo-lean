/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.RankOne

/-!
# Linear-section coordinates on a Picard-rank-one fourfold

The dimension-four counterpart of `Examples/Threefold/LinearSection.lean`, with the same
justification: a class is recorded by its multiplicities against

`[O_X], [O_{X∩H}], [O_{X∩H²}], [O_{X∩H³}], [O_pt]`,

and `ch(O_{X∩Hᵏ}) = (1 − e^{−H})ᵏ` by the Koszul resolution. Expanding through codimension
four:

* `k = 1`: `H − H²/2 + H³/6 − H⁴/24`
* `k = 2`: `H² − H³ + (7/12)H⁴`
* `k = 3`: `H³ − (3/2)H⁴`
* `k = 4`: `H⁴`, and a point is `H⁴/d` because `∫_X H⁴ = d`.

The `7/12` and `−3/2` are the terms that make dimension four more than a longer version of
dimension three: they are the first coefficients of `(1 − e^{−H})ᵏ` that are neither `±1` nor
a reciprocal factorial, so a model that got them wrong would still produce integral `χ` on
three of its five generators.

## Main definitions

* `FourfoldNum` — the coordinates `(a, b, c, e, f)`.
* `fourfoldChCoeff` — the Chern-character coefficients on a fourfold of degree `d`.

## Main results

* `fourfoldChCoeff_add` — additivity.
* `fourfoldChi_sum` — the Riemann–Roch sum with `Finset.range 5` expanded.

## References

* Hartshorne, *Algebraic Geometry*, I.7 and V.1
* Griffiths–Harris, *Principles of Algebraic Geometry*, ch. 4
-/

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- A class on a Picard-rank-one fourfold, in linear-section coordinates: `(a, b, c, e, f)`
stands for `a·[O_X] + b·[O_{X∩H}] + c·[O_{X∩H²}] + e·[O_{X∩H³}] + f·[O_pt]`. -/
abbrev FourfoldNum : Type := Fin 5 → ℤ

/-- The Chern-character coefficients of a class in linear-section coordinates on a fourfold
of degree `∫_X H⁴ = d`. The coefficient of `Hⁱ` is entry `i`. The `7/12` and `−3/2` in
entries `4` and `3` are the terms that do not follow the threefold pattern; see the module
docstring for the expansion of `(1 − e^{−H})ᵏ` they come from. -/
noncomputable def fourfoldChCoeff (d : ℚ) (E : FourfoldNum) : ℕ → ℚ
  | 0 => (E 0 : ℚ)
  | 1 => (E 1 : ℚ)
  | 2 => -(E 1 : ℚ) / 2 + (E 2 : ℚ)
  | 3 => (E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ)
  | 4 => -(E 1 : ℚ) / 24 + 7 * (E 2 : ℚ) / 12 - 3 * (E 3 : ℚ) / 2
      + (E 4 : ℚ) / d
  | _ + 5 => 0

theorem fourfoldChCoeff_add (d : ℚ) (E F : FourfoldNum) (i : ℕ) :
    fourfoldChCoeff d (E + F) i = fourfoldChCoeff d E i + fourfoldChCoeff d F i := by
  match i with
  | 0 | 1 => simp only [fourfoldChCoeff, Pi.add_apply, Int.cast_add]
  | 2 | 3 | 4 =>
    simp only [fourfoldChCoeff, Pi.add_apply, Int.cast_add]
    ring
  | _ + 5 => simp only [fourfoldChCoeff, add_zero]

/-- The rank of a class in linear-section coordinates is its `[O_X]` multiplicity: the other
four generators are supported in positive codimension. -/
def fourfoldRank : FourfoldNum →+ ℤ where
  toFun E := E 0
  map_zero' := rfl
  map_add' _ _ := rfl

theorem fourfoldChCoeff_zero (d : ℚ) (E : FourfoldNum) :
    fourfoldChCoeff d E 0 = (fourfoldRank E : ℚ) := rfl

/-- The Riemann–Roch sum of `rankOneNumericalVariety`, with `Finset.range 5` expanded and the
`4 − i` reductions performed. -/
theorem fourfoldChi_sum (d : ℚ) (t : ℕ → ℚ) (E : FourfoldNum) :
    (∑ i ∈ Finset.range (4 + 1), fourfoldChCoeff d E i * t (4 - i))
      = (E 0 : ℚ) * t 4 + (E 1 : ℚ) * t 3
        + (-(E 1 : ℚ) / 2 + (E 2 : ℚ)) * t 2
        + ((E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ)) * t 1
        + (-(E 1 : ℚ) / 24 + 7 * (E 2 : ℚ) / 12 - 3 * (E 3 : ℚ) / 2
            + (E 4 : ℚ) / d) * t 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [show (4 : ℕ) - 0 = 4 from rfl, show (4 : ℕ) - 1 = 3 from rfl,
    show (4 : ℕ) - 2 = 2 from rfl, show (4 : ℕ) - 3 = 1 from rfl,
    show (4 : ℕ) - 4 = 0 from rfl]
  rfl

end Examples

end AlgebraicGeometry.Numerical
