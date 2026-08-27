/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.RankOne

/-!
# Linear-section coordinates on a Picard-rank-one threefold

Both threefold models in this directory — `ℙ³` and the quintic Calabi–Yau — record a class
by its multiplicities against the flag of structure sheaves of linear sections

`[O_X], [O_{X ∩ H}], [O_{X ∩ H²}], [O_pt]`.

Those coordinates are shared, and so are the resulting Chern-character coefficients: the
Koszul resolution of a `k`-fold hyperplane section gives `ch(O_{X ∩ Hᵏ}) = (1 − e^{−H})ᵏ`,
which through codimension three is

* `k = 0`: `1`
* `k = 1`: `H − H²/2 + H³/6`
* `k = 2`: `H² − H³`
* `k = 3`: `H³`, and a point is `H³/d` because `∫_X H³ = d`.

The point class is the only place the degree enters, and it is why the coefficients are
parametrised by `d` rather than fixed.

## Why these coordinates

The alternative — recording `(r, c₁, ch₂, ch₃)` directly — cannot be a lattice: `ch₂` is a
half-integer and `ch₃` a sixth-integer, so `χ` would not land in `ℤ`. Exactly the same
problem forced the `(r, c, v)` coordinates in
`Examples/Surface/ProjectivePlane.lean`. Linear sections solve it structurally instead of by
a substitution chosen to work: every generator is an actual coherent sheaf, so its `χ` is an
integer by construction, and the integrality of `χ` on the whole lattice is then automatic
rather than something the model has to arrange.

## Main definitions

* `ThreefoldNum` — the coordinates `(a, b, c, e)`.
* `threefoldChCoeff` — the Chern-character coefficients of `a·[O_X] + b·[O_H] + c·[O_L] +
  e·[O_pt]` on a threefold of degree `d`.

## Main results

* `threefoldChCoeff_add` — additivity, the hypothesis `rankOneNumericalVariety` asks for.
* `threefoldChi_sum` — the Riemann–Roch sum with `Finset.range 4` expanded, so that each
  model closes its own Riemann–Roch obligation by `push_cast; ring`.

## References

* Hartshorne, *Algebraic Geometry*, I.7 and V.1
* Griffiths–Harris, *Principles of Algebraic Geometry*, ch. 4
-/

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- A class on a Picard-rank-one threefold, in linear-section coordinates: `(a, b, c, e)`
stands for `a·[O_X] + b·[O_{X∩H}] + c·[O_{X∩H²}] + e·[O_pt]`. -/
abbrev ThreefoldNum : Type := Fin 4 → ℤ

/-- The Chern-character coefficients of a class in linear-section coordinates on a threefold
of degree `∫_X H³ = d`. The coefficient of `Hⁱ` is entry `i`; see the module docstring for
where each number comes from. -/
noncomputable def threefoldChCoeff (d : ℚ) (E : ThreefoldNum) : ℕ → ℚ
  | 0 => (E 0 : ℚ)
  | 1 => (E 1 : ℚ)
  | 2 => -(E 1 : ℚ) / 2 + (E 2 : ℚ)
  | 3 => (E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ) / d
  | _ + 4 => 0

theorem threefoldChCoeff_add (d : ℚ) (E F : ThreefoldNum) (i : ℕ) :
    threefoldChCoeff d (E + F) i = threefoldChCoeff d E i + threefoldChCoeff d F i := by
  match i with
  | 0 | 1 => simp only [threefoldChCoeff, Pi.add_apply, Int.cast_add]
  | 2 | 3 =>
    simp only [threefoldChCoeff, Pi.add_apply, Int.cast_add]
    ring
  | _ + 4 => simp only [threefoldChCoeff, add_zero]

/-- The rank of a class in linear-section coordinates is its `[O_X]` multiplicity: the other
three generators are supported in positive codimension. -/
def threefoldRank : ThreefoldNum →+ ℤ where
  toFun E := E 0
  map_zero' := rfl
  map_add' _ _ := rfl

theorem threefoldChCoeff_zero (d : ℚ) (E : ThreefoldNum) :
    threefoldChCoeff d E 0 = (threefoldRank E : ℚ) := rfl

/-- The Riemann–Roch sum of `rankOneNumericalVariety`, with `Finset.range 4` expanded and the
`3 − i` reductions performed.

Each model then has a goal in the four Todd coefficients and nothing else, which is what
makes a new threefold cost a table of numbers rather than a proof. -/
theorem threefoldChi_sum (d : ℚ) (t : ℕ → ℚ) (E : ThreefoldNum) :
    (∑ i ∈ Finset.range (3 + 1), threefoldChCoeff d E i * t (3 - i))
      = (E 0 : ℚ) * t 3 + (E 1 : ℚ) * t 2
        + (-(E 1 : ℚ) / 2 + (E 2 : ℚ)) * t 1
        + ((E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ) / d) * t 0 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [show (3 : ℕ) - 0 = 3 from rfl, show (3 : ℕ) - 1 = 2 from rfl,
    show (3 : ℕ) - 2 = 1 from rfl, show (3 : ℕ) - 3 = 0 from rfl]
  rfl

end Examples

end AlgebraicGeometry.Numerical
