/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Fourfold.LinearSection
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Fourfold

/-!
# The sextic Calabi–Yau fourfold

A smooth sextic hypersurface `X ⊂ ℙ⁵`, and the model that makes
`AlgebraicGeometry.Numerical.CalabiYauFourfold` inhabited.

The data: `∫_X H⁴ = 6`, `K_X = 0`, and the Chern classes of a degree-six hypersurface in
`ℙ⁵`, which the normal-bundle sequence `0 → T_X → T_{ℙ⁵}|_X → O_X(6) → 0` and the Whitney
sum formula give as `c(X) = (1+H)⁶/(1+6H)`, hence `c₂ = 15H²` and `c₄ = 435H⁴`. Adjunction
is the `c₁` half of that same computation: `K_X = (K_{ℙ⁵} + 6H)|_X = 0`. Hence

`td(X) = 1 + 0 + (5/4)H² + 0 + (1/3)H⁴`,

with `td₂ = c₂/12 = 15/12` and `td₄ = (3c₂² − c₄)/720 = (675 − 435)/720 = 1/3`. The top
coefficient is the one worth checking: `∫_X td₄ = 6 · (1/3) = 2`, which is `χ(O_X)` for a
Calabi–Yau fourfold, where `h^{0,i} = 1, 0, 0, 0, 1`. A threefold's `χ(O_X)` is `0`; a
fourfold's is `2`, and that difference is the whole reason `CalabiYauFourfold.IsCalabiYau`
carries a value rather than a vanishing.

## The lattice, and why its Euler characteristics are the check

As on the quintic, the linear-section generators are classical varieties whose Euler
characteristics are known independently:

| generator | what it is | `χ` |
|---|---|---|
| `[O_X]` | the Calabi–Yau fourfold | `2` |
| `[O_{X∩H}]` | a smooth sextic threefold in `ℙ⁴`, `h^{3,0} = C(5,4) = 5` | `−4` |
| `[O_{X∩H²}]` | a smooth sextic surface in `ℙ³`, `χ(O) = C(5,3) + 1` | `11` |
| `[O_{X∩H³}]` | a plane sextic curve, genus `10` | `−9` |
| `[O_pt]` | a point | `1` |

All five agree with what `sexticChi` returns, which is what makes `td₂` and `td₄` above
checked numbers rather than transcribed ones.

## Main definitions

* `sexticNumericalVariety` — the model.

## Main results

* `sextic_isCalabiYau` — the model satisfies `CalabiYauFourfold.IsCalabiYau`.
* `sexticChi_lineBundle` — `χ(O_X(m)) = (m⁴ + 15m² + 8)/4`, which is `6` at `m = 1` and `2`
  at `m = 0`.

## References

* Hartshorne, *Algebraic Geometry*, I.7 and V.1
* Griffiths–Harris, *Principles of Algebraic Geometry*, ch. 4
-/

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- The Todd coefficients of a sextic Calabi–Yau fourfold against the powers of `H`. -/
def sexticTodd : ℕ → ℚ
  | 0 => 1
  | 1 => 0
  | 2 => 5 / 4
  | 3 => 0
  | 4 => 1 / 3
  | _ + 5 => 0

/-- The Euler characteristic on the sextic in linear-section coordinates. See the module
docstring for the five generator values this encodes. -/
def sexticChi : FourfoldNum →+ ℤ where
  toFun E := 2 * E 0 - 4 * E 1 + 11 * E 2 - 9 * E 3 + E 4
  map_zero' := rfl
  map_add' E F := by
    show 2 * (E 0 + F 0) - 4 * (E 1 + F 1) + 11 * (E 2 + F 2)
        - 9 * (E 3 + F 3) + (E 4 + F 4)
      = (2 * E 0 - 4 * E 1 + 11 * E 2 - 9 * E 3 + E 4)
        + (2 * F 0 - 4 * F 1 + 11 * F 2 - 9 * F 3 + F 4)
    ring

/-- **The model.** A smooth sextic fourfold in `ℙ⁵`: `∫H⁴ = 6`,
`td = 1 + (5/4)H² + (1/3)H⁴`. -/
@[reducible]
noncomputable def sexticNumericalVariety :
    NumericalVarietyData 4 (RankOneRing 4) FourfoldNum :=
  rankOneNumericalVariety 4 6 fourfoldRank sexticChi (fourfoldChCoeff 6) sexticTodd
    (fourfoldChCoeff_zero 6) (fourfoldChCoeff_add 6) rfl

/-- Substituting the sextic Todd coefficients into the rank-one HRR polynomial recovers the
integer-valued Euler formula in linear-section coordinates. -/
theorem sexticNumericalVariety_satisfiesHRR : sexticNumericalVariety.SatisfiesHRR :=
  rankOneNumericalVariety_satisfiesHRR 4 6 fourfoldRank sexticChi (fourfoldChCoeff 6)
    sexticTodd (fourfoldChCoeff_zero 6) (fourfoldChCoeff_add 6) rfl (fun E => by
    rw [fourfoldChi_sum]
    show ((2 * E 0 - 4 * E 1 + 11 * E 2 - 9 * E 3 + E 4 : ℤ) : ℚ)
      = 6 * ((E 0 : ℚ) * (1 / 3) + (E 1 : ℚ) * 0
        + (-(E 1 : ℚ) / 2 + (E 2 : ℚ)) * (5 / 4)
        + ((E 1 : ℚ) / 6 - (E 2 : ℚ) + (E 3 : ℚ)) * 0
        + (-(E 1 : ℚ) / 24 + 7 * (E 2 : ℚ) / 12 - 3 * (E 3 : ℚ) / 2
            + (E 4 : ℚ) / 6) * 1)
    push_cast
    ring)

/-- The model really is a Calabi–Yau fourfold: `td₁ = td₃ = 0` and `∫_X td₄ = χ(O_X) = 2`.

The third condition is the one with content — it is the only place the degree `∫H⁴ = 6` and
the Todd coefficient `1/3` have to agree — and it is why this file computes `c₄ = 435H⁴`
rather than normalising `td₄` to whatever makes the answer come out. -/
theorem sextic_isCalabiYau :
    CalabiYauFourfold.IsCalabiYau sexticNumericalVariety := by
  refine ⟨?_, ?_, ?_⟩
  · show algebraMap ℚ (RankOneRing 4) (sexticTodd 1) * rankOneH 4 ^ 1 = 0
    show algebraMap ℚ (RankOneRing 4) 0 * rankOneH 4 ^ 1 = 0
    rw [map_zero, zero_mul]
  · show algebraMap ℚ (RankOneRing 4) (sexticTodd 3) * rankOneH 4 ^ 3 = 0
    show algebraMap ℚ (RankOneRing 4) 0 * rankOneH 4 ^ 3 = 0
    rw [map_zero, zero_mul]
  · show rankOneDegree 4 6 (algebraMap ℚ (RankOneRing 4) (sexticTodd 4) * rankOneH 4 ^ 4) = 2
    rw [rankOneDegree_algebraMap_mul_pow]
    norm_num [sexticTodd]

/-- `χ(O_X) = 2` — the Calabi–Yau fourfold signature, read off the coordinates. -/
theorem sexticChi_structureSheaf : sexticChi ![1, 0, 0, 0, 0] = 2 := rfl

/-- `χ(O_{X∩H}) = −4`: a hyperplane section of the sextic fourfold is a smooth sextic
threefold in `ℙ⁴`, whose only nonzero Hodge number off the structure sheaf is
`h^{3,0} = C(d−1,4) = 5`, so `χ(O) = 1 − 5`. -/
theorem sexticChi_hyperplaneSection : sexticChi ![0, 1, 0, 0, 0] = -4 := rfl

/-- `χ(O_{X∩H²}) = 11`: a codimension-two linear section is a smooth sextic surface in `ℙ³`,
with `χ(O) = C(d−1,3) + 1 = 11`. -/
theorem sexticChi_surfaceSection : sexticChi ![0, 0, 1, 0, 0] = 11 := rfl

/-- `χ(O_{X∩H³}) = −9`: a codimension-three linear section is a plane sextic curve, of genus
`(6−1)(6−2)/2 = 10`, so `χ(O) = 1 − 10`. -/
theorem sexticChi_curveSection : sexticChi ![0, 0, 0, 1, 0] = -9 := rfl

/-- `χ(O_pt) = 1`. -/
theorem sexticChi_point : sexticChi ![0, 0, 0, 0, 1] = 1 := rfl

/-- **Riemann–Roch on the sextic reproduces `χ(O_X(m)) = (m⁴ + 15m² + 8)/4`.**

`O(mH)` is the class `(1, m, c, e, f)` with `2c = m(m+1)`, `6e = m(m+1)(m+2)` and
`4f = m(m+1)(m+2)(m+3)`. The denominator there is `4` rather than the `24` of `ℙ⁴` because
the point class is `[pt] = H⁴/6`, so `f = 6·C(m+3,4)` and `24·C(m+3,4)` clears to `4f`; it
is an integer because a product of four consecutive integers is divisible by `24`.

At `m = 1` this gives `6`, which is `h⁰(O_X(1)) = 6` for the sextic embedded in `ℙ⁵`; at
`m = 0` it gives `2 = χ(O_X)`. -/
theorem sexticChi_lineBundle (m c e f : ℤ) (hc : 2 * c = m * (m + 1))
    (he : 6 * e = m * (m + 1) * (m + 2))
    (hf : 4 * f = m * (m + 1) * (m + 2) * (m + 3)) :
    4 * sexticChi ![1, m, c, e, f] = m ^ 4 + 15 * m ^ 2 + 8 := by
  show 4 * (2 * 1 - 4 * m + 11 * c - 9 * e + f) = m ^ 4 + 15 * m ^ 2 + 8
  linear_combination 22 * hc - 6 * he + hf

end Examples

end AlgebraicGeometry.Numerical
