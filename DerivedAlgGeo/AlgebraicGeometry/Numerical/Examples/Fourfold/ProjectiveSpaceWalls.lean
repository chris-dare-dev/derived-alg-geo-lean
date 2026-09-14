/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Fourfold.ProjectiveSpace
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.PolarisedWallTransport

/-!
# The wall layer of `ℙ⁴`, at zero polynomial cost

`Examples/Fourfold/ProjectiveSpace.lean` builds the `ℙ⁴` numerical model with
proved Riemann--Roch, and until this file nothing connected it to a charge: no
fourfold charge or wall family existed anywhere in the tree, because every
charge in the tree was written per dimension and nobody had written the
dimension-four one.

**This file writes no charge polynomial.** Its entire content is one
`Polarization`, after which `Polarised.wallChargeFamily` at `(n, m, κ) = (4, 4, 1)`
supplies the family and `Wall.Exp.ofMoments` supplies the polynomial. That is
the point of the slice: a new dimension costs a polarisation, not a charge.

## What the slots come out as

The transport's slot `k` is `∫ H^(4-k) · ch_k(E)`, and on a Picard-rank-one
model `∫ H^(4-k) · Hᵏ = ∫H⁴`. With `∫_{ℙ⁴} H⁴ = 1` the five slots are therefore
the linear-section Chern coefficients themselves, which is what
`p4_hDegrees_eq_chCoeff` says in one statement for all five. Slot `0` is
`E 0 = rank E`, which is the `∫H⁴ = 1` case of the root's `hDegrees_zero`; on
the sextic (`CalabiYauWalls.lean`) the same slot carries the factor `6` and the
weighting is visible.

`p4_charge` evaluates the family, and it is the only place the coefficients
`1, -1, 1/2, -1/6, 1/24` appear — read off `Wall.Exp.coeff`, not written down
here.

## The gap this slice records rather than fills

**The `n = 4` graded pairing has no counterpart in this repository.** There is
no fourfold discriminant, no fourfold self-pairing, and hence no comparison to
prove and no consumer to serve. The charge needs none of that — `ofMoments`
takes moments, and the scalar moments of a compressed degree vector are all the
family uses — so the slot is left genuinely empty. Inventing a pairing to fill
it would add a definition with no leaf reaching it, which is the failure the
abstraction tree's root-review clause exists to prevent.

## Main definitions

* `p4Polarization` — the hyperplane class of `ℙ⁴`, the first polarisation of a
  fourfold model in the repository.
* `p4WallChargeFamily` — the wall family, inherited rather than defined.

## Main results

* `p4_degree_H_pow_four` — `∫_{ℙ⁴} H⁴ = 1`.
* `p4_hDegrees_eq_chCoeff` — the five slots, in linear-section coordinates.
* `p4_charge` — the charge evaluated on those coordinates.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

/-! ### The polarization -/

/-- `∫_{ℙ⁴} H⁴ = 1`. -/
theorem p4_degree_H_pow_four :
    p4NumericalVariety.ring.degree (rankOneH 4 ^ 4) = 1 := by
  show rankOneDegree 4 1 (rankOneH 4 ^ 4) = 1
  rw [rankOneDegree_pow]
  norm_num

/-- **The hyperplane class as a polarization of `ℙ⁴`.**  The first polarization
of a fourfold model in the repository, and the entire cost of the wall layer
below. -/
def p4Polarization : Polarization p4NumericalVariety.ring where
  cls := rankOneH 4
  cls_mem := by
    have h := rankOneH_pow_mem_piece 4 1
    rwa [pow_one] at h
  degree_pow_pos := by
    rw [p4_degree_H_pow_four]
    norm_num

@[simp]
theorem p4Polarization_cls : p4Polarization.cls = rankOneH 4 := rfl

/-! ### The transported `H`-degrees -/

/-- Integration of a Chern-character component against a power of `H`: only the
total codimension four survives. -/
private theorem p4_degree_chComp_mul (i k : ℕ) (E : FourfoldNum) :
    p4NumericalVariety.ring.degree (p4NumericalVariety.chComp E i * rankOneH 4 ^ k)
      = fourfoldChCoeff 1 E i * (if i + k = 4 then 1 else 0) := by
  show rankOneDegree 4 1
      (algebraMap ℚ (RankOneRing 4) (fourfoldChCoeff 1 E i) * rankOneH 4 ^ i
        * rankOneH 4 ^ k) = _
  rw [mul_assoc, ← pow_add, rankOneDegree_algebraMap_mul_pow]

/-- **The five slots of `ℙ⁴`, all at once.**  Slot `k` is
`∫ H^(4-k) · ch_k(E) = ch_k(E)` because `∫_{ℙ⁴} H⁴ = 1`, so the compressed
degree vector is the linear-section coefficient sequence on the nose.

Stated for every `k : Fin 5` rather than five times: the `k`-dependence is
entirely inside `fourfoldChCoeff`, and the only fact about `k` the proof uses is
`k ≤ 4`, which is `Fin.isLt`. -/
theorem p4_hDegrees_eq_chCoeff (k : Fin 5) (E : FourfoldNum) :
    Polarised.hDegrees p4NumericalVariety p4Polarization
        (Polarised.unitCorr (RankOneRing 4)) 4 E k
      = ((fourfoldChCoeff 1 E (k : ℕ) : ℚ) : ℝ) := by
  have hk : (k : ℕ) ≤ 4 := Nat.lt_succ_iff.mp k.isLt
  show ((p4NumericalVariety.ring.degree
      (Polarised.corrComp p4NumericalVariety (Polarised.unitCorr (RankOneRing 4)) E (k : ℕ)
        * p4Polarization.cls ^ (4 - (k : ℕ))) : ℚ) : ℝ) = _
  rw [Polarised.corrComp_unitCorr, p4Polarization_cls, p4_degree_chComp_mul,
    if_pos (show (k : ℕ) + (4 - (k : ℕ)) = 4 by omega), mul_one]

/-! ### The charge family on the model -/

/-- **The wall family of `ℙ⁴`**, inherited from `Polarised.wallChargeFamily` at
`(n, m, κ) = (4, 4, 1)`.  No charge polynomial is written here or anywhere else
for dimension four; the polynomial is `Wall.Exp.ofMoments`. -/
def p4WallChargeFamily : Wall.ChargeFamily ℂ FourfoldNum :=
  Polarised.wallChargeFamily p4NumericalVariety p4Polarization
    (Polarised.unitCorr (RankOneRing 4)) 4

@[simp]
theorem p4WallChargeFamily_charge (w : ℂ) (E : FourfoldNum) :
    p4WallChargeFamily.charge w E
      = Wall.Exp.charge 4 w
          (Polarised.hDegrees p4NumericalVariety p4Polarization
            (Polarised.unitCorr (RankOneRing 4)) 4 E) := rfl

/-- **The `ℙ⁴` charge in linear-section coordinates.**

`Z(w) = -(ch₄ - w·ch₃ + w²/2·ch₂ - w³/6·ch₁ + w⁴/24·ch₀)`, which is
`-∫exp(-wH)·ch(E)` truncated at codimension four.  The five coefficients are
`Wall.Exp.coeff 0..4`; they are read off the kernel, not written down for this
model. -/
theorem p4_charge (w : ℂ) (E : FourfoldNum) :
    p4WallChargeFamily.charge w E
      = -(((fourfoldChCoeff 1 E 4 : ℚ) : ℂ)
          - w * ((fourfoldChCoeff 1 E 3 : ℚ) : ℂ)
          + w ^ 2 / 2 * ((fourfoldChCoeff 1 E 2 : ℚ) : ℂ)
          - w ^ 3 / 6 * ((fourfoldChCoeff 1 E 1 : ℚ) : ℂ)
          + w ^ 4 / 24 * ((fourfoldChCoeff 1 E 0 : ℚ) : ℂ)) := by
  rw [p4WallChargeFamily_charge, Wall.Exp.charge_apply, Wall.Exp.ofMoments]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Wall.Exp.moments, Nat.zero_le, Nat.le_refl, dif_pos,
    p4_hDegrees_eq_chCoeff]
  norm_num [Wall.Exp.coeff, Nat.factorial]
  ring

end

end Examples

end AlgebraicGeometry.Numerical
