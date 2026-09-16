/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Fourfold.CalabiYau
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.PolarisedWallTransport

/-!
# The wall layer of the sextic Calabi--Yau fourfold

The second half of the fourfold slice, and the half that makes the weighting
visible.  `Models/Fourfold/CalabiYau.lean` builds the smooth sextic
`X ⊂ ℙ⁵` with `∫_X H⁴ = 6`; `ProjectiveSpaceWalls.lean` does the same job at
`∫H⁴ = 1`, where the polarisation degree is invisible because it is one.

As there, **no charge polynomial is written**.  The whole file is one
`Polarization` and the evaluations that follow from it.

## The degree is an overall factor, and only because the Picard rank is one

Slot `k` of the transport is `∫ H^(4-k) · ch_k(E)`, and on a rank-one model
`ch_k(E) = ch_k · Hᵏ` for a rational `ch_k`, so every slot integrates the same
top power and picks up the same `∫_X H⁴ = 6`.  Hence
`sextic_hDegrees_eq_chCoeff` carries the factor `6` in all five slots and
`sextic_charge` factors it out of the charge entirely.

That factorisation is a fact about Picard rank one, **not** about the
transport.  Slot `0` carries `∫Hⁿ` in every dimension and every Picard rank —
that is the root's `hDegrees_zero` — while the other slots carry it here only
because there is a single generator to integrate against.  On a model of higher
Picard rank the slots do not share a factor and the charge does not scale.

## `κ` stays at `1`

The correction class is `unitCorr`, so this is the plain Chern character and
not the Mukai vector, exactly as on `ℙ⁴`.  `td₁ = td₃ = 0` on a Calabi--Yau
fourfold, so `√td` differs from `1` only in codimensions two and four, and
`corrComp` at `sqrtToddComp` would produce a genuinely different family rather
than a rescaling of this one.  The two must not be fused; the correction slot's
inhabitant is the subject of its own slice.

## Main definitions

* `sexticPolarization` — the hyperplane class of the sextic.
* `sexticWallChargeFamily` — the wall family, inherited rather than defined.

## Main results

* `sextic_degree_H_pow_four` — `∫_X H⁴ = 6`.
* `sextic_hDegrees_eq_chCoeff` — the five slots, each weighted by `6`.
* `sextic_charge` — the charge, with the degree factored out.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

/-! ### The polarization -/

/-- `∫_X H⁴ = 6` for a smooth sextic fourfold in `ℙ⁵`. -/
theorem sextic_degree_H_pow_four :
    sexticNumericalVariety.ring.degree (rankOneH 4 ^ 4) = 6 := by
  show rankOneDegree 4 6 (rankOneH 4 ^ 4) = 6
  rw [rankOneDegree_pow]
  norm_num

/-- **The hyperplane class as a polarization of the sextic.**  Positivity of
`∫_X H⁴` is the degree `6`, so no Nakai--Moishezon input is needed here. -/
def sexticPolarization : Polarization sexticNumericalVariety.ring where
  cls := rankOneH 4
  cls_mem := by
    have h := rankOneH_pow_mem_piece 4 1
    rwa [pow_one] at h
  degree_pow_pos := by
    rw [sextic_degree_H_pow_four]
    norm_num

@[simp]
theorem sexticPolarization_cls : sexticPolarization.cls = rankOneH 4 := rfl

/-! ### The transported `H`-degrees -/

/-- Integration of a Chern-character component against a power of `H`: only the
total codimension four survives, and it integrates to `6`. -/
private theorem sextic_degree_chComp_mul (i k : ℕ) (E : FourfoldNum) :
    sexticNumericalVariety.ring.degree
        (sexticNumericalVariety.chComp E i * rankOneH 4 ^ k)
      = fourfoldChCoeff 6 E i * (if i + k = 4 then 6 else 0) := by
  show rankOneDegree 4 6
      (algebraMap ℚ (RankOneRing 4) (fourfoldChCoeff 6 E i) * rankOneH 4 ^ i
        * rankOneH 4 ^ k) = _
  rw [mul_assoc, ← pow_add, rankOneDegree_algebraMap_mul_pow]

/-- **The five slots of the sextic, all at once**, each carrying the
polarisation degree `∫_X H⁴ = 6`.

Compare `p4_hDegrees_eq_chCoeff`, where the same statement has no visible
factor because the degree is one.  Slot `0` here is `6 · rank E`, which is the
root's `hDegrees_zero` with the weight showing. -/
theorem sextic_hDegrees_eq_chCoeff (k : Fin 5) (E : FourfoldNum) :
    Polarised.hDegrees sexticNumericalVariety sexticPolarization
        (Polarised.unitCorr (RankOneRing 4)) 4 E k
      = ((fourfoldChCoeff 6 E (k : ℕ) * 6 : ℚ) : ℝ) := by
  have hk : (k : ℕ) ≤ 4 := Nat.lt_succ_iff.mp k.isLt
  show ((sexticNumericalVariety.ring.degree
      (Polarised.corrComp sexticNumericalVariety (Polarised.unitCorr (RankOneRing 4)) E (k : ℕ)
        * sexticPolarization.cls ^ (4 - (k : ℕ))) : ℚ) : ℝ) = _
  rw [Polarised.corrComp_unitCorr, sexticPolarization_cls, sextic_degree_chComp_mul,
    if_pos (show (k : ℕ) + (4 - (k : ℕ)) = 4 by omega)]

/-! ### The charge family on the model -/

/-- **The wall family of the sextic Calabi--Yau fourfold**, inherited from
`Polarised.wallChargeFamily` at `(n, m, κ) = (4, 4, 1)`.  The second fourfold
inhabitant, and the second one that costs no polynomial. -/
def sexticWallChargeFamily : Wall.ChargeFamily ℂ FourfoldNum :=
  Polarised.wallChargeFamily sexticNumericalVariety sexticPolarization
    (Polarised.unitCorr (RankOneRing 4)) 4

@[simp]
theorem sexticWallChargeFamily_charge (w : ℂ) (E : FourfoldNum) :
    sexticWallChargeFamily.charge w E
      = Wall.Exp.charge 4 w
          (Polarised.hDegrees sexticNumericalVariety sexticPolarization
            (Polarised.unitCorr (RankOneRing 4)) 4 E) := rfl

/-- **The sextic charge in linear-section coordinates.**

`Z(w) = -6·(ch₄ - w·ch₃ + w²/2·ch₂ - w³/6·ch₁ + w⁴/24·ch₀)`.  The factor `6` is
the polarisation degree, common to all five slots because the Picard rank is
one; see the module docstring for why that is not a property of the transport. -/
theorem sextic_charge (w : ℂ) (E : FourfoldNum) :
    sexticWallChargeFamily.charge w E
      = -(6 * (((fourfoldChCoeff 6 E 4 : ℚ) : ℂ)
          - w * ((fourfoldChCoeff 6 E 3 : ℚ) : ℂ)
          + w ^ 2 / 2 * ((fourfoldChCoeff 6 E 2 : ℚ) : ℂ)
          - w ^ 3 / 6 * ((fourfoldChCoeff 6 E 1 : ℚ) : ℂ)
          + w ^ 4 / 24 * ((fourfoldChCoeff 6 E 0 : ℚ) : ℂ))) := by
  rw [sexticWallChargeFamily_charge, Wall.Exp.charge_apply, Wall.Exp.ofMoments]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [Wall.Exp.moments, Nat.zero_le, Nat.le_refl, dif_pos,
    sextic_hDegrees_eq_chCoeff]
  norm_num [Wall.Exp.coeff, Nat.factorial]
  ring

end

end Examples

end AlgebraicGeometry.Numerical
