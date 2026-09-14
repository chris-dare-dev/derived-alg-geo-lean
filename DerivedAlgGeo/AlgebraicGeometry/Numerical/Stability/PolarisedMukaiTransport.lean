/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialMukai
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialWallTransport
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.PolarisedWallTransport
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.PolarisedWallTransportComparison

/-!
# The correction slot at `√td`: the transport there is the Mukai charge

`PolarisedWallTransport.lean` carries a correction class `κ` as a parameter and
says of it that `κ = 1` gives the plain Chern character and `κ = √td` gives the
Mukai vector.  Only the first of those had an inhabitant.  `corrComp_sqrtToddComp`
proved the *class map* at `√td` is `mukaiComp` by `rfl`, but nothing tied the
resulting **charge** to the Mukai charge the repository already had, so the
claim that `κ = √td` produces the K3 Mukai charge rested on a docstring.

This file proves it, for an arbitrary surface realization and with no K3
hypothesis.  The K3 statement is a corollary.

## Why the comparison is pointwise, and why that is not a weakness

No equality of `ChargeFamily`s is statable here, and the reason is structural
rather than a shortfall of the proof.  `Polarised.wallChargeFamily` is indexed
by `ℂ`; `mukaiCharge` is indexed by `StabilityParameters D`, a pair of
independent divisor classes.  The two carriers sit over different data bundles,
and the map between the parameter spaces exists only on the rank-one slice
`B = sH`, `ω = tH`, where `Surface.NumericalRealization.rankOneParameters`
already provides it.  So the comparison is stated pointwise on that slice,
exactly as `wallChargeFamily_charge_eq_centralCharge` states the `κ = 1` case.

## `κ = 1` and `κ = √td` are two pullbacks, not one family

They are genuinely different walls and must not be fused.  The difference is
`mukaiCharge_eq_centralCharge_add` (`Walls/Divisorial/Mukai.lean`), which is
linear in the class and nonzero whenever `√td` is: on a K3 it shifts the third
Mukai coordinate by the rank, which is what turns `(r, c₁, ch₂)` into
Bridgeland's `(r, c₁, ch₂ + r)`.

## `SqrtTodd` is an image, not a truncation

`Wall.Divisorial.SqrtTodd` keeps a codimension-one class and one real number.
It is what a *realization* of `κ` can see, not a truncation of `κ` itself: the
map forgetting slots `0` and above `2` is lossy, and `√td₀ = 1` is dropped by
it rather than preserved.  `NumericalRealization.sqrtTodd` (`DivisorialMukai.lean`)
is that image, and the three slot lemmas below are where the loss is accounted
for — slot `0` reappears as the `∫H²` weight and nowhere else.

## Main results

* `hDegrees_sqrtToddComp_eq_mukaiVector` — the transported degrees at `κ = √td`
  are the compressed Mukai vector.  This is the whole content; the charges then
  agree because they are the same polynomial.
* `wallChargeFamily_sqrtToddComp_eq_mukaiCharge` — the comparison, for any
  surface realization.
* `wallChargeFamily_sqrtToddComp_eq_mukaiCharge_k3` — the K3 corollary, through
  `mukaiCharge_of_isK3`.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

universe u v w

namespace AlgebraicGeometry.Numerical.Surface

noncomputable section

variable {A : Type u} {N : Type v} {D : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable [AddCommGroup D] [Module ℝ D]

namespace NumericalRealization

variable {V : NumericalVarietyData 2 A N}
variable (R : NumericalRealization V.ring (D := D))
variable (P : Polarization V.ring)

/-- The realized polarisation pairs with any realized codimension-one class to
that class's rational `H`-degree.  `pair_realizePolarization_chOne`
(`DivisorialWallTransport.lean`) is the `ch₁` case of this; `√td₁` needs the
same fact and is not a Chern component. -/
theorem pair_realizePolarization_divisorClass (x : V.ring.piece 1) :
    R.divisorSpace.pair (R.realizePolarization P) (R.divisorClass x)
      = ((V.ring.degree (P.cls * x.1) : ℚ) : ℝ) := by
  change R.divisorSpace.pair
      (R.divisorClass ⟨P.cls, P.cls_mem⟩) (R.divisorClass x) = _
  rw [R.intersection_eq]

/-- Pairing the realized polarisation against a realized class plus a real
multiple of another.  This is the exact shape slot 1 of the Mukai vector takes:
`c₁ + r·√td₁`, with the scalar a real rank rather than a rational one. -/
theorem pair_realizePolarization_add_smul (x y : V.ring.piece 1) (r : ℝ) :
    R.divisorSpace.pair (R.realizePolarization P)
        (R.divisorClass x + r • R.divisorClass y)
      = ((V.ring.degree (P.cls * x.1) : ℚ) : ℝ)
        + r * ((V.ring.degree (P.cls * y.1) : ℚ) : ℝ) := by
  rw [DivisorSpace.pair_apply, map_add, map_smul, smul_eq_mul,
    ← DivisorSpace.pair_apply, ← DivisorSpace.pair_apply,
    R.pair_realizePolarization_divisorClass P x,
    R.pair_realizePolarization_divisorClass P y]

/-- **The transported degrees at `κ = √td` are the compressed Mukai vector.**

Slot by slot: `∫H²·r`, `∫H·(c₁ + r√td₁)`, and `∫(ch₂ + ch₁√td₁ + r√td₂)`.  The
middle and last are the two places `√td` enters, and the first is where the
polarisation weight lives — `√td₀ = 1` contributes there and is invisible in
`SqrtTodd`, which is the loss the module docstring names. -/
theorem hDegrees_sqrtToddComp_eq_mukaiVector (E : N) :
    Polarised.hDegrees V P V.sqrtToddComp 2 E
      = ![R.divisorSpace.pair (R.realizePolarization P) (R.realizePolarization P)
            * (R.chernCharacter.mukaiVector R.divisorSpace (R.sqrtTodd (V := V)) E).1,
          R.divisorSpace.pair (R.realizePolarization P)
            (R.chernCharacter.mukaiVector R.divisorSpace (R.sqrtTodd (V := V)) E).2.1,
          (R.chernCharacter.mukaiVector R.divisorSpace (R.sqrtTodd (V := V)) E).2.2] := by
  have hsq := R.pair_realizePolarization_self P
  funext k
  fin_cases k
  · -- slot 0: `∫H² · r`, the only slot `√td₀ = 1` touches
    show ((V.ring.degree (Polarised.corrComp V V.sqrtToddComp E 0 * P.cls ^ (2 - 0)) : ℚ) : ℝ)
      = _
    rw [Polarised.corrComp_sqrtToddComp, V.mukaiComp_zero,
      NumericalRingData.degree_algebraMap_mul]
    simp only [ChernCharacter.mukaiVector_apply, chernCharacter_rank, hsq]
    push_cast
    ring
  · -- slot 1: `∫H · (c₁ + r√td₁)`
    show ((V.ring.degree (Polarised.corrComp V V.sqrtToddComp E 1 * P.cls ^ (2 - 1)) : ℚ) : ℝ)
      = _
    have hmu : Polarised.corrComp V V.sqrtToddComp E 1
        = algebraMap ℚ A (V.rank E : ℚ) * V.sqrtToddComp 1 + V.chComp E 1 := by
      rw [Polarised.corrComp_sqrtToddComp, NumericalVarietyData.mukaiComp,
        Finset.sum_range_succ, Finset.sum_range_one, V.chComp_zero,
        V.sqrtToddComp_zero, mul_one]
    simp only [ChernCharacter.mukaiVector_apply, chernCharacter_rank,
      chernCharacter_chOne, sqrtTodd_divisor]
    rw [R.pair_realizePolarization_add_smul P, hmu, pow_one, add_mul, map_add,
      mul_assoc, NumericalRingData.degree_algebraMap_mul,
      show V.sqrtToddComp 1 * P.cls = P.cls * V.sqrtToddComp 1 from by ring,
      show V.chComp E 1 * P.cls = P.cls * V.chComp E 1 from by ring]
    push_cast
    ring
  · -- slot 2: `∫(ch₂ + ch₁√td₁ + r√td₂)`
    show ((V.ring.degree (Polarised.corrComp V V.sqrtToddComp E 2 * P.cls ^ (2 - 2)) : ℚ) : ℝ)
      = _
    have hmu : Polarised.corrComp V V.sqrtToddComp E 2
        = algebraMap ℚ A (V.rank E : ℚ) * V.sqrtToddComp 2
          + V.chComp E 1 * V.sqrtToddComp 1 + V.chComp E 2 := by
      rw [Polarised.corrComp_sqrtToddComp, NumericalVarietyData.mukaiComp,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
        V.chComp_zero, V.sqrtToddComp_zero, mul_one]
    simp only [ChernCharacter.mukaiVector_apply, chernCharacter_rank, chernCharacter_chOne,
      chernCharacter_chTwo, sqrtTodd_divisor, sqrtTodd_number]
    rw [pow_zero, mul_one, hmu, map_add, map_add,
      NumericalRingData.degree_algebraMap_mul]
    show _ = ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ)
        + R.divisorSpace.pair
            (R.divisorClass ⟨V.sqrtToddComp 1, V.sqrtToddComp_mem 1⟩)
            (R.divisorClass ⟨V.chComp E 1, V.chComp_mem E 1⟩)
        + (V.rank E : ℝ) * ((V.ring.degree (V.sqrtToddComp 2) : ℚ) : ℝ)
    rw [R.intersection_eq,
      show V.chComp E 1 * V.sqrtToddComp 1 = V.sqrtToddComp 1 * V.chComp E 1 from by ring]
    push_cast
    ring

/-- **The correction slot has a real inhabitant.**

The polarised transport at `κ = √td`, on the rank-one slice `B = sH`, `ω = tH`,
**is** the repository's Mukai charge.  No K3 hypothesis: this holds for every
surface realization, and the K3 case is the corollary below.

Both sides are the same exponential polynomial — the left through
`Exp.charge` on compressed degrees, the right through `Mukai.expCharge` on the
intersection form — so once the degrees are known to be the Mukai vector
(`hDegrees_sqrtToddComp_eq_mukaiVector`) the charges agree by the rank-one
collapse of the keystone. -/
theorem wallChargeFamily_sqrtToddComp_eq_mukaiCharge (p : ℝ × ℝ) (E : N) :
    (Polarised.wallChargeFamily V P V.sqrtToddComp 2).charge (Wall.Exp.stChart p) E
      = R.chernCharacter.mukaiCharge R.divisorSpace (R.sqrtTodd (V := V))
          (R.rankOneParameters P p) E := by
  rw [Polarised.wallChargeFamily_charge, ChernCharacter.mukaiCharge_apply,
    rankOneParameters, expCharge_rankOne_eq_charge,
    ← R.hDegrees_sqrtToddComp_eq_mukaiVector P E]

/-- **The K3 corollary.**  On a K3 the transport at `κ = √td` is the ordinary
divisorial charge minus the rank.

It is a corollary and not the statement: `mukaiCharge_of_isK3` is what supplies
`√td = 1 + [pt]`, and the comparison above holds without it. -/
theorem wallChargeFamily_sqrtToddComp_eq_mukaiCharge_k3 (hK3 : K3.IsK3 V)
    (p : ℝ × ℝ) (E : N) :
    (Polarised.wallChargeFamily V P V.sqrtToddComp 2).charge (Wall.Exp.stChart p) E
      = R.chernCharacter.centralCharge R.divisorSpace (R.rankOneParameters P p) E
        - Complex.ofReal ((V.rank E : ℤ) : ℝ) := by
  rw [R.wallChargeFamily_sqrtToddComp_eq_mukaiCharge P p E,
    R.mukaiCharge_of_isK3 hK3]

end NumericalRealization

/-! ### The two correction values are not one family

The block above needs a realization, because `mukaiCharge` lives on a real
divisor space.  The statement below needs none: it compares the two values of
`κ` against each other, and both sides are built from `V` and `P` alone. -/

/-- On a K3 the `√td`-corrected degrees are the plain ones with the rank added
to the last slot, and nothing else moved.

`√td₁ = 0` is what leaves slots `0` and `1` alone, and `∫√td₂ = 1` is what puts
exactly the rank into slot `2`.  Those are `K3.sqrtToddComp_one` and
`K3.degree_sqrtToddComp_two`; no other K3 input is used. -/
theorem hDegrees_sqrtToddComp_k3 {V : NumericalVarietyData 2 A N}
    (P : Polarization V.ring) (hK3 : K3.IsK3 V) (E : N) :
    Polarised.hDegrees V P V.sqrtToddComp 2 E
      = Polarised.hDegrees V P (Polarised.unitCorr A) 2 E
        + ![0, 0, (((V.rank E : ℤ) : ℚ) : ℝ)] := by
  have hone : V.sqrtToddComp 1 = 0 := K3.sqrtToddComp_one hK3
  funext k
  fin_cases k
  · show ((V.ring.degree (Polarised.corrComp V V.sqrtToddComp E 0 * P.cls ^ (2 - 0)) : ℚ) : ℝ)
      = ((V.ring.degree (Polarised.corrComp V (Polarised.unitCorr A) E 0
          * P.cls ^ (2 - 0)) : ℚ) : ℝ) + _
    rw [Polarised.corrComp_sqrtToddComp, Polarised.corrComp_unitCorr, V.mukaiComp_zero,
      V.chComp_zero]
    show _ = _ + (0 : ℝ)
    rw [add_zero]
  · have hmu : Polarised.corrComp V V.sqrtToddComp E 1 = V.chComp E 1 := by
      rw [Polarised.corrComp_sqrtToddComp, NumericalVarietyData.mukaiComp,
        Finset.sum_range_succ, Finset.sum_range_one, V.sqrtToddComp_zero, mul_one,
        show (1 : ℕ) - 0 = 1 from rfl, hone, mul_zero, zero_add]
    show ((V.ring.degree (Polarised.corrComp V V.sqrtToddComp E 1 * P.cls ^ (2 - 1)) : ℚ) : ℝ)
      = ((V.ring.degree (Polarised.corrComp V (Polarised.unitCorr A) E 1
          * P.cls ^ (2 - 1)) : ℚ) : ℝ) + _
    rw [hmu, Polarised.corrComp_unitCorr]
    show _ = _ + (0 : ℝ)
    rw [add_zero]
  · have hmu : Polarised.corrComp V V.sqrtToddComp E 2
        = algebraMap ℚ A (V.rank E : ℚ) * V.sqrtToddComp 2 + V.chComp E 2 := by
      rw [Polarised.corrComp_sqrtToddComp, NumericalVarietyData.mukaiComp,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
        V.chComp_zero, V.sqrtToddComp_zero, mul_one,
        show (2 : ℕ) - 1 = 1 from rfl, hone, mul_zero, add_zero]
    show ((V.ring.degree (Polarised.corrComp V V.sqrtToddComp E 2 * P.cls ^ (2 - 2)) : ℚ) : ℝ)
      = ((V.ring.degree (Polarised.corrComp V (Polarised.unitCorr A) E 2
          * P.cls ^ (2 - 2)) : ℚ) : ℝ) + _
    rw [hmu, Polarised.corrComp_unitCorr, pow_zero, mul_one, mul_one, map_add,
      NumericalRingData.degree_algebraMap_mul, K3.degree_sqrtToddComp_two hK3, mul_one]
    show ((_ + _ : ℚ) : ℝ) = _ + (((V.rank E : ℤ) : ℚ) : ℝ)
    push_cast
    ring

/-- **The two correction values give different charges, and the difference is
the rank.**

On a K3 the `κ = √td` transport is the `κ = 1` transport of
`WallTransport.lean` minus the rank — an additive term linear in the class, so
the two are not a reparameterisation of each other and their walls genuinely
differ.  This is what makes "do not fuse the two pullbacks" a theorem rather
than a warning in a docstring.

No realization appears: both sides are built from `V` and `P`. -/
theorem wallChargeFamily_sqrtToddComp_sub_unitCorr_k3
    {V : NumericalVarietyData 2 A N} (P : Polarization V.ring) (hK3 : K3.IsK3 V)
    (p : ℝ × ℝ) (E : N) :
    (Polarised.wallChargeFamily V P V.sqrtToddComp 2).charge (Wall.Exp.stChart p) E
      = (wallChargeFamily V P).charge p E - (((V.rank E : ℤ) : ℚ) : ℝ) := by
  have hrank : (Wall.Exp.charge 2 (Wall.Exp.stChart p))
      ![0, 0, (((V.rank E : ℤ) : ℚ) : ℝ)] = -((((V.rank E : ℤ) : ℚ) : ℝ) : ℂ) := by
    rw [Wall.Exp.charge_apply, Wall.Exp.ofMoments]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [Wall.Exp.moments, Wall.Exp.coeff, Nat.factorial]
  rw [Polarised.surface_wallChargeFamily_eq V P, Wall.ChargeFamily.reindex_charge,
    Polarised.wallChargeFamily_charge, Polarised.wallChargeFamily_charge,
    hDegrees_sqrtToddComp_k3 P hK3 E, map_add, hrank]
  ring


end

end AlgebraicGeometry.Numerical.Surface
