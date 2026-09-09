/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialChargeNumerical
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Slice
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.WallTransport

/-!
# The `(s,t)` transport is the rank-one slice of the divisorial family

`WallTransport.lean` pulls the three-coordinate `(s,t)` charge family back to a
polarised numerical surface through the degree-weighted `toNumClassHom`.
`DivisorialWallSlice.lean` builds the arbitrary-`(B,ω)` charge family of a real
divisor space from a full `ChernCharacter`.  Until this file, those two
descendants of `Wall.ChargeFamily` had no theorem connecting them: the
hierarchy was a forest with two formula owners, `reZ`/`imZ` on one side and
`ChernCharacter.centralCharge` on the other.

For any `NumericalRealization` of the surface's rational intersection ring in
a real divisor space, the two families agree exactly: the compressed `(s,t)`
family is the reindexing of the intrinsic divisorial family along the rank-one
slice `B = sH`, `ω = tH`, where `H` is the realized polarisation.  Consequently
every rank-one child (the K3 model included) reaches both the circle, line,
disjointness, and nesting theorems of the `(s,t)` polynomial and the
arbitrary-`(B,ω)` divisorial layer, and the wall loci of the two presentations
coincide pointwise.

Nothing here is geometric: the identity is a match of two arithmetic
presentations of `-∫ ch₂^B + (ω²/2) ch₀ + i ω·ch₁^B`.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

universe u v w

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical.Surface

noncomputable section

variable {A : Type u} {N : Type v} {D : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable [AddCommGroup D] [Module ℝ D]

namespace NumericalRealization

variable {V : NumericalVarietyData 2 A N}
variable (R : NumericalRealization V.ring (D := D))
variable (P : Polarization V.ring)

/-- The rank-one slice parameters `B = sH`, `ω = tH` of a realized
polarisation, indexed by the `(s,t)` plane of `WallTransport.lean`. -/
def rankOneParameters (p : ℝ × ℝ) : StabilityParameters D :=
  StabilityParameters.rankOne (R.realizePolarization P) p.2 p.1

@[simp]
theorem rankOneParameters_B (p : ℝ × ℝ) :
    (R.rankOneParameters P p).B = p.1 • R.realizePolarization P := rfl

@[simp]
theorem rankOneParameters_omega (p : ℝ × ℝ) :
    (R.rankOneParameters P p).omega = p.2 • R.realizePolarization P := rfl

/-- The realized polarisation pairs with the realized first Chern class to the
rational `H`-degree. -/
theorem pair_realizePolarization_chOne (E : N) :
    R.divisorSpace.pair (R.realizePolarization P) (R.chernCharacter.chOne E) =
      ((degH V P E : ℚ) : ℝ) := by
  change R.divisorSpace.pair
      (R.divisorClass ⟨P.cls, P.cls_mem⟩)
      (R.divisorClass ⟨V.chComp E 1, V.chComp_mem E 1⟩) = _
  rw [R.intersection_eq]
  unfold degH
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_comm]

/-- The realized polarisation has the rational polarisation square. -/
theorem pair_realizePolarization_self :
    R.divisorSpace.pair (R.realizePolarization P) (R.realizePolarization P) =
      ((V.ring.degree (P.cls ^ 2) : ℚ) : ℝ) := by
  change R.divisorSpace.pair
      (R.divisorClass ⟨P.cls, P.cls_mem⟩)
      (R.divisorClass ⟨P.cls, P.cls_mem⟩) = _
  rw [R.intersection_eq, pow_two]

/-- **The two branches of the wall hierarchy agree.**  The degree-weighted
`(s,t)` charge of `WallTransport.lean` is the intrinsic divisorial charge at
`B = sH`, `ω = tH`. -/
theorem wallChargeFamily_charge_eq_centralCharge (p : ℝ × ℝ) (E : N) :
    (wallChargeFamily V P).charge p E =
      R.chernCharacter.centralCharge R.divisorSpace (R.rankOneParameters P p) E := by
  rw [wallChargeFamily_charge, rankOneParameters,
    ChernCharacter.centralCharge_rankOne_eq]
  apply Complex.ext
  · rw [Wall.stCharge_re, ChargeCoordinates.centralCharge_re]
    simp only [ChargeCoordinates.twistByScalar_chTwo,
      ChargeCoordinates.twistByScalar_hyperplaneSquare,
      ChargeCoordinates.twistByScalar_rank, ChernCharacter.coordinatesAt_chTwo,
      ChernCharacter.coordinatesAt_degree, ChernCharacter.coordinatesAt_rank,
      ChernCharacter.coordinatesAt_hyperplaneSquare, chernCharacter_rank,
      chernCharacter_chTwo, R.pair_realizePolarization_chOne,
      R.pair_realizePolarization_self, Wall.reZ, toNumClass_rk, toNumClass_deg,
      toNumClass_ch2]
    push_cast
    ring
  · rw [Wall.stCharge_im, ChargeCoordinates.centralCharge_im]
    simp only [ChargeCoordinates.twistByScalar_degree,
      ChernCharacter.coordinatesAt_degree,
      ChernCharacter.coordinatesAt_rank, ChernCharacter.coordinatesAt_hyperplaneSquare,
      chernCharacter_rank, R.pair_realizePolarization_chOne,
      R.pair_realizePolarization_self, Wall.imZ, toNumClass_rk, toNumClass_deg]
    push_cast
    ring

/-- The compressed `(s,t)` family is literally the reindexing of the intrinsic
divisorial family along the rank-one slice. -/
theorem wallChargeFamily_eq_rankOne_reindex :
    wallChargeFamily V P =
      (R.chernCharacter.fullChargeFamily R.divisorSpace).reindex
        (R.rankOneParameters P) := by
  ext p E
  rw [Wall.ChargeFamily.reindex_charge, ChernCharacter.fullChargeFamily_charge]
  exact R.wallChargeFamily_charge_eq_centralCharge P p E

/-- The `(s,t)` wall of two classes is the rank-one slice of their divisorial
wall. -/
theorem wallChargeFamily_wall_eq (v w : N) :
    (wallChargeFamily V P).wall v w =
      R.rankOneParameters P ⁻¹'
        (R.chernCharacter.fullChargeFamily R.divisorSpace).wall v w := by
  rw [R.wallChargeFamily_eq_rankOne_reindex P, Wall.ChargeFamily.reindex_wall]

end NumericalRealization

end

end AlgebraicGeometry.Numerical.Surface
