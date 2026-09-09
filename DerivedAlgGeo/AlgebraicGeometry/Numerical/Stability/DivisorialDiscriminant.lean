/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialWallTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Discriminant

/-!
# Discriminants of a realized numerical surface

`Walls/Divisorial/Discriminant.lean` owns the Macrì--Schmidt quadratic forms
(arXiv:1607.01262v3, Definition 6.12) on an abstract real divisor space, and
the `DivisorSpace.HodgeIndex` certificate.  This file is their geometric
adapter: it reads those forms off a `NumericalRealization` of a rational
numerical intersection ring and connects them to the numerical data of
`BogomolovGieseker.lean`.

The two Hodge certificates are related in one direction only.  A
`DivisorSpace.HodgeIndex` on the realized divisor space yields the numerical
`HodgeIndexStatement`, because the latter is the former restricted to first
Chern classes of numerical classes.  The converse is false as stated:
`HodgeIndexStatement` quantifies over classes `E : N`, not over arbitrary real
divisors, so it yields only `index_le_chOne_of_hodgeIndexStatement`.  That
asymmetry is deliberate and is the honest content of this file.

Bogomolov--Gieseker enters only as the supplied `BogomolovGiesekerData` of
`BogomolovGieseker.lean`; nothing here proves an inequality about sheaves.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

universe u v w

namespace AlgebraicGeometry.Numerical.Surface

noncomputable section

variable {A : Type u} {N : Type v} {D : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable [AddCommGroup D] [Module ℝ D]

/-! ### Through a numerical realization -/

namespace NumericalRealization

variable {V : NumericalVarietyData 2 A N}
variable (R : NumericalRealization V.ring (D := D))
variable (P : Polarization V.ring)

/-- The realized first Chern class has the rational self-intersection. -/
theorem pair_chOne_self (E : N) :
    R.divisorSpace.pair (R.chernCharacter.chOne E) (R.chernCharacter.chOne E) =
      ((V.ring.degree (V.chComp E 1 * V.chComp E 1) : ℚ) : ℝ) := by
  change R.divisorSpace.pair
      (R.divisorClass ⟨V.chComp E 1, V.chComp_mem E 1⟩)
      (R.divisorClass ⟨V.chComp E 1, V.chComp_mem E 1⟩) = _
  rw [R.intersection_eq]

/-- The intrinsic discriminant of the realized character is the integrated
numerical discriminant `∫Δ(E)`. -/
theorem discriminant_chernCharacter (E : N) :
    R.chernCharacter.discriminant R.divisorSpace E =
      ((V.ring.degree (V.discriminant E) : ℚ) : ℝ) := by
  rw [ChernCharacter.discriminant, R.pair_chOne_self, V.degree_discriminant]
  simp only [chernCharacter_rank, chernCharacter_chTwo]
  push_cast
  ring

/-- **A Hodge index inequality on the realized divisor space yields the
numerical `HodgeIndexStatement`**: the latter is the former restricted to first
Chern classes of numerical classes. -/
theorem hodgeIndexStatement_of_hodgeIndex
    (h : R.divisorSpace.HodgeIndex (R.realizePolarization P)) :
    HodgeIndexStatement V P where
  index_le E := by
    have hidx := h.index_le (R.chernCharacter.chOne E)
    rw [R.pair_realizePolarization_self P, R.pair_chOne_self,
      R.pair_realizePolarization_chOne P] at hidx
    exact_mod_cast hidx

/-- The numerical `HodgeIndexStatement` yields the index inequality on realized
first Chern classes.  It does not yield `DivisorSpace.HodgeIndex`, which
quantifies over every real class. -/
theorem index_le_chOne_of_hodgeIndexStatement (hI : HodgeIndexStatement V P) (E : N) :
    R.divisorSpace.pair (R.realizePolarization P) (R.realizePolarization P) *
        R.divisorSpace.pair (R.chernCharacter.chOne E) (R.chernCharacter.chOne E) ≤
      R.divisorSpace.pair (R.realizePolarization P) (R.chernCharacter.chOne E) ^ 2 := by
  rw [R.pair_realizePolarization_self P, R.pair_chOne_self,
    R.pair_realizePolarization_chOne P]
  exact_mod_cast hI.index_le E

/-- Bogomolov--Gieseker, transported: the intrinsic discriminant of a
semistable class is nonnegative.  `BogomolovGiesekerData` is the supplied
datum; nothing is proved about sheaves. -/
theorem discriminant_nonneg_of_semistable {E : N} (B : BogomolovGiesekerData V P)
    (hE : B.Semistable E) :
    0 ≤ R.chernCharacter.discriminant R.divisorSpace E := by
  rw [R.discriminant_chernCharacter]
  exact_mod_cast nonneg_degree_discriminant B hE

/-- **The bar discriminant of a semistable class is nonnegative at every
`(B, ω)` with a Hodge index at `ω`.**  This is the Bogomolov half of
Macrì--Schmidt Theorem 6.13 for slope-semistable classes; the Bridgeland
semistable half is not stated here. -/
theorem barDiscriminant_nonneg_of_semistable {E : N} (B : BogomolovGiesekerData V P)
    (hE : B.Semistable E) (Q : StabilityParameters D)
    (h : R.divisorSpace.HodgeIndex Q.omega) :
    0 ≤ R.chernCharacter.barDiscriminant R.divisorSpace Q E :=
  ChernCharacter.barDiscriminant_nonneg_of_discriminant_nonneg _ _ Q h E
    (R.discriminant_nonneg_of_semistable P B hE)

/-- On the rank-one slice `B = sH`, `ω = tH` of a realized polarisation the bar
discriminant is `t² · discrH`. -/
theorem barDiscriminant_rankOneParameters (p : ℝ × ℝ) (E : N) :
    R.chernCharacter.barDiscriminant R.divisorSpace (R.rankOneParameters P p) E =
      p.2 ^ 2 * ((discrH V P E : ℚ) : ℝ) := by
  rw [rankOneParameters, ChernCharacter.barDiscriminant_rankOne]
  simp only [ChargeCoordinates.discr, ChernCharacter.coordinatesAt_degree,
    ChernCharacter.coordinatesAt_rank, ChernCharacter.coordinatesAt_chTwo,
    ChernCharacter.coordinatesAt_hyperplaneSquare, chernCharacter_rank, chernCharacter_chTwo,
    R.pair_realizePolarization_chOne P, R.pair_realizePolarization_self P, discrH_eq]
  push_cast
  ring

/-- The same, against the wall-plane discriminant of the transported class:
the bar discriminant on the `(s,t)` slice is `t²` times
`Wall.NumClass.discr (toNumClass V P E)`. -/
theorem barDiscriminant_rankOneParameters_eq_discr_toNumClass (p : ℝ × ℝ) (E : N) :
    R.chernCharacter.barDiscriminant R.divisorSpace (R.rankOneParameters P p) E =
      p.2 ^ 2 * Wall.NumClass.discr (toNumClass V P E) := by
  rw [R.barDiscriminant_rankOneParameters P, discr_toNumClass]

/-- On the rank-one slice the bar discriminant of a semistable class is
nonnegative from the numerical data alone: `BogomolovGiesekerData` and the
numerical `HodgeIndexStatement`, with no real Hodge index at `ω` required. -/
theorem barDiscriminant_rankOneParameters_nonneg {E : N} (B : BogomolovGiesekerData V P)
    (hI : HodgeIndexStatement V P) (hE : B.Semistable E) (p : ℝ × ℝ) :
    0 ≤ R.chernCharacter.barDiscriminant R.divisorSpace (R.rankOneParameters P p) E := by
  rw [R.barDiscriminant_rankOneParameters P]
  have h := discrH_nonneg B hI hE
  have h' : (0 : ℝ) ≤ ((discrH V P E : ℚ) : ℝ) := by exact_mod_cast h
  positivity

end NumericalRealization

end

end AlgebraicGeometry.Numerical.Surface
