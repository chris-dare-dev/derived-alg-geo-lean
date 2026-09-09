/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Charge
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.SurfaceChargeNumerical

/-!
# Real divisor realizations of numerical surface data

`NumericalRingData` stores a rational graded intersection ring, whereas a
surface stability condition uses divisor parameters in `N^1(X)_ℝ`.  This file
is the bridge between those layers.

A `Surface.NumericalRealization` sends the codimension-one piece of a numerical
intersection ring additively into a real divisor space, respects rational
scalars after the inclusion `ℚ → ℝ`, and identifies multiplication followed by
degree with the real intersection form.  Given any `NumericalVarietyData`
using that ring, it then constructs the full `ChernCharacter`; no
basis or Picard-rank hypothesis is involved.

The main compatibility theorem identifies the resulting intrinsic divisorial
charge at

`B = realize(B₀)`, `omega = a * realize(H)`

with the existing charge obtained directly from a rational `BField B₀` and a
`Polarization H`.  Thus the rational ring presentation is a source of concrete
children of `DivisorialCharge`, rather than a competing central-charge API.
-/

open Complex

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical.Surface

noncomputable section

universe u v w

variable {A : Type u} {N : Type v} {D : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable [AddCommGroup D] [Module ℝ D]

/-- A realization of rational numerical divisor classes in a real divisor
space, preserving the surface intersection form.

The scalar law is stated explicitly instead of asking typeclass inference to
choose a `ℚ`-module structure on `D`; the intended scalar action is always the
one obtained from `ℚ → ℝ`. -/
structure NumericalRealization (S : NumericalRingData 2 A) where
  /-- The real numerical divisor space. -/
  divisorSpace : DivisorSpace D
  /-- Realization of the rational codimension-one piece. -/
  divisorClass : S.piece 1 →+ D
  /-- Compatibility with extension of scalars from `ℚ` to `ℝ`. -/
  map_rat_smul : ∀ (q : ℚ) (x : S.piece 1),
    divisorClass (q • x) = (q : ℝ) • divisorClass x
  /-- Multiplication and degree compute the realized intersection pairing. -/
  intersection_eq : ∀ (x y : S.piece 1),
    divisorSpace.pair (divisorClass x) (divisorClass y) =
      ((S.degree (x.1 * y.1) : ℚ) : ℝ)

namespace NumericalRealization

variable {V : NumericalVarietyData 2 A N}
variable (R : NumericalRealization V.ring (D := D))

/-- The codimension-one Chern-character component as an additive map into its
graded piece. -/
def chOneClassHom (V : NumericalVarietyData 2 A N) : N →+ V.ring.piece 1 :=
  AddMonoidHom.mk'
    (fun E => ⟨V.chComp E 1, V.chComp_mem E 1⟩)
    (by
      intro E F
      ext
      exact V.chComp_add E F 1)

/-- The full real Chern character induced by a numerical surface
presentation. -/
def chernCharacter : ChernCharacter N D where
  rank := ChargeCoordinates.rankHom V
  chOne := R.divisorClass.comp (chOneClassHom V)
  chTwo := ChargeCoordinates.chTwoHom V

@[simp]
theorem chernCharacter_rank (E : N) :
    R.chernCharacter.rank E = (V.rank E : ℝ) := rfl

@[simp]
theorem chernCharacter_chOne (E : N) :
    R.chernCharacter.chOne E =
      R.divisorClass ⟨V.chComp E 1, V.chComp_mem E 1⟩ := rfl

@[simp]
theorem chernCharacter_chTwo (E : N) :
    R.chernCharacter.chTwo E =
      ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ) := rfl

/-- Realize a rational numerical `B`-field. -/
def realizeBField (B : BField V.ring) : D :=
  R.divisorClass ⟨B.cls, B.cls_mem⟩

/-- Realize the divisor class underlying a polarization. -/
def realizePolarization (P : Polarization V.ring) : D :=
  R.divisorClass ⟨P.cls, P.cls_mem⟩

/-- Parameters obtained from a rational `B`-field and a real multiple of a
realized polarization. -/
def parameters (P : Polarization V.ring) (B : BField V.ring) (a : ℝ) :
    StabilityParameters D where
  B := R.realizeBField B
  omega := a • R.realizePolarization P

/-- Realization commutes with the degree-one part of the `B`-twisted Chern
character. -/
theorem twist_chOne_eq (B : BField V.ring) (E : N) :
    (R.chernCharacter.twist R.divisorSpace (R.realizeBField B)).chOne E =
      R.divisorClass ⟨chBComp V B E 1, chBComp_mem V B E 1⟩ := by
  rw [ChernCharacter.twist_chOne]
  change R.divisorClass ⟨V.chComp E 1, V.chComp_mem E 1⟩ -
      (V.rank E : ℝ) • R.divisorClass ⟨B.cls, B.cls_mem⟩ =
    R.divisorClass ⟨chBComp V B E 1, chBComp_mem V B E 1⟩
  have htwist :
      (⟨chBComp V B E 1, chBComp_mem V B E 1⟩ : V.ring.piece 1) =
        ⟨V.chComp E 1, V.chComp_mem E 1⟩ -
          (V.rank E : ℚ) • ⟨B.cls, B.cls_mem⟩ := by
    apply Subtype.ext
    change chBComp V B E 1 =
      V.chComp E 1 - (V.rank E : ℚ) • B.cls
    rw [chBComp_one, V.chComp_zero]
    rw [Algebra.smul_def]
  rw [htwist, map_sub]
  have hcast : (((V.rank E : ℤ) : ℚ) : ℝ) = (V.rank E : ℝ) := by
    norm_cast
  rw [R.map_rat_smul, hcast]

/-- Realization commutes with the integrated degree-two part of the
`B`-twisted Chern character. -/
theorem twist_chTwo_eq (B : BField V.ring) (E : N) :
    (R.chernCharacter.twist R.divisorSpace (R.realizeBField B)).chTwo E =
      ((V.ring.degree (chBComp V B E 2) : ℚ) : ℝ) := by
  rw [ChernCharacter.twist_chTwo]
  simp only [chernCharacter_chTwo, chernCharacter_chOne, chernCharacter_rank,
    realizeBField]
  rw [R.intersection_eq, R.intersection_eq, chBComp_two, V.chComp_zero,
    map_add, map_sub]
  have hcomm : B.cls * V.chComp E 1 = V.chComp E 1 * B.cls := by ring
  rw [hcomm]
  have hquadratic :
      algebraMap ℚ A (1 / 2) * algebraMap ℚ A (V.rank E : ℚ) * B.cls ^ 2 =
        algebraMap ℚ A ((1 / 2) * (V.rank E : ℚ)) * B.cls ^ 2 := by
    rw [map_mul]
  rw [hquadratic, NumericalRingData.degree_algebraMap_mul, ← pow_two]
  push_cast
  ring

/-- The square of a realized, real-scaled polarization is the scalar extension
of its rational self-intersection. -/
theorem parameters_omega_square (P : Polarization V.ring)
    (B : BField V.ring) (a : ℝ) :
    R.divisorSpace.pair (R.parameters P B a).omega (R.parameters P B a).omega =
      a ^ 2 * ((V.ring.degree (P.cls ^ 2) : ℚ) : ℝ) := by
  change R.divisorSpace.pair
      (a • R.divisorClass ⟨P.cls, P.cls_mem⟩)
      (a • R.divisorClass ⟨P.cls, P.cls_mem⟩) = _
  have hpair := R.intersection_eq
    (⟨P.cls, P.cls_mem⟩ : V.ring.piece 1) ⟨P.cls, P.cls_mem⟩
  change R.divisorSpace.intersection
      (R.divisorClass ⟨P.cls, P.cls_mem⟩)
      (R.divisorClass ⟨P.cls, P.cls_mem⟩) = _ at hpair
  simp only [DivisorSpace.pair, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hpair]
  simp only [pow_two]
  ring

/-- Pairing the realized polarization with the realized twisted first Chern
class recovers the rational twisted degree. -/
theorem parameters_pair_twist_chOne (P : Polarization V.ring)
    (B : BField V.ring) (a : ℝ) (E : N) :
    R.divisorSpace.pair (R.parameters P B a).omega
        ((R.chernCharacter.twist R.divisorSpace (R.realizeBField B)).chOne E) =
      a * ((V.ring.degree (chBComp V B E 1 * P.cls) : ℚ) : ℝ) := by
  rw [R.twist_chOne_eq]
  change R.divisorSpace.pair
      (a • R.divisorClass ⟨P.cls, P.cls_mem⟩)
      (R.divisorClass ⟨chBComp V B E 1, chBComp_mem V B E 1⟩) = _
  have hpair := R.intersection_eq
    (⟨P.cls, P.cls_mem⟩ : V.ring.piece 1)
    ⟨chBComp V B E 1, chBComp_mem V B E 1⟩
  change R.divisorSpace.intersection
      (R.divisorClass ⟨P.cls, P.cls_mem⟩)
      (R.divisorClass ⟨chBComp V B E 1, chBComp_mem V B E 1⟩) = _ at hpair
  simp only [DivisorSpace.pair, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hpair]
  rw [mul_comm P.cls (chBComp V B E 1)]

/-- The intrinsic real divisorial charge agrees with the existing numerical
ring charge whenever `B` and the polarization come from the rational
presentation. -/
theorem centralCharge_eq_ofNumericalDataB
    (P : Polarization V.ring) (B : BField V.ring) (a : ℝ) (E : N) :
    R.chernCharacter.centralCharge R.divisorSpace (R.parameters P B a) E =
      (ChargeCoordinates.ofNumericalDataB V P B).centralCharge a E := by
  rw [ChernCharacter.centralCharge_apply_twisted,
    ChargeCoordinates.centralCharge_apply]
  rw [show (R.parameters P B a).B = R.realizeBField B from rfl]
  rw [R.twist_chTwo_eq,
    R.parameters_omega_square, R.parameters_pair_twist_chOne]
  simp only [ChargeCoordinates.ofNumericalDataB_rank,
    ChargeCoordinates.ofNumericalDataB_degree,
    ChargeCoordinates.ofNumericalDataB_chTwo,
    ChargeCoordinates.ofNumericalDataB_hyperplaneSquare,
    chernCharacter_rank]
  push_cast
  ring

end NumericalRealization

end

end AlgebraicGeometry.Numerical.Surface
