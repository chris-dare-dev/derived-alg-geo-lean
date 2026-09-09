/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.SqrtTodd
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialChargeNumerical
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Mukai

/-!
# `√td_X` read off a numerical realization, and Bridgeland's K3 charge

`Walls/Divisorial/Mukai.lean` owns the Mukai vector and the Mukai charge on an
abstract real divisor space, parameterized by a supplied `SqrtTodd`: the
codimension-one class `√td₁` and the number `∫√td₂`.  This file supplies that
datum from geometry rather than by hand, using the `sqrtToddComp` of
`Numerical/Mukai/SqrtTodd.lean`, and identifies the result on a K3.

Three things are proved.

* `sqrtTodd_eq_k3`: on a K3 the realized square root is `SqrtTodd.k3`, the
  formal content of `√td(X) = 1 + [pt]`.  It rests on `K3.sqrtToddComp_one` and
  `K3.degree_sqrtToddComp_two`, both already proved from `IsK3`; nothing new is
  assumed.
* `mukaiVector_snd_snd_of_isK3`: the third coordinate of the Mukai vector is
  `K3.mukaiS`, the repository's existing `s = rank + ∫ch₂`, and hence
  `K3.mukaiSInt = χ − rank` once Hirzebruch--Riemann--Roch is supplied.  This is
  what ties the new adapter to `GrothendieckGroup/MukaiVector.lean` and the K3
  model of `Examples/Surface/K3Mukai.lean` instead of leaving two unrelated
  notions of "Mukai vector" in the library.
* `mukaiCharge_of_isK3`: Bridgeland's charge is the ordinary divisorial charge
  minus the rank.

## What this does not do

It does not construct a numerical realization for the K3 model of
`Examples/Surface/K3.lean`; the statements below hold for any realization of any
`NumericalVarietyData 2` satisfying `IsK3`, and the K3 model's own realization
is a separate piece of work.  It also does not compare the real Mukai extension
used here with the integral `Mukai.MukaiLattice` of
`GrothendieckGroup/MukaiVector.lean`; that comparison needs a realization of the
integral lattice inside the real divisor space and is not attempted.
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

/-- **`√td_X` as a surface Mukai vector sees it**: the realized codimension-one
component and the integrated codimension-two component. -/
def sqrtTodd : SqrtTodd D where
  divisor := R.divisorClass ⟨V.sqrtToddComp 1, V.sqrtToddComp_mem 1⟩
  number := ((V.ring.degree (V.sqrtToddComp 2) : ℚ) : ℝ)

@[simp]
theorem sqrtTodd_divisor :
    (R.sqrtTodd (V := V)).divisor =
      R.divisorClass ⟨V.sqrtToddComp 1, V.sqrtToddComp_mem 1⟩ := rfl

@[simp]
theorem sqrtTodd_number :
    (R.sqrtTodd (V := V)).number =
      ((V.ring.degree (V.sqrtToddComp 2) : ℚ) : ℝ) := rfl

/-- **On a K3 the realized square root is `1 + [pt]`.**  This is
`K3.sqrtToddComp_one` and `K3.degree_sqrtToddComp_two` in the shape the Mukai
vector consumes. -/
theorem sqrtTodd_eq_k3 (hK3 : K3.IsK3 V) : R.sqrtTodd (V := V) = SqrtTodd.k3 := by
  have hone : (⟨V.sqrtToddComp 1, V.sqrtToddComp_mem 1⟩ : V.ring.piece 1) = 0 := by
    apply Subtype.ext
    exact K3.sqrtToddComp_one hK3
  apply congrArg₂ SqrtTodd.mk
  · rw [hone, map_zero]
  · rw [K3.degree_sqrtToddComp_two hK3]
    norm_num

/-- On a K3 the Mukai vector is `(rank, c₁, ∫ch₂ + rank)`. -/
theorem mukaiVector_of_isK3 (hK3 : K3.IsK3 V) (E : N) :
    R.chernCharacter.mukaiVector R.divisorSpace (R.sqrtTodd (V := V)) E =
      (((V.rank E : ℤ) : ℝ), R.chernCharacter.chOne E,
        ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ) + ((V.rank E : ℤ) : ℝ)) := by
  rw [R.sqrtTodd_eq_k3 hK3, ChernCharacter.mukaiVector_k3]
  rfl

/-- **The third Mukai coordinate is the repository's `K3.mukaiS`**, namely
`s = rank + ∫ch₂`.  This is what identifies the vector built here with the one
`GrothendieckGroup/MukaiVector.lean` already uses. -/
theorem mukaiVector_snd_snd_of_isK3 (hK3 : K3.IsK3 V) (E : N) :
    (R.chernCharacter.mukaiVector R.divisorSpace (R.sqrtTodd (V := V)) E).2.2 =
      ((K3.mukaiS V E : ℚ) : ℝ) := by
  rw [R.mukaiVector_of_isK3 hK3, K3.mukaiS]
  push_cast
  ring

/-- The same coordinate, as the integer `s = χ − rank` of
`K3.mukaiSInt`, once Hirzebruch--Riemann--Roch is supplied. -/
theorem mukaiVector_snd_snd_eq_mukaiSInt (hHRR : V.SatisfiesHRR) (hK3 : K3.IsK3 V) (E : N) :
    (R.chernCharacter.mukaiVector R.divisorSpace (R.sqrtTodd (V := V)) E).2.2 =
      ((K3.mukaiSInt V E : ℤ) : ℝ) := by
  rw [R.mukaiVector_snd_snd_of_isK3 hK3, ← K3.mukaiSInt_spec V hHRR hK3 E]
  norm_num

/-- **Bridgeland's K3 charge is the ordinary divisorial charge minus the
rank.**  The two presentations differ by an additive term linear in the class,
not by a scalar, so their walls differ. -/
theorem mukaiCharge_of_isK3 (hK3 : K3.IsK3 V) (P : StabilityParameters D) (E : N) :
    R.chernCharacter.mukaiCharge R.divisorSpace (R.sqrtTodd (V := V)) P E =
      R.chernCharacter.centralCharge R.divisorSpace P E
        - Complex.ofReal ((V.rank E : ℤ) : ℝ) := by
  rw [R.sqrtTodd_eq_k3 hK3, ChernCharacter.mukaiCharge_k3]
  rfl

end NumericalRealization

end

end AlgebraicGeometry.Numerical.Surface
