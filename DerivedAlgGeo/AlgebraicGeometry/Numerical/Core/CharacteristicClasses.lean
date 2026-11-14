/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Algebra.Rat

/-!
# Universal characteristic-class formulas

The Chern character and Todd class do not have separate definitions for surfaces,
threefolds, and fourfolds. They are universal power-series expressions; dimension only says
where the series truncates in a particular numerical ring.

This module records the components through codimension four, the range currently used by the
project. `ChernClassData A` is deliberately just algebraic input. The geometric construction
of these classes for coherent sheaves and tangent bundles, and the proof that the resulting
formulas agree with `NumericalVarietyData.chComp` and `toddComp`, belong to the future
geometric-to-numerical realization layer.
-/

universe u

namespace AlgebraicGeometry.Numerical

/-- Rank and Chern-class components in a commutative coefficient ring.

No dimension is stored here: a `NumericalRingData n A` determines which components vanish after
these universal formulas have been evaluated. -/
structure ChernClassData (A : Type u) where
  /-- The virtual rank. -/
  rank : ℤ
  /-- The Chern classes, with positive indices carrying the mathematical content. -/
  c : ℕ → A

namespace ChernClassData

variable {A : Type u} [CommRing A] [Algebra ℚ A]

/-- `ch₀ = rank`. -/
noncomputable def chernCharacterZero (C : ChernClassData A) : A :=
  algebraMap ℚ A (C.rank : ℚ)

/-- `ch₁ = c₁`. -/
def chernCharacterOne (C : ChernClassData A) : A :=
  C.c 1

/-- `ch₂ = (c₁² - 2c₂) / 2`. -/
noncomputable def chernCharacterTwo (C : ChernClassData A) : A :=
  algebraMap ℚ A (1 / 2) * (C.c 1 ^ 2 - 2 * C.c 2)

/-- `ch₃ = (c₁³ - 3c₁c₂ + 3c₃) / 6`. -/
noncomputable def chernCharacterThree (C : ChernClassData A) : A :=
  algebraMap ℚ A (1 / 6) * (C.c 1 ^ 3 - 3 * C.c 1 * C.c 2 + 3 * C.c 3)

/-- `ch₄ = (c₁⁴ - 4c₁²c₂ + 2c₂² + 4c₁c₃ - 4c₄) / 24`. -/
noncomputable def chernCharacterFour (C : ChernClassData A) : A :=
  algebraMap ℚ A (1 / 24) *
    (C.c 1 ^ 4 - 4 * C.c 1 ^ 2 * C.c 2 + 2 * C.c 2 ^ 2
      + 4 * C.c 1 * C.c 3 - 4 * C.c 4)

/-- The Chern-character component selected from the universal formulas through codimension
four. Components above four are zero because this is the bounded realization API currently
supported by DerivedAlgGeo; `Variety.NumericalHypotheses` records the corresponding hypothesis `n ≤ 4`. -/
noncomputable def chernCharacterComponent (C : ChernClassData A) : ℕ → A
  | 0 => chernCharacterZero C
  | 1 => chernCharacterOne C
  | 2 => chernCharacterTwo C
  | 3 => chernCharacterThree C
  | 4 => chernCharacterFour C
  | _ => 0

@[simp] theorem chernCharacterComponent_zero (C : ChernClassData A) :
    chernCharacterComponent C 0 = algebraMap ℚ A (C.rank : ℚ) := rfl

@[simp] theorem chernCharacterComponent_one (C : ChernClassData A) :
    chernCharacterComponent C 1 = C.c 1 := rfl

@[simp] theorem chernCharacterComponent_two (C : ChernClassData A) :
    chernCharacterComponent C 2 = chernCharacterTwo C := rfl

@[simp] theorem chernCharacterComponent_three (C : ChernClassData A) :
    chernCharacterComponent C 3 = chernCharacterThree C := rfl

@[simp] theorem chernCharacterComponent_four (C : ChernClassData A) :
    chernCharacterComponent C 4 = chernCharacterFour C := rfl

/-- `td₀ = 1`. -/
def toddZero : A := 1

/-- `td₁ = c₁ / 2`. -/
noncomputable def toddOne (T : ChernClassData A) : A :=
  algebraMap ℚ A (1 / 2) * T.c 1

/-- `td₂ = (c₁² + c₂) / 12`. -/
noncomputable def toddTwo (T : ChernClassData A) : A :=
  algebraMap ℚ A (1 / 12) * (T.c 1 ^ 2 + T.c 2)

/-- `td₃ = c₁c₂ / 24`. -/
noncomputable def toddThree (T : ChernClassData A) : A :=
  algebraMap ℚ A (1 / 24) * (T.c 1 * T.c 2)

/-- `td₄ = (-c₁⁴ + 4c₁²c₂ + 3c₂² + c₁c₃ - c₄) / 720`. -/
noncomputable def toddFour (T : ChernClassData A) : A :=
  algebraMap ℚ A (1 / 720) *
    (-T.c 1 ^ 4 + 4 * T.c 1 ^ 2 * T.c 2 + 3 * T.c 2 ^ 2
      + T.c 1 * T.c 3 - T.c 4)

/-- The Todd component selected from the universal formulas through codimension four. -/
noncomputable def toddComponent (T : ChernClassData A) : ℕ → A
  | 0 => toddZero
  | 1 => toddOne T
  | 2 => toddTwo T
  | 3 => toddThree T
  | 4 => toddFour T
  | _ => 0

@[simp] theorem toddComponent_zero (T : ChernClassData A) : toddComponent T 0 = 1 := rfl

@[simp] theorem toddComponent_one (T : ChernClassData A) : toddComponent T 1 = toddOne T := rfl

@[simp] theorem toddComponent_two (T : ChernClassData A) : toddComponent T 2 = toddTwo T := rfl

@[simp] theorem toddComponent_three (T : ChernClassData A) :
    toddComponent T 3 = toddThree T := rfl

@[simp] theorem toddComponent_four (T : ChernClassData A) : toddComponent T 4 = toddFour T := rfl

end ChernClassData

end AlgebraicGeometry.Numerical
