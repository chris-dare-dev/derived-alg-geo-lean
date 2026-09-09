/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Slice
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.CentralCharge

/-!
# The Mukai charge, as a second child rather than an overload

`Charge.lean` builds the divisorial central charge out of a `ChernCharacter`
whose third coordinate is the ordinary `ch₂`.  Bridgeland's K3 construction
(arXiv:math/0307164, §6) instead pairs `exp(B + iω)` with the **Mukai vector**

```text
v(E) = ch(E) √td_X,   v(E) = (r, c₁, s) with s = ch₂ + r on a K3,
```

whose third coordinate is `ch₂ + rank`, not `ch₂`.  Writing that vector into a
`ChernCharacter` would put a Todd-corrected number into a field whose contract
says it holds the ordinary Chern character, so this file gives the Mukai
presentation its own name and relates the two by a proved comparison.

## What `√td_X` contributes, and why two numbers suffice

On a surface only two components of `√td_X` can reach the charge: the
codimension-one class `√td₁` and the number `∫√td₂`.  `SqrtTodd` carries exactly
those two, so the Mukai vector is

```text
v(E) = (r, c₁ + r √td₁, ch₂ + √td₁ · c₁ + r ∫√td₂).
```

`SqrtTodd.trivial` is `(0, 0)` and `SqrtTodd.k3` is `(0, 1)`, the latter being
the formal content of `√td = 1 + [pt]` on a K3.  The two presentations are then
two values of one parameter rather than two constructions:
`mukaiCharge_trivial` says the ordinary divisorial charge is the Mukai charge at
`SqrtTodd.trivial`, and `mukaiCharge_k3` says the K3 Mukai charge is the
ordinary charge minus the rank.

## The charge is the existing exponential charge

`LinearAlgebra/Lattice/Mukai/CentralCharge.lean` already owns
`Mukai.expChargeHom`, the additive `Z(β,ω)` on a real Mukai extension.  Nothing
is rebuilt here: `mukaiCharge` is that homomorphism composed with the Mukai
class map, and `centralCharge_eq_expChargeHom` records that the ordinary
divisorial charge is the same homomorphism composed with the ordinary triple.
So the divisorial layer and the Mukai lattice layer share one charge formula.

## Walls are not preserved

The Mukai and ordinary charges differ by a term that is real-linear in the
class but is **not** a scalar multiple of the charge, so `wall_smul` does not
apply and the two families have different walls in general.  That is the point
of keeping them apart, and `mukaiCharge_k3` makes the difference explicit.

Nothing here is a stability condition, a heart, or a K3 surface; `SqrtTodd` is
supplied data, and no theorem below claims it comes from a geometric `√td`.
-/

open QuadraticMap

universe v w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

variable {N : Type v} {D : Type w}
variable [AddCommGroup N] [AddCommGroup D] [Module ℝ D]

/-- The part of `√td_X` a surface Mukai vector can see: its codimension-one
class and its integrated codimension-two number.

This is supplied data.  Nothing in this file asserts that it is the square root
of a Todd class; the geometric constructor lives with the numerical adapters. -/
structure SqrtTodd (D : Type w) [AddCommGroup D] [Module ℝ D] where
  /-- The codimension-one component `√td₁`. -/
  divisor : D
  /-- The integrated codimension-two component `∫√td₂`. -/
  number : ℝ

namespace SqrtTodd

/-- The trivial square root, at which the Mukai vector is the ordinary
Chern-character triple. -/
def trivial : SqrtTodd D := ⟨0, 0⟩

/-- The K3 square root `√td = 1 + [pt]`: no codimension-one part, and
`∫√td₂ = 1`. -/
def k3 : SqrtTodd D := ⟨0, 1⟩

@[simp] theorem trivial_divisor : (trivial : SqrtTodd D).divisor = 0 := rfl

@[simp] theorem trivial_number : (trivial : SqrtTodd D).number = 0 := rfl

@[simp] theorem k3_divisor : (k3 : SqrtTodd D).divisor = 0 := rfl

@[simp] theorem k3_number : (k3 : SqrtTodd D).number = 1 := rfl

end SqrtTodd

namespace ChernCharacter

variable (ch : ChernCharacter N D) (S : DivisorSpace D)

/-- **The Mukai vector** `v(E) = ch(E) √td_X`, as an additive map into the real
Mukai extension of the divisor space.

Its third coordinate is deliberately not `ch₂`: it is `ch₂ + √td₁·c₁ + r∫√td₂`,
which on a K3 is `ch₂ + r`. -/
def mukaiVector (t : SqrtTodd D) : N →+ Mukai.RealExtension D where
  toFun E :=
    (ch.rank E, ch.chOne E + ch.rank E • t.divisor,
      ch.chTwo E + S.pair t.divisor (ch.chOne E) + ch.rank E * t.number)
  map_zero' := by
    simp only [map_zero, zero_smul, add_zero, DivisorSpace.pair, zero_mul]
    simp
  map_add' E F := by
    simp only [map_add, DivisorSpace.pair, Prod.mk_add_mk, add_smul, Prod.mk.injEq]
    exact ⟨trivial, by abel, by ring⟩

@[simp]
theorem mukaiVector_apply (t : SqrtTodd D) (E : N) :
    ch.mukaiVector S t E =
      (ch.rank E, ch.chOne E + ch.rank E • t.divisor,
        ch.chTwo E + S.pair t.divisor (ch.chOne E) + ch.rank E * t.number) := rfl

/-- At the trivial square root the Mukai vector is the ordinary
Chern-character triple.

Not a `simp` lemma: with `pair_zero_left` the left-hand side already reduces to
the right-hand side, so `simp` proves it and the normal-form linter rejects the
attribute.  It is stated because it is the identification that makes the
ordinary charge a value of the Mukai parameter. -/
theorem mukaiVector_trivial (E : N) :
    ch.mukaiVector S SqrtTodd.trivial E = ch.toRealExtension E := by
  simp [SqrtTodd.trivial, DivisorSpace.pair]

/-- On a K3 square root the Mukai vector is `(r, c₁, ch₂ + r)`, which is
Bridgeland's `v(E) = (r, c₁, s)` with `s = ch₂ + rank`.

Not a `simp` lemma, for the reason given at `mukaiVector_trivial`. -/
theorem mukaiVector_k3 (E : N) :
    ch.mukaiVector S SqrtTodd.k3 E =
      (ch.rank E, ch.chOne E, ch.chTwo E + ch.rank E) := by
  simp [SqrtTodd.k3, DivisorSpace.pair]

/-- **The ordinary divisorial charge is the exponential charge of the Mukai
lattice layer**, composed with the ordinary triple.

This is `centralCharge_eq_realPairing` restated against the additive
homomorphism `Mukai.expChargeHom`, and it is what lets the two layers share one
charge formula. -/
theorem centralCharge_eq_expChargeHom (P : StabilityParameters D) (E : N) :
    ch.centralCharge S P E =
      Mukai.expChargeHom S.intersection P.B P.omega (ch.toRealExtension E) := by
  have hb : ∀ x y : D, S.intersection x y = S.intersection y x := fun x y => S.pair_comm x y
  rw [Mukai.expChargeHom_apply, toRealExtension_apply,
    Mukai.expCharge_apply _ _ _ hb, centralCharge_apply]
  simp only [DivisorSpace.pair]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, zero_add, add_zero, sub_zero]
  · ring
  · linear_combination (ch.rank E) * hb P.B P.omega

/-- **The Mukai central charge**: Bridgeland's `Z(E) = (exp(B + iω), v(E))`.

It is the same `Mukai.expChargeHom` the ordinary charge uses, composed with the
Mukai class map instead of the ordinary triple. -/
def mukaiCharge (t : SqrtTodd D) (P : StabilityParameters D) : N →+ ℂ :=
  (Mukai.expChargeHom S.intersection P.B P.omega).comp (ch.mukaiVector S t)

@[simp]
theorem mukaiCharge_apply (t : SqrtTodd D) (P : StabilityParameters D) (E : N) :
    ch.mukaiCharge S t P E =
      Mukai.expCharge S.intersection P.B P.omega (ch.mukaiVector S t E) := rfl

/-- At the trivial square root the Mukai charge **is** the ordinary divisorial
charge.  The two presentations are two values of one parameter. -/
theorem mukaiCharge_trivial (P : StabilityParameters D) (E : N) :
    ch.mukaiCharge S SqrtTodd.trivial P E = ch.centralCharge S P E := by
  rw [mukaiCharge_apply, mukaiVector_trivial, ch.centralCharge_eq_expChargeHom S P E,
    Mukai.expChargeHom_apply]

/-- **The exact comparison.**  The Mukai charge exceeds the ordinary divisorial
charge by a term linear in the class and determined by `√td_X`. -/
theorem mukaiCharge_eq_centralCharge_add (t : SqrtTodd D) (P : StabilityParameters D)
    (E : N) :
    ch.mukaiCharge S t P E =
      ch.centralCharge S P E
        + Complex.ofReal (ch.rank E * S.pair P.B t.divisor
            - S.pair t.divisor (ch.chOne E) - ch.rank E * t.number)
        + Complex.I * Complex.ofReal (ch.rank E * S.pair P.omega t.divisor) := by
  have hb : ∀ x y : D, S.intersection x y = S.intersection y x := fun x y => S.pair_comm x y
  rw [mukaiCharge_apply, mukaiVector_apply, Mukai.expCharge_apply _ _ _ hb,
    centralCharge_apply]
  simp only [DivisorSpace.pair, map_add, map_smul, smul_eq_mul]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, mul_zero, zero_add, add_zero, sub_zero]
  · ring
  · linear_combination (ch.rank E) * hb P.omega P.B

/-- **On a K3 the Mukai charge is the ordinary charge minus the rank.**

This is the whole numerical difference between Bridgeland's presentation and
the Arcara--Bertram / Macrì--Schmidt one on a K3, and it is why the two have
different walls: the shift is not a scalar multiple of the charge. -/
theorem mukaiCharge_k3 (P : StabilityParameters D) (E : N) :
    ch.mukaiCharge S SqrtTodd.k3 P E =
      ch.centralCharge S P E - Complex.ofReal (ch.rank E) := by
  rw [mukaiCharge_eq_centralCharge_add]
  simp only [SqrtTodd.k3_divisor, SqrtTodd.k3_number, DivisorSpace.pair, map_zero,
    LinearMap.zero_apply, mul_zero, mul_one, zero_sub, sub_zero]
  push_cast
  ring

/-- The Mukai charge as a child of the universal wall root, indexed by the same
independent `(B, omega)` parameters as `fullChargeFamily`. -/
def mukaiChargeFamily (t : SqrtTodd D) :
    Wall.ChargeFamily (StabilityParameters D) N where
  charge P := ch.mukaiCharge S t P

@[simp]
theorem mukaiChargeFamily_charge (t : SqrtTodd D) (P : StabilityParameters D) (E : N) :
    (ch.mukaiChargeFamily S t).charge P E = ch.mukaiCharge S t P E := rfl

/-- At the trivial square root the Mukai wall family is the divisorial one. -/
theorem mukaiChargeFamily_trivial :
    ch.mukaiChargeFamily S SqrtTodd.trivial = ch.fullChargeFamily S := by
  ext P E
  rw [mukaiChargeFamily_charge, fullChargeFamily_charge, mukaiCharge_trivial]

end ChernCharacter

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
