/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Algebra.Hom
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.General

/-!
# The dual involution on a numerical intersection ring

`(-)^∨` acts on the codimension-`i` part of `A^•(X)_ℚ` by `(-1)^i`. It is what turns
Hirzebruch–Riemann–Roch into its bilinear form `χ(E,F) = ∫_X ch(E)^∨ · ch(F) · td(X)`, and
so it is the last piece of Layer A that Bridgeland stability needs: the central charge
factors through `N(X)` modulo the radical of that pairing.

## Why a separate data bundle

`NumericalRingDualHypotheses R` is an explicit extension of one selected presentation
`R : NumericalRingData n A`, not a field of every numerical ring and not an independent
bundle with another path back to `R`.
A ring that has no chosen dual needs no placeholder, while two choices can coexist without
instance search selecting between them.

## Main definitions

* `NumericalRingDualHypotheses R` — the involution, as data plus the axiom that it acts by
  `(-1)^i` on `piece i`.
* `chDual E` — `ch(E)^∨`, written directly as `Σᵢ (-1)ⁱ chᵢ(E)` rather than as `dual (ch E)`.

## Main results

* `dual_ch` — the two descriptions of `ch(E)^∨` agree.
* `dual_involutive_of_mem_piece` — `(-)^∨` is an involution on each graded piece.

## Deliberately not stated

`dual (dual x) = x` for *arbitrary* `x`, and `degree (dual x) = (-1)^n · degree x`. Both are
true, and both need the graded decomposition of `x` — `NumericalRingData.isInternal` — rather
than just membership in a single piece. Nothing downstream needs them: every consumer here
reaches `dual` through `chComp` and `toddComp`, which are graded by construction, so the
component-wise lemmas suffice. Adding the general versions means importing
`DirectSum.IsInternal` machinery for no current gain.
-/

universe u v

namespace AlgebraicGeometry.Numerical

open NumericalRingData Finset

/-- The **dual involution** on a numerical intersection ring: a `ℚ`-algebra endomorphism
acting on codimension `i` by `(-1)^i`.

Geometrically this is `E ↦ E^∨` read through the Chern character: `chᵢ(E^∨) = (-1)ⁱchᵢ(E)`.
It is carried as data because `NumericalRingData` does not expose the graded projections, so
there is nothing to define it *from* at this layer. -/
structure NumericalRingDualHypotheses {n : ℕ} {A : Type u} [CommRing A] [Algebra ℚ A]
    (R : NumericalRingData n A) where
  /-- The involution, as a `ℚ`-algebra map. -/
  dual : A →ₐ[ℚ] A
  /-- It acts on codimension `i` by `(-1)^i`. -/
  dual_of_mem_piece : ∀ {i : ℕ} {x : A}, x ∈ R.piece i → dual x = (-1 : ℚ) ^ i • x

namespace NumericalRingDualHypotheses

variable {n : ℕ} {A : Type u} [CommRing A] [Algebra ℚ A]
variable {R : NumericalRingData n A} (D : NumericalRingDualHypotheses R)

/-- `(-)^∨` preserves each graded piece: it only rescales it. -/
theorem dual_mem_piece {i : ℕ} {x : A} (hx : x ∈ R.piece i) :
    D.dual x ∈ R.piece i := by
  rw [D.dual_of_mem_piece hx]
  exact Submodule.smul_mem _ _ hx

/-- `(-)^∨` is an involution on each graded piece. -/
theorem dual_involutive_of_mem_piece {i : ℕ} {x : A} (hx : x ∈ R.piece i) :
    D.dual (D.dual x) = x := by
  rw [D.dual_of_mem_piece hx, map_smul, D.dual_of_mem_piece hx, smul_smul, ← pow_add]
  rw [Even.neg_one_pow ⟨i, rfl⟩, one_smul]

/-- Scalars are fixed by `(-)^∨`, since they sit in codimension zero. -/
theorem dual_algebraMap (q : ℚ) : D.dual (algebraMap ℚ A q) = algebraMap ℚ A q := by
  rw [D.dual_of_mem_piece (R.algebraMap_mem_piece_zero q), pow_zero, one_smul]

end NumericalRingDualHypotheses

namespace NumericalVarietyData

open NumericalRingDualHypotheses

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData n A N)

/-- The Chern character is additive, componentwise additivity summed up.

Stated before the dual is in scope because it has nothing to do with it. -/
theorem ch_add (E F : N) : V.ch (E + F) = V.ch E + V.ch F := by
  simp only [ch, V.chComp_add]
  exact Finset.sum_add_distrib

/-- The **dual Chern character** `ch(E)^∨ = Σᵢ (-1)ⁱ chᵢ(E)`.

Defined from the grading alone, with no `NumericalRingDualHypotheses` argument in sight: the
alternating sum is available on any `NumericalVarietyData`, and `dual_ch` below is what says it
deserves the name. Everything the Euler pairing needs lives at this level of generality. -/
noncomputable def chDual (E : N) : A :=
  ∑ i ∈ range (n + 1), (-1 : ℚ) ^ i • V.chComp E i

/-- `ch(-)^∨` is additive, componentwise again. -/
theorem chDual_add (E F : N) :
    V.chDual (E + F) = V.chDual E + V.chDual F := by
  simp only [chDual, V.chComp_add, smul_add]
  exact Finset.sum_add_distrib

variable (D : NumericalRingDualHypotheses V.ring)

/-- `chᵢ(E^∨) = (-1)ⁱ chᵢ(E)`. -/
theorem dual_chComp (E : N) (i : ℕ) :
    D.dual (V.chComp E i) = (-1 : ℚ) ^ i • V.chComp E i :=
  D.dual_of_mem_piece (V.chComp_mem E i)

/-- `tdᵢ(X)^∨ = (-1)ⁱ tdᵢ(X)`. -/
theorem dual_toddComp (i : ℕ) :
    D.dual (V.toddComp i) = (-1 : ℚ) ^ i • V.toddComp i :=
  D.dual_of_mem_piece (V.toddComp_mem i)

/-- `ch(E)^∨` really is `ch(E)` pushed through the involution. -/
theorem dual_ch (E : N) : D.dual (V.ch E) = V.chDual E := by
  simp only [ch, chDual, map_sum]
  exact Finset.sum_congr rfl fun i _ => V.dual_chComp D E i

end NumericalVarietyData

end AlgebraicGeometry.Numerical
