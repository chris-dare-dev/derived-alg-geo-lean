/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Discriminant

/-!
# K3 surfaces, numerically

A K3 surface is a smooth projective surface with trivial canonical bundle and no first
cohomology. Numerically that is exactly two conditions on the Todd class:

* `td₁(X) = −K_X/2 = 0`;
* `∫_X td₂(X) = χ(O_X) = 2`.

`IsK3` asserts those two and nothing else, so every consequence below is a consequence of
*those two facts about the Todd class*, not of anything else one knows about K3 surfaces.

## Main results

* `chi_eq` — `χ(E) = 2·rank(E) + ∫_X ch₂(E)`.
* `mukaiSelfPairing_eq` — `⟨v(E), v(E)⟩ = ∫_X Δ(E) − 2·rank(E)²`, relating the Mukai
  self-pairing to the Bogomolov–Gieseker discriminant.

The second identity is what makes the Mukai lattice and the discriminant two views of one
object: `v² ≥ −2` (the condition for a moduli space to be nonempty) and `∫Δ ≥ 0`
(Bogomolov) differ by exactly `2r²`.

## Not proved here

That the axioms have a K3 *model*: a concrete `NumericalVarietyData 2 A N` with
`A = ℚ[t]/(t³)`, `∫t² = 2d`, satisfying `IsK3`. Only the dimension-zero witness in
`Numerical/Models/DimensionZero/Point.lean` exists so far, so the statements below are
conditional on a
`NumericalVarietyData 2 A N` existing at all. Building that model is the next task; it needs the
internality of the grading, i.e. linear independence of `1, t, t²`.
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace K3

open Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 2 A N)

/-- The numerical signature of a K3 surface: trivial canonical class and `χ(O_X) = 2`. -/
structure IsK3 : Prop where
  /-- `td₁(X) = −K_X/2 = 0`. -/
  toddComp_one : V.toddComp 1 = 0
  /-- `∫_X td₂(X) = χ(O_X) = 2`. -/
  degree_toddComp_two : V.ring.degree (V.toddComp 2) = 2

/-- **Riemann–Roch on a K3 surface**: `χ(E) = 2·rank(E) + ∫_X ch₂(E)`.

The `c₁`-term of the surface formula drops out because `td₁ = 0`; this is the whole of what
triviality of the canonical class buys. -/
theorem chi_eq (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    (V.chi E : ℚ) = 2 * (V.rank E : ℚ) + V.ring.degree (V.chComp E 2) := by
  have h := V.chi_eq_sum hHRR E
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at h
  simp only [show (2 : ℕ) - 0 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
    show (2 : ℕ) - 2 = 0 from rfl] at h
  rw [h, V.chComp_zero, V.ring.degree_algebraMap_mul, V.toddComp_zero, mul_one,
    hK3.toddComp_one, hK3.degree_toddComp_two, mul_zero, map_zero]
  ring

/-- The third component of the Mukai vector `v(E) = (r, c₁, s)`, integrated:
`s = rank(E) + ∫_X ch₂(E)`.

For a K3, `v(E) = ch(E)·√td(X)` with `√td(X) = 1 + [pt]`, so the top component of `v` is
`ch₂(E) + rank(E)·[pt]`; `mukaiS` is its degree. -/
noncomputable def mukaiS (E : N) : ℚ :=
  (V.rank E : ℚ) + V.ring.degree (V.chComp E 2)

/-- Riemann–Roch in Mukai coordinates: `χ(E) = r + s`. -/
theorem chi_eq_rank_add_mukaiS (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    (V.chi E : ℚ) = (V.rank E : ℚ) + mukaiS V E := by
  rw [chi_eq V hHRR hK3 E, mukaiS]
  ring

/-- The Mukai self-pairing `⟨v(E), v(E)⟩ = c₁² − 2rs`. -/
noncomputable def mukaiSelfPairing (E : N) : ℚ :=
  V.ring.degree (V.chComp E 1 * V.chComp E 1)
    - 2 * (V.rank E : ℚ) * mukaiS V E

/-- **The Mukai pairing and the Bogomolov–Gieseker discriminant differ by `2r²`**:

`⟨v(E), v(E)⟩ = ∫_X Δ(E) − 2·rank(E)²`.

So `v² ≥ −2` and `∫Δ ≥ 0` are statements about the same quantity, shifted.

`IsK3` is `omit`ted deliberately: this identity is arithmetic relating two definitions and
holds on *any* surface. Only the reading of `(r, c₁, s)` as a Mukai vector is K3-specific. -/
theorem mukaiSelfPairing_eq (E : N) :
    mukaiSelfPairing V E
      = V.ring.degree (V.discriminant E) - 2 * (V.rank E : ℚ) ^ 2 := by
  rw [mukaiSelfPairing, mukaiS, V.degree_discriminant]
  ring

/-- A rank-zero object has `⟨v, v⟩ = ∫_X c₁²`. Also independent of `IsK3`. -/
theorem mukaiSelfPairing_of_rank_eq_zero (E : N) (hE : V.rank E = 0) :
    mukaiSelfPairing V E = V.ring.degree (V.chComp E 1 * V.chComp E 1) := by
  rw [mukaiSelfPairing, hE]
  push_cast
  ring

end K3

end AlgebraicGeometry.Numerical
