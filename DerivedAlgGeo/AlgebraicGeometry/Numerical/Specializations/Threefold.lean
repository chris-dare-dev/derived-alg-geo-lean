/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.General

/-!
# Display formulas for numerical threefolds

The `n = 3` specialisation of `AlgebraicGeometry.Numerical.NumericalVarietyData.chi_eq_sum`,
written exactly the way
`DerivedAlgGeo/AlgebraicGeometry/Numerical/Specializations/Surface.lean` writes the `n = 2` case:
expand
`Finset.range 4` and simplify `3 - i`. There is no threefold-specific *mathematics* here.
That the two files differ only in how many times `Finset.sum_range_succ` fires is the
content of the claim that Layer A is dimension-general.

## Main results

* `Threefold.chi_eq` — `χ(E) = r·∫td₃(X) + ∫c₁(E)·td₂(X) + ∫ch₂(E)·td₁(X) + ∫ch₃(E)`.
* `CalabiYauThreefold.IsCalabiYau` — the numerical signature of a Calabi–Yau threefold.
* `CalabiYauThreefold.chi_eq` — `χ(E) = ∫c₁(E)·td₂(X) + ∫ch₃(E)` on such a threefold.

Writing `td₂(X) = (K_X² + c₂(X))/12`, which on a Calabi–Yau threefold is `c₂(X)/12`, turns
`CalabiYauThreefold.chi_eq` into the classical `χ(E) = ∫ch₃(E) + (1/12)∫c₁(E)·c₂(X)`. That
substitution needs `K_X` and `c₂`, which are Layer B objects, so it is not asserted here.

## Models

`Numerical/Examples/Threefold/` carries two: `ℙ³`, whose Todd class has no vanishing
component and so exercises every term of `chi_eq`, and the quintic hypersurface in `ℙ⁴`,
which discharges `CalabiYauThreefold.IsCalabiYau`. Both are built from the dimension-general
ring `ℚ[t]/(t⁴)` of `Numerical/Models/MonogenicRing.lean`.
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace Threefold

open NumericalRingData NumericalVarietyData Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 3 A N)

/-- `χ(O_X)` for a threefold, read off the top Todd component: taking `E` of rank one with
vanishing higher Chern components in `chi_eq` leaves exactly `∫_X td₃(X)`. -/
noncomputable abbrev chiStructureSheaf : ℚ := V.structureSheafEulerCharacteristic

/-- **Riemann–Roch for threefolds.**

`χ(E) = rank(E) · ∫_X td₃(X) + ∫_X c₁(E)·td₂(X) + ∫_X ch₂(E)·td₁(X) + ∫_X ch₃(E)`. -/
theorem chi_eq (hV : V.SatisfiesHRR) (E : N) :
    (V.chi E : ℚ)
      = (V.rank E : ℚ) * V.ring.degree (V.toddComp 3)
        + V.ring.degree (V.chComp E 1 * V.toddComp 2)
        + V.ring.degree (V.chComp E 2 * V.toddComp 1)
        + V.ring.degree (V.chComp E 3) := by
  have h := V.chi_eq_sum hV E
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  simp only [show (3 : ℕ) - 0 = 3 from rfl, show (3 : ℕ) - 1 = 2 from rfl,
    show (3 : ℕ) - 2 = 1 from rfl, show (3 : ℕ) - 3 = 0 from rfl] at h
  rw [h, V.chComp_zero, V.ring.degree_algebraMap_mul, V.toddComp_zero, mul_one]

end Threefold

namespace CalabiYauThreefold

open NumericalRingData NumericalVarietyData

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 3 A N)

/-- The numerical signature of a **Calabi–Yau threefold**: trivial canonical class and
`χ(O_X) = 0`.

As with `K3.IsK3`, this asserts only two facts about the Todd class, so everything below is
a consequence of *those two facts* and not of anything else one knows about Calabi–Yau
threefolds. `∫_X td₃(X) = 0` is `χ(O_X) = 1 - 0 + 0 - 1 = 0`, which is what `h¹ = h² = 0`
and `K_X = 0` give. -/
structure IsCalabiYau : Prop where
  /-- `td₁(X) = −K_X/2 = 0`. -/
  toddComp_one : V.toddComp 1 = 0
  /-- `∫_X td₃(X) = χ(O_X) = 0`. -/
  degree_toddComp_three : V.ring.degree (V.toddComp 3) = 0

/-- **Riemann–Roch on a Calabi–Yau threefold**: `χ(E) = ∫_X c₁(E)·td₂(X) + ∫_X ch₃(E)`.

Two of the four terms of `Threefold.chi_eq` vanish, and they vanish for different reasons:
the rank term because `∫td₃ = 0`, the `ch₂` term because `td₁ = 0`. Note that the `ch₂`
term goes as well as the rank term — `td₁ = 0` kills it, so the collapsed formula has two
terms, not three. -/
theorem chi_eq (hHRR : V.SatisfiesHRR) (hCY : IsCalabiYau V) (E : N) :
    (V.chi E : ℚ)
      = V.ring.degree (V.chComp E 1 * V.toddComp 2)
        + V.ring.degree (V.chComp E 3) := by
  rw [Threefold.chi_eq V hHRR E, hCY.toddComp_one, hCY.degree_toddComp_three]
  simp only [mul_zero, map_zero]
  ring

/-- On a Calabi–Yau threefold `χ` does not see the rank: two objects with the same `c₁` and
the same `ch₃` have the same Euler characteristic however their ranks differ.

This is the concrete reason the Bridgeland-stability side wants the Calabi–Yau case
separately — the central charge cannot be normalised against `χ` alone. -/
theorem chi_eq_of_chComp_eq (E F : N)
    (hHRR : V.SatisfiesHRR) (hCY : IsCalabiYau V)
    (h₁ : V.chComp E 1 = V.chComp F 1)
    (h₃ : V.chComp E 3 = V.chComp F 3) :
    (V.chi E : ℚ) = (V.chi F : ℚ) := by
  rw [chi_eq V hHRR hCY E, chi_eq V hHRR hCY F, h₁, h₃]

end CalabiYauThreefold

end AlgebraicGeometry.Numerical
