/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Discriminant

/-!
# Display formulas for numerical surfaces

The `n = 2` specialisation of `AlgebraicGeometry.Numerical.NumericalVarietyData.chi_eq_sum`.

This is an optional display specialization of the dimension-general API. It contains no
foundational surface object: `NumericalVarietyData 2 A N` is the general variety interface at
dimension two, and the discriminant itself lives in
`Numerical/GrothendieckGroup/Discriminant.lean` for
arbitrary dimension.

## Main definitions

* `AlgebraicGeometry.Numerical.Surface.chiStructureSheaf` — `χ(O_X)`, read off the top Todd
  component.
* `AlgebraicGeometry.Numerical.Surface.discriminant` — the Bogomolov–Gieseker discriminant, as
  a compatibility alias for the dimension-general one.

## Main results

* `chi_eq` — `χ(E) = r·∫td₂(X) + ∫c₁(E)·td₁(X) + ∫ch₂(E)`.
* compatibility aliases for the dimension-general numerical discriminant.

## Implementation notes

Writing `td₁(X) = −K_X/2` and `ch₂(E) = (c₁² − 2c₂)/2` turns `chi_eq` into the classical
`χ(E) = r·χ(O_X) + ½c₁(c₁ − K_X) − c₂`. Those substitutions need `K_X` and `c₂`, which are
Layer B objects, so they are *not* asserted here.

## References

The general statement is `AlgebraicGeometry.Numerical.NumericalVarietyData.chi_eq_sum`, and the
discriminant is `NumericalVarietyData.discriminant`.

## Tags

Riemann–Roch, surface, discriminant, Todd class, numerical variety
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace Surface

open NumericalRingData NumericalVarietyData Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 2 A N)

/-- `χ(O_X)` for a surface, read off the top Todd component: taking `E` of rank one with
vanishing higher Chern components in `chi_eq` leaves exactly `∫_X td₂(X)`. -/
noncomputable abbrev chiStructureSheaf : ℚ :=
  V.structureSheafEulerCharacteristic

/-- **Riemann–Roch for surfaces.**

`χ(E) = rank(E) · ∫_X td₂(X) + ∫_X c₁(E)·td₁(X) + ∫_X ch₂(E)`. -/
theorem chi_eq (hV : V.SatisfiesHRR) (E : N) :
    (V.chi E : ℚ)
      = (V.rank E : ℚ) * V.ring.degree (V.toddComp 2)
        + V.ring.degree (V.chComp E 1 * V.toddComp 1)
        + V.ring.degree (V.chComp E 2) := by
  have h := V.chi_eq_sum hV E
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at h
  simp only [show (2 : ℕ) - 0 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
    show (2 : ℕ) - 2 = 0 from rfl] at h
  rw [h, V.chComp_zero, V.ring.degree_algebraMap_mul, V.toddComp_zero, mul_one]

/-- The **Bogomolov–Gieseker discriminant** `Δ(E) = c₁(E)² − 2·rank(E)·ch₂(E)`, a class in
codimension two.

Equivalently `Δ(E) = 2·r·c₂(E) − (r − 1)·c₁(E)²` once `c₂` is available; the `ch`-form is
used here because `c₂` is a Layer B object. Bogomolov's inequality — `∫_X Δ(E) ≥ 0` for
`E` slope-semistable with respect to a polarisation — is *not* stated at this layer: there
is no stability notion in `NumericalVarietyData`, and asserting it here would hide a real
theorem behind a class field. -/
noncomputable abbrev discriminant (E : N) : A := V.discriminant E

/-- The discriminant lives in codimension two. -/
theorem discriminant_mem_piece_two (E : N) :
    V.discriminant E ∈ V.ring.piece 2 := by
  exact V.discriminant_mem_piece_two E

/-- `∫_X Δ(E) = ∫_X c₁(E)² − 2·rank(E)·∫_X ch₂(E)`: the scalar the
Bogomolov–Gieseker inequality is about. -/
theorem degree_discriminant (E : N) :
    V.ring.degree (V.discriminant E)
      = V.ring.degree (V.chComp E 1 * V.chComp E 1)
        - 2 * (V.rank E : ℚ) * V.ring.degree (V.chComp E 2) := by
  exact V.degree_discriminant E

end Surface

end AlgebraicGeometry.Numerical
