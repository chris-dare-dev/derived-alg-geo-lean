/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.BlowUpPlaneWalls
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Circle

/-!
# A nontrivial orthogonal slice, and the first `IsGeometric` witness

`Walls/Divisorial/Slice.lean` builds the basis-free orthogonal slice and attaches
two certificates to it: `IsHodge`, which asks the distinguished direction to have
positive square and every nonzero transverse direction negative square, and
`IsGeometric`, which adds that the direction is ample.

Before this file the tree had two slices and one and a half certificates.

* The rank-one slice has transverse space `Fin 0 → ℝ`, so it is the classical
  `(s, t)` plane and `rankOne_isHodge` is vacuous in its second clause.
* `SmoothQuadricCharge.wallSlice` has a one-dimensional transverse space but no
  certificate.
* **`IsGeometric` had no witness at all.**  Not for want of an ample cone:
  `SmoothQuadricCharge.ampleCone` is one, and carries a `DivisorialParameters`
  over it.  What was missing was anyone proving the certificate *for a slice*.
  The blow-up had no cone either way, recording ampleness only as
  `IsAmpleCoefficients`, a predicate on rational coefficients that nothing
  consumes.

This file supplies a slice whose transverse space is a genuine **plane**, both
certificates for it, and the ample cone the second needs.

## The slice

The anticanonical class `-K = 3H - E₁ - E₂` has square `7`, and its orthogonal
complement in the rank-three space is two-dimensional:

```text
x ⊥ -K  ↔  3x₀ + x₁ + x₂ = 0,
```

spanned by `E₁ - E₂` and `H - E₁ - 2E₂`.  `transverse` is that parameterization.
`IsHodge` is then immediate from `hodgeDefinite`, which this model proves rather
than assumes, and injectivity of `transverse` is what turns `u ≠ 0` into
`transverse u ≠ 0`.

## The ample cone

`ampleCone` is the real cone `aH + bE₁ + cE₂` with `b < 0`, `c < 0` and
`-b - c < a`, which is `IsAmpleCoefficients` written for the realized
coordinates; `mem_ampleCone_of_isAmpleCoefficients` is the bridge, so the file
does not introduce a second unrelated notion of ampleness.

## What is not claimed

No scheme and no ample line bundle appear.  `ampleCone` is a subset of `ℝ³`
chosen to match the classical description of the ample cone of a two-point
blow-up; nothing here proves that it *is* that cone for a geometric surface, and
`IsGeometric` asks only that the direction lie in the supplied set.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical.Examples.BlowUpPlane

noncomputable section

/-! ### The ample cone, as a set of real divisors -/

/-- The ample cone of the two-point blow-up, in the realized coordinates
`aH + bE₁ + cE₂`: both exceptional coefficients negative, and the hyperplane
coefficient exceeding their sum in absolute value. -/
def ampleCone : Set Divisor :=
  {x | x.2.1 < 0 ∧ x.2.2 < 0 ∧ -x.2.1 - x.2.2 < x.1}

theorem mem_ampleCone_iff (x : Divisor) :
    x ∈ ampleCone ↔ x.2.1 < 0 ∧ x.2.2 < 0 ∧ -x.2.1 - x.2.2 < x.1 := Iff.rfl

/-- **The rational ample condition lands in the real cone.**  This is what keeps
`ampleCone` from being a second, unrelated notion of ampleness: it is
`IsAmpleCoefficients` read in the realized coordinates, where `aH - bE₁ - cE₂`
becomes `(a, -b, -c)`. -/
theorem mem_ampleCone_of_isAmpleCoefficients {a b c : ℚ}
    (h : IsAmpleCoefficients a b c) :
    (((a : ℚ) : ℝ), ((-b : ℚ) : ℝ), ((-c : ℚ) : ℝ)) ∈ ampleCone := by
  obtain ⟨hb, hc, hbc⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · show ((-b : ℚ) : ℝ) < 0
    have : (0 : ℝ) < ((b : ℚ) : ℝ) := by exact_mod_cast hb
    push_cast
    linarith
  · show ((-c : ℚ) : ℝ) < 0
    have : (0 : ℝ) < ((c : ℚ) : ℝ) := by exact_mod_cast hc
    push_cast
    linarith
  · show -((-b : ℚ) : ℝ) - ((-c : ℚ) : ℝ) < ((a : ℚ) : ℝ)
    have : ((b : ℚ) : ℝ) + ((c : ℚ) : ℝ) < ((a : ℚ) : ℝ) := by exact_mod_cast hbc
    push_cast
    linarith

/-- The realized anticanonical class is ample. -/
theorem antiCanonical_mem_ampleCone :
    numericalRealization.realizePolarization antiCanonicalPolarization ∈ ampleCone := by
  rw [antiCanonicalPolarization, numericalRealization_polarization]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ### The transverse plane -/

/-- The two-dimensional orthogonal complement of `-K`, spanned by `E₁ - E₂` and
`H - E₁ - 2E₂`. -/
def transverseMap : (ℝ × ℝ) →ₗ[ℝ] Divisor where
  toFun u := (u.2, u.1 - u.2, -u.1 - 2 * u.2)
  map_add' u v := by
    ext <;> simp <;> ring
  map_smul' a u := by
    ext <;> simp <;> ring

@[simp]
theorem transverseMap_apply (u : ℝ × ℝ) :
    transverseMap u = (u.2, u.1 - u.2, -u.1 - 2 * u.2) := rfl

/-- **Every transverse direction is orthogonal to `-K`.**  The defining equation
of the complement is `3x₀ + x₁ + x₂ = 0`. -/
theorem pair_antiCanonical_transverse (u : ℝ × ℝ) :
    divisorSpace.pair
      (numericalRealization.realizePolarization antiCanonicalPolarization)
      (transverseMap u) = 0 := by
  rw [antiCanonicalPolarization, numericalRealization_polarization]
  simp only [divisorSpace_pair, transverseMap_apply]
  push_cast
  ring

/-- The parameterization is injective, which is what turns `u ≠ 0` into
`transverse u ≠ 0`. -/
theorem transverseMap_injective : Function.Injective transverseMap := by
  intro u v h
  have h2 : u.2 = v.2 := congrArg Prod.fst h
  have h1 : u.1 - u.2 = v.1 - v.2 := congrArg (fun z => z.2.1) h
  refine Prod.ext ?_ h2
  rw [h2] at h1
  linarith

/-! ### The slice, and its two certificates -/

/-- **An orthogonal slice whose transverse space is a plane.**

The rank-one slice has transverse space `Fin 0 → ℝ` and the quadric's has a
line; this is the first with a two-dimensional one, which is what Picard rank
three buys. -/
def antiCanonicalSlice : OrthogonalSlice divisorSpace (ℝ × ℝ) where
  H := numericalRealization.realizePolarization antiCanonicalPolarization
  transverse := transverseMap
  orthogonal := pair_antiCanonical_transverse

@[simp]
theorem antiCanonicalSlice_H :
    antiCanonicalSlice.H
      = numericalRealization.realizePolarization antiCanonicalPolarization := rfl

/-- **The slice is Hodge**, and not vacuously: the second clause quantifies over
a plane of transverse directions, and is discharged by `hodgeDefinite`, which
this model proves. -/
theorem antiCanonicalSlice_isHodge : antiCanonicalSlice.IsHodge where
  H_square_pos := antiCanonical_sq_pos
  transverse_square_neg u hu := by
    refine (hodgeDefinite antiCanonical_sq_pos).neg_definite (transverseMap u)
      (pair_antiCanonical_transverse u) ?_
    intro hc
    exact hu (transverseMap_injective (by rw [hc, map_zero]))

/-- **The first `IsGeometric` witness in the repository.**

`IsGeometric` adds ampleness of the distinguished direction to the Hodge data.
Nothing inhabited it before.  `SmoothQuadricCharge.ampleCone` shows the missing
piece was not a cone but the certificate itself: no slice in the tree had one. -/
theorem antiCanonicalSlice_isGeometric : antiCanonicalSlice.IsGeometric ampleCone where
  __ := antiCanonicalSlice_isHodge
  H_ample := antiCanonical_mem_ampleCone

/-! ### The wall family of the slice -/

/-- The wall family of the two-point blow-up along the anticanonical slice,
indexed by `(s, u, t)` with `u` in a plane. -/
def sliceChargeFamily :
    Wall.ChargeFamily (OrthogonalSlice.Point (ℝ × ℝ)) NumericalClass :=
  antiCanonicalSlice.chargeFamily numericalRealization.chernCharacter

@[simp]
theorem sliceChargeFamily_charge (p : OrthogonalSlice.Point (ℝ × ℝ))
    (E : NumericalClass) :
    sliceChargeFamily.charge p E =
      numericalRealization.chernCharacter.centralCharge divisorSpace
        (antiCanonicalSlice.parameters p) E := rfl

/-- **The circle description of walls fires on this slice.**

For each fixed transverse parameter the wall of two classes in the `(s, t)`
half-plane is a circle or a line, by `wall_ofST_iff_circle`.  On the rank-one
slice that statement has one such half-plane; here it has a plane's worth. -/
theorem wall_ofST_iff_circle (uu : ℝ × ℝ) {p : ℝ × ℝ} (ht : p.2 ≠ 0)
    (v w : NumericalClass) :
    OrthogonalSlice.Point.ofST uu p ∈
        antiCanonicalSlice.wall numericalRealization.chernCharacter v w ↔
      Wall.minA
            ((antiCanonicalSlice.sliceCoordinates
              numericalRealization.chernCharacter uu).toNumClass v)
            ((antiCanonicalSlice.sliceCoordinates
              numericalRealization.chernCharacter uu).toNumClass w)
            * (p.1 ^ 2 + p.2 ^ 2)
          + 2 * Wall.minB
            ((antiCanonicalSlice.sliceCoordinates
              numericalRealization.chernCharacter uu).toNumClass v)
            ((antiCanonicalSlice.sliceCoordinates
              numericalRealization.chernCharacter uu).toNumClass w) * p.1
          + 2 * Wall.minC
            ((antiCanonicalSlice.sliceCoordinates
              numericalRealization.chernCharacter uu).toNumClass v)
            ((antiCanonicalSlice.sliceCoordinates
              numericalRealization.chernCharacter uu).toNumClass w) = 0 :=
  OrthogonalSlice.wall_ofST_iff_circle antiCanonicalSlice
    numericalRealization.chernCharacter uu ht v w

end

end AlgebraicGeometry.Numerical.Examples.BlowUpPlane
