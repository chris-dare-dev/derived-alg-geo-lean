/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Discriminant
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.K3

/-!
# A polarisation, the Mumford slope, and the two `H`-discriminants

The numerical layer has an intersection ring, a Chern character and a rank, but
no **polarisation**: nothing yet picks a class `H` in codimension one against
which degrees are taken. This file adds one, and the three quantities that need
it.

## Definitions only

Every statement here is a definition, a grading lemma, or an evaluation. **No
inequality is proved and none is assumed** — not Bogomolov–Gieseker, not Hodge
index, not `0 ≤ discrH`. Those are the next slice's, and `discrH`'s docstring
says so where a reader will look.

## The two discriminants must not be conflated

There are two different things called "the `H`-discriminant" and they are not
equal:

```
discDegH E = ∫ Δ(E) · H^(n-2)          -- what Bogomolov–Gieseker is about in dimension n
discrH   E = (∫ch₁(E)·H)² - 2(∫H²)·rk(E)·∫ch₂(E)   -- the surface tilt discriminant
```

`discrH` **weights the rank slot by `∫H²`**, because that is what the charge
formula of `Walls/Numerical/Basic.lean` requires of a class transported to the
`(s, t)` plane. The two agree only when `∫H² = 1`. Conflating them is the
mistake this section exists to prevent, and it is why `discrH` is defined only
at `n = 2`, under `Surface`, rather than in general.

## `ℕ`-subtraction in the exponents

`degH` twists by `H^(n-1)` and `discDegH` by `H^(n-2)`, both written with
`ℕ`-subtraction. At `n = 0` and `n < 2` respectively the exponent truncates to
`0` and the definition is junk. That is harmless and is the convention the rest
of the layer already lives with; the grading lemmas that need the exponent to
mean what it says carry `2 ≤ n` as an explicit hypothesis.

At `n = 2` the `discDegH` twist is `H^0 = 1`, which is why the surface
statements downstream carry no polarisation in their conclusions —
`Surface.discDegH_eq` records exactly that.

## Explicit data, never an instance

`Polarization` hangs off `NumericalRingData`, **not** off
`NumericalVarietyData`: a polarisation is a fact about the intersection ring and
says nothing about the Grothendieck group, and keeping it there lets one `H`
serve several presentations on the same carrier. It is a `structure`, it is
passed explicitly, and it is never selected by instance search — the idiom
`NumericalRingData` and `NumericalVarietyData` already follow.

`degree_pow_pos` is the only positivity assumed anywhere in this file. It is a
field, supplied by whoever builds the polarisation.

## Main results

* `Polarization` and `Polarization.pow_mem`.
* `degH`, `degH_add`, `degHHom` — the `H`-degree, additive in the class.
* `slopeH` — the Mumford slope, junk at rank zero.
* `discDegH`, `discDegH_mul_mem` and `Surface.discDegH_eq`.
* `Surface.discrH` — the tilt discriminant, and **not** `∫Δ(E)`.
* `Examples.k3Polarization` and `Examples.degH_k3` — a worked instance.
-/

universe u v

namespace AlgebraicGeometry.Numerical

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

/-! ### The polarisation -/

/-- **A polarisation of a numerical intersection ring**: a codimension-one class
whose top self-intersection is positive.

`degree_pow_pos` is supplied, not proved. It stands for `∫_X Hⁿ > 0`, which for
an actual ample class follows from Nakai–Moishezon; nothing here relates this
structure to Mathlib's `IsAmple`, and nothing here needs to. -/
structure Polarization (R : NumericalRingData n A) where
  /-- The polarising class `H`. -/
  cls : A
  /-- `H` lives in codimension one. -/
  cls_mem : cls ∈ R.piece 1
  /-- `∫_X Hⁿ > 0`. Supplied by the caller. -/
  degree_pow_pos : 0 < R.degree (cls ^ n)

namespace Polarization

variable {R : NumericalRingData n A}

/-- `Hⁱ` lives in codimension `i`. -/
theorem pow_mem (P : Polarization R) (i : ℕ) : P.cls ^ i ∈ R.piece i := by
  induction i with
  | zero => simpa using R.one_mem_piece_zero
  | succ i ih => simpa [pow_succ] using R.mul_mem_piece ih P.cls_mem

end Polarization

/-! ### The `H`-degree and the Mumford slope -/

variable (V : NumericalVarietyData n A N) (P : Polarization V.ring)

/-- **The `H`-degree** `deg_H(E) = ∫_X ch₁(E) · H^(n-1)`.

The exponent is `ℕ`-subtraction, so at `n = 0` it truncates to `0` and the
definition is junk — the same convention the rest of the numerical layer uses. -/
noncomputable def degH (E : N) : ℚ := V.ring.degree (V.chComp E 1 * P.cls ^ (n - 1))

/-- The `H`-degree is additive, because `ch₁` is. -/
theorem degH_add (E F : N) : degH V P (E + F) = degH V P E + degH V P F := by
  simp only [degH, V.chComp_add, add_mul, map_add]

/-- The `H`-degree, bundled as an additive homomorphism. -/
noncomputable def degHHom : N →+ ℚ := AddMonoidHom.mk' (degH V P) (degH_add V P)

@[simp]
theorem degHHom_apply (E : N) : degHHom V P E = degH V P E := rfl

/-- **The Mumford slope** `μ_H(E) = deg_H(E) / rk(E)`.

Junk at rank zero, exactly as `SlopeData.slope` in
`CategoryTheory/…/StabilityFunction/Slope.lean` is, so the two agree where they
meet. -/
noncomputable def slopeH (E : N) : ℚ := degH V P E / (V.rank E : ℚ)

theorem slopeH_eq (E : N) : slopeH V P E = degH V P E / (V.rank E : ℚ) := rfl

/-! ### The two discriminants -/

/-- **The `H`-twisted discriminant degree** `∫_X Δ(E) · H^(n-2)`.

This is the quantity the Bogomolov–Gieseker inequality is about in dimension
`n`. It is **not** `Surface.discrH`; see the module docstring. -/
noncomputable def discDegH (E : N) : ℚ :=
  V.ring.degree (V.discriminant E * P.cls ^ (n - 2))

/-- The integrand of `discDegH` sits in the top piece, which is what makes
`discDegH` the integral of a top-dimensional class rather than a truncation.
`2 ≤ n` is where the `ℕ`-subtraction in the exponent stops being junk. -/
theorem discDegH_mul_mem (hn : 2 ≤ n) (E : N) :
    V.discriminant E * P.cls ^ (n - 2) ∈ V.ring.piece n := by
  have h := V.ring.mul_mem_piece (V.discriminant_mem_piece_two E) (P.pow_mem (n - 2))
  rwa [Nat.add_sub_cancel' hn] at h

namespace Surface

variable (V : NumericalVarietyData 2 A N) (P : Polarization V.ring)

/-- At `n = 2` the twist is `H⁰ = 1`, so the polarisation drops out of
`discDegH` entirely. This is why the surface statements downstream carry no
polarisation in their conclusions. -/
theorem discDegH_eq (E : N) : discDegH V P E = V.ring.degree (V.discriminant E) := by
  simp [discDegH]

/-- **The surface tilt discriminant**
`discrH(E) = (∫ch₁(E)·H)² − 2·(∫H²)·rk(E)·∫ch₂(E)`.

**This is not `discDegH`, and it is not `∫Δ(E)`.** It weights the rank slot by
`∫H²`, because that is what the twisted-charge formula of
`Walls/Numerical/Basic.lean` requires of a class transported to the `(s, t)`
plane. The two agree only when `∫H² = 1`.

`0 ≤ discrH` is **not** proved here. It needs Bogomolov–Gieseker and the Hodge
index inequality, both of which are supplied data in the next slice. -/
noncomputable def discrH (E : N) : ℚ :=
  degH V P E ^ 2
    - 2 * V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) * V.ring.degree (V.chComp E 2)

theorem discrH_eq (E : N) :
    discrH V P E = degH V P E ^ 2
      - 2 * V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) * V.ring.degree (V.chComp E 2) := rfl

end Surface

/-! ### A worked instance on the rank-one K3 model -/

namespace Examples

open AlgebraicGeometry.Numerical.Examples

/-- The hyperplane class as a polarisation of the K3 numerical ring.

`hd : d ≠ 0` is what makes `∫H² = 2d` positive, matching the convention of
`k3NumericalVariety_satisfiesHRR` and `k3_isK3`. -/
noncomputable def k3Polarization (d : ℕ) (hd : d ≠ 0) :
    Polarization (surfaceNumericalRing (2 * (d : ℚ))) where
  cls := H
  cls_mem := H_mem_piece_one
  degree_pow_pos := by
    have : (surfaceNumericalRing (2 * (d : ℚ))).degree (H ^ 2) = 2 * (d : ℚ) :=
      surfaceDegree_Hsq _
    rw [this]
    have : (0 : ℚ) < (d : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hd
    linarith

/-- The `H`-degree on the K3 model is `2d` times the `ch₁` coefficient. -/
theorem degH_k3 (d : ℕ) (hd : d ≠ 0) (E : SurfaceNum) :
    degH (k3NumericalVariety d) (k3Polarization d hd) E = 2 * (d : ℚ) * (E 1 : ℚ) := by
  show (surfaceNumericalRing (2 * (d : ℚ))).degree
      (algebraMap ℚ SurfaceRing (k3ChCoeff E 1) * H * H ^ 1) = _
  rw [pow_one, mul_assoc, ← pow_two,
    NumericalRingData.degree_algebraMap_mul, surfaceDegree_Hsq]
  show (E 1 : ℚ) * (2 * (d : ℚ)) = _
  ring

end Examples

end AlgebraicGeometry.Numerical
