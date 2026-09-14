/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.ChargeFamily
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The exponential charge, indexed by truncation degree

One polynomial. `Walls/Numerical/` carries the surface charge on three real
coordinates and `Walls/Threefold/` the Bayer--Macrì--Toda charge on four, and
the threefold file's own docstring records that they are the same expansion of
`-∫exp(-(β + iα)H)ch` at two codimensions. They are nevertheless two unrelated
roots, and no fourfold charge exists. This file is the shared parent, and
`Walls/Exp/Comparison.lean` proves both existing families are instances of it.

## The index is the truncation degree, never the dimension

`m` counts how many codimensions survive, not how many the variety has. The two
are equal for the untilted charge of an `n`-fold, and that coincidence is what
made the wrong index look right: a family indexed by dimension covers the
surface at `m = n = 2` and the threefold at `m = n = 3`, and then fails at the
first example where they differ. The cubic-threefold Kuznetsov charge is one,
at `(n, m) = (3, 2)`, and `Exp.tiltChargeFamily` in a later slice is the
truncation that produces it.

This is also why `numerical-k-theory-e5` is parked. That track assumed one type
indexed by dimension would cover the surface, threefold and fourfold numerical
formulas, recorded the assumption FALSIFIED on 2026-08-27, and parked the epic.
The falsification stands; the index was the defect.

## What the moments are for

`ofMoments` takes an arbitrary moment sequence rather than a vector of degrees,
so that the two genuinely different sources of moments share it:

* scalar moments `μ j = w^j · d_{m-j}` on compressed `H`-degrees, below, which
  is the polarised case of Picard rank one;
* intersection-form moments `μ₀ = ch₂`, `μ₁ = ⟨w, ch₁⟩`, `μ₂ = ⟨w, w⟩·rk`, which
  is the divisorial case of arbitrary Picard rank, in a later slice.

The second does not factor through the first: the `H`-compression is not
injective once the Picard rank exceeds one. So the two are siblings under
`ofMoments` rather than one being a specialization of the other, and a kernel
indexed by compressed degrees alone would have excluded the divisorial charge —
which two of the three independent designs of this tree wrongly concluded.

## What is not here

No twist, no discriminant, no truncation, and no wall theory. This module
imports `Walls/ChargeFamily.lean` and Mathlib and nothing else, so the root
imports no leaf; the comparisons with the existing families live beside it in
`Comparison.lean`, which may import both.
-/

open Complex Finset

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

namespace Exp

/-- The exponential coefficient `(-1)^j / j!`, written once.

Every charge in the tree spells these out per dimension: `1`, `-1`, `1/2` for
the surface and additionally `-(1/6)` for the threefold. -/
def coeff (j : ℕ) : ℂ := (-1) ^ j / (j.factorial : ℂ)

@[simp] theorem coeff_zero : coeff 0 = 1 := by simp [coeff]

@[simp] theorem coeff_one : coeff 1 = -1 := by simp [coeff]

theorem coeff_two : coeff 2 = 1 / 2 := by norm_num [coeff, Nat.factorial]

theorem coeff_three : coeff 3 = -(1 / 6) := by norm_num [coeff, Nat.factorial]

/-- **The charge.** `Z = -∑_{j ≤ m} (-1)^j/j! · μ j`.

The moment sequence is arbitrary; `moments` below supplies the scalar one and
the divisorial lane supplies the intersection-form one. The leading sign is the
convention of `-∫exp(-(B + iω))ch`, which is what both existing families use. -/
def ofMoments (m : ℕ) (mu : ℕ → ℂ) : ℂ := -∑ j ∈ range (m + 1), coeff j * mu j

theorem ofMoments_add (m : ℕ) (mu nu : ℕ → ℂ) :
    ofMoments m (mu + nu) = ofMoments m mu + ofMoments m nu := by
  simp only [ofMoments, Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add]

/-! ### The scalar moments: compressed `H`-degrees -/

/-- Compressed `H`-degrees at truncation degree `m`: `d k = ∫H^(n-k)·ch_k`, so
the slot index is codimension and slot `0` carries the weight `∫Hⁿ` rather than
the bare rank. Both existing transports already obey that convention.

An `abbrev`, so no new carrier is introduced and
`scripts/check_single_instantiation.py`, which counts `structure` heads, has
nothing to see. -/
abbrev HDeg (m : ℕ) : Type := Fin (m + 1) → ℝ

/-- The scalar moments `μ j = w^j · d_{m-j}` of a compressed degree vector.

`w` is the single complex parameter `B + iω` of the polarised lane; the two
lanes disagree about which of its parts comes first, and `stChart` and
`alphaBetaChart` below are where that disagreement is written down. -/
def moments (m : ℕ) (w : ℂ) (d : HDeg m) (j : ℕ) : ℂ :=
  if h : j ≤ m then w ^ j * ((d ⟨m - j, by omega⟩ : ℝ) : ℂ) else 0

theorem moments_add (m : ℕ) (w : ℂ) (d e : HDeg m) :
    moments m w (d + e) = moments m w d + moments m w e := by
  funext j
  by_cases h : j ≤ m <;> simp [moments, h, mul_add]

/-- **The polarised charge at truncation degree `m`**, as an additive map. -/
def charge (m : ℕ) (w : ℂ) : HDeg m →+ ℂ :=
  AddMonoidHom.mk' (fun d => ofMoments m (moments m w d)) (by
    intro d e
    rw [moments_add]
    exact ofMoments_add m _ _)

@[simp] theorem charge_apply (m : ℕ) (w : ℂ) (d : HDeg m) :
    charge m w d = ofMoments m (moments m w d) := rfl

/-- The scalar charge family, an inhabitant of the dimension-independent wall
root with parameter space `ℂ`.

The parameter space is `ℂ` and not `ℝ × ℝ` on purpose: `w` is one complex
number, and the real charts that present it as a pair are `reindex`es of this
family rather than its definition. -/
def chargeFamily (m : ℕ) : ChargeFamily ℂ (HDeg m) := ⟨charge m⟩

@[simp] theorem chargeFamily_charge (m : ℕ) (w : ℂ) (d : HDeg m) :
    (chargeFamily m).charge w d = charge m w d := rfl

/-! ### The two real charts

The surface lane parameterizes by `(s, t)` and the threefold lane by `(α, β)`,
and the two orders are transposed. Writing both here means the transposition is
recorded once instead of at every consumer that moves between the lanes. -/

/-- The surface lane's chart: `(s, t) ↦ s + tI`. -/
abbrev stChart (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * I

/-- The threefold lane's chart: `(α, β) ↦ β + αI`.

Note the transposition against `stChart`. The threefold family's parameter pair
is `(α, β)` with `α` the ample coefficient, where the surface family's is
`(s, t)` with `t` the ample coefficient. -/
abbrev alphaBetaChart (p : ℝ × ℝ) : ℂ := (p.2 : ℂ) + (p.1 : ℂ) * I

end Exp

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
