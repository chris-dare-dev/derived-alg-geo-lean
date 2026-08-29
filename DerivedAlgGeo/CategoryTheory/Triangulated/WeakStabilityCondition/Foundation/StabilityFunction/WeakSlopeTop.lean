/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.WeakSlope
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.WeakSlopeGeometry

/-!
# The surface slope, honestly valued

`WeakSlope.lean` gives `WeakSlopeData` a slope `degree / rank`, and says of it, correctly,
that it is **junk at rank zero** — division by zero returns `0`, where the classical slope
is `+∞`. Every statement there carries a positive-rank hypothesis for that reason.

`WeakSlopeGeometry.lean` gives `WeakStabilityFunctionOn` a slope valued in `WithTop ℝ`,
which is `⊤` exactly on the real boundary of the closed upper half-plane — in particular
at charge `0`, the skyscraper.

This file connects them, which is what makes the junk value harmless rather than merely
quarantined: `topSlope` is the honest slope of a `WeakSlopeData`, and the two agree wherever
the `ℝ`-valued one means anything.

## Why this is the last piece of the surface redirect's first stage

A rank-zero object on a surface is why `SlopeData` could not be instantiated: a skyscraper
has `degree = 0` as well, so its charge is `0` and it has no phase. The cutoff classes of
`WeakCutoff.lean` place it at `⊤`, in the torsion class at every finite cutoff, with no
positivity hypothesis at all. `topSlope_of_rank_zero` is the statement that `WeakSlopeData`'s
own objects land there — so the geometry and the cutoff agree about skyscrapers, rather than
each being separately correct about a different notion of slope.
-/

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace WeakSlopeData

variable (D : WeakSlopeData A)

/-- **The honest slope of a `WeakSlopeData`**, valued in `WithTop ℝ`.

Defined through the weak stability function rather than by a second `if`, so that every
result about `WeakStabilityFunctionOn.slope` — the see-saws, `slope_le_of_epi`, and the
cutoff classes — applies to it without transport. -/
def topSlope (E : A) : WithTop ℝ := D.toWeakStabilityFunction.slope E

theorem topSlope_eq_chargeSlope (E : A) :
    D.topSlope E = chargeSlope (D.toWeakStabilityFunction.charge E) := rfl

/-- **At positive rank the two slopes agree**, under the coercion `ℝ → WithTop ℝ`.

This is the whole of the compatibility: `WeakSlope.lean`'s `slope` is correct exactly where
its positive-rank hypotheses say it is. -/
theorem topSlope_of_rank_pos {E : A} (h : 0 < D.rank E) :
    D.topSlope E = ((D.slope E : ℝ) : WithTop ℝ) := by
  have hZ : D.toWeakStabilityFunction.charge E = D.charge E := D.toWeakStabilityFunction_Z E
  have him : 0 < (D.toWeakStabilityFunction.charge E).im := by
    rw [hZ, charge_im]
    exact_mod_cast h
  rw [topSlope, D.toWeakStabilityFunction.slope_of_im_pos him, hZ, charge_re, charge_im, slope]
  norm_num

/-- **At rank zero the honest slope is `⊤`** — no positivity hypothesis anywhere.

This is the skyscraper. `WeakSlope.lean`'s `slope` returns `0` here, which is the junk value
its docstring warns about; `topSlope` returns the classical `+∞` instead, and that is what
`WeakCutoff.lean`'s `mem_hnTors_of_slope_eq_top` reads. -/
theorem topSlope_of_rank_zero {E : A} (h : D.rank E = 0) : D.topSlope E = ⊤ := by
  refine D.toWeakStabilityFunction.slope_of_im_nonpos ?_
  have hZ : D.toWeakStabilityFunction.charge E = D.charge E := D.toWeakStabilityFunction_Z E
  rw [hZ, charge_im, h]
  simp

/-- The honest slope is an isomorphism invariant. -/
theorem topSlope_eq_of_iso {E F : A} (e : E ≅ F) : D.topSlope E = D.topSlope F :=
  D.toWeakStabilityFunction.slope_eq_of_iso e

end WeakSlopeData

end CategoryTheory.Triangulated
