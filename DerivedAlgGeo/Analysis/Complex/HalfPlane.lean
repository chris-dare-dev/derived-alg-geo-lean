/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# The semi-closed and closed upper half-planes

Two subsets of `ℂ` and the three facts about them that every consumer needs.
Nothing here is categorical, algebraic or stability-theoretic: the statements
quantify over complex numbers and use `Complex.arg` alone.

## Placement

These declarations were introduced beside their first consumer, the central
charge conditions in `StabilityCondition/Weak/Charge.lean`, and that file's own
docstring recorded them as an upstream candidate for
`Mathlib/Analysis/Complex/UpperHalfPlane/`. MO1.13 (#1324) acted on that: the
Euclidean core of the mass-subadditivity proof must be importable without
categories and without stability, and it cannot be while a half-plane
membership predicate lives inside the stability tree. The nearest owner at the
pinned Mathlib revision is `Analysis/Complex/`, so that is the path.

The namespace is deliberately **not** changed. `CategoryTheory` reads oddly over
an analysis file and the oddity is accepted rather than repaired: a namespace
cutover would rename declarations and invalidate the immutable review payloads
that `exe/RestateHistoricalNames.lean` exists to protect. This is standing
decision 1 of the cutover ledger.
-/

noncomputable section

open Complex Real

namespace CategoryTheory

/-- The semi-closed upper half-plane used for central charges: positive
imaginary part together with the negative real axis. -/
def semiClosedUpperHalfPlane : Set ℂ :=
  {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ z.re < 0}

theorem semiClosedUpperHalfPlane_ne_zero {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : z ≠ 0 := by
  rcases hz with him | ⟨him, hre⟩
  · exact ne_of_apply_ne im him.ne'
  · exact ne_of_apply_ne re hre.ne

/-- The **closed** upper half-plane: the weak condition, which unlike
`semiClosedUpperHalfPlane` contains `0`.  That single difference is the whole of
the weak/strict distinction, and it is why μ-slope stability on a surface is weak
— a skyscraper has zero rank and zero degree, so its μ-charge is `0`. -/
def closedUpperHalfPlane : Set ℂ :=
  {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ z.re ≤ 0}

theorem semiClosedUpperHalfPlane_subset_closed :
    semiClosedUpperHalfPlane ⊆ closedUpperHalfPlane :=
  fun _ hz ↦ hz.imp id (fun h ↦ ⟨h.1, h.2.le⟩)

theorem arg_pos_of_mem_semiClosedUpperHalfPlane {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : 0 < arg z := by
  rcases hz with him | ⟨him, hre⟩
  · refine lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) ?_
    exact fun h => him.ne' (arg_eq_zero_iff.mp h.symm).2
  · have hz : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
    rw [hz, arg_ofReal_of_neg hre]
    exact Real.pi_pos

end CategoryTheory
