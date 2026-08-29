/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.Slope
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.WeakSlopeTop
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.WeakTruncation

/-!
# Where the rank-zero objects go, on a surface

`SlopeCutoff.lean` answers this question on a **curve**: `degree_pos_of_rank_zero`
puts a nonzero rank-zero object on the strictly negative real axis, so it has
phase one, so it lies in `T β` for every `β < 1`.  On a **surface** that argument
is unavailable — a skyscraper has `c₁ = 0`, hence degree `0`, hence charge exactly
`0`, and `arg 0 = 0` is not a phase.  `WeakSlope.lean` says so explicitly and
leaves the question open.

`WeakSlopeTop.lean` supplies the slope that can answer it, `topSlope`, valued in
`WithTop ℝ` and `⊤` at rank zero.  This file draws the consequence for the cut of
`WeakCutoff.lean`, which is what that slope was for.

## The comparison, which is the point

| | curve (`SlopeData`) | surface (`WeakSlopeData`) |
|---|---|---|
| cutoff | `β : ℝ`, restricted to `β < 1` | `μ₀ : WithTop ℝ`, restricted to `μ₀ ≠ ⊤` |
| rank zero gives | `φ⁻ = 1` | `μ⁻ = ⊤` |
| needs | `degree_pos_of_rank_zero` | nothing beyond `rank_nonneg` |

The Harder--Narasimhan filtration cannot get in the way for the same reason it
could not on a curve: rank is additive and nonnegative, so rank zero passes to
every subobject and quotient, hence to the last HN factor, hence `μ⁻ = ⊤`.
`rank_eq_zero_of_shortExact` is that step and is `omega` on two inequalities.

Note what `mem_hnTors_of_rank_zero` does **not** ask for.  It has no semistability
hypothesis, and no hypothesis on the degree — so it holds for a skyscraper, whose
charge is `0` and which therefore has no phase to be compared at all.  That is
strictly more than the curve statement can express, rather than a transcription
of it.

## What is here beyond `WeakSlopeTop.lean`

That file defines `topSlope` and pins its two values.  This one adds the facts
that need `rank_nonneg` as well — that `⊤` occurs at rank zero and nowhere else,
and the order comparisons that follow — and then the cutoff consequence.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace WeakSlopeData

variable (D : WeakSlopeData A)

/-- Rank zero passes to both ends of a short exact sequence, because rank is
additive and never negative.  The `SlopeData` proof, which never reads the degree
field and so did not need the curve hypothesis. -/
theorem rank_eq_zero_of_shortExact {S : ShortComplex A} (hS : S.ShortExact)
    (h : D.rank S.X₂ = 0) : D.rank S.X₁ = 0 ∧ D.rank S.X₃ = 0 := by
  have hadd := D.rank_additive S hS
  have h1 : 0 ≤ D.rank S.X₁ := D.rank_nonneg S.X₁
  have h3 : 0 ≤ D.rank S.X₃ := D.rank_nonneg S.X₃
  omega

/-! ### `⊤` occurs at rank zero and nowhere else

`WeakSlopeTop.lean` proves each value in its own case.  Combining them into an
`iff` is where `rank_nonneg` enters: without it a negative rank would be a third
case, and the charge would leave the closed upper half-plane. -/

/-- The honest slope is `⊤` on exactly the rank-zero objects. -/
theorem topSlope_eq_top_iff_rank_eq_zero {E : A} :
    D.topSlope E = ⊤ ↔ D.rank E = 0 := by
  refine ⟨fun h => ?_, D.topSlope_of_rank_zero⟩
  rcases lt_or_eq_of_le (D.rank_nonneg E) with hpos | hzero
  · rw [D.topSlope_of_rank_pos hpos] at h
    exact absurd h WithTop.coe_ne_top
  · exact hzero.symm

theorem topSlope_ne_top_iff_rank_pos {E : A} :
    D.topSlope E ≠ ⊤ ↔ 0 < D.rank E := by
  rw [Ne, topSlope_eq_top_iff_rank_eq_zero]
  exact ⟨fun h => lt_of_le_of_ne (D.rank_nonneg E) (Ne.symm h), fun h => ne_of_gt h⟩

/-! ### The order, restated in `WithTop ℝ` -/

/-- The honest slope order and the `ℝ`-valued slope order agree on objects of
positive rank, where both are defined. -/
theorem topSlope_le_topSlope_iff_slope_le {E F : A} (hE : 0 < D.rank E)
    (hF : 0 < D.rank F) : D.topSlope E ≤ D.topSlope F ↔ D.slope E ≤ D.slope F := by
  rw [D.topSlope_of_rank_pos hE, D.topSlope_of_rank_pos hF]
  exact WithTop.coe_le_coe

/-- **The phase order is the honest slope order** on objects of positive rank.
`WeakSlope.lean`'s `phase_le_iff_slope_le`, carried into `WithTop ℝ`. -/
theorem phase_le_iff_topSlope_le {E F : A} (hE : 0 < D.rank E) (hF : 0 < D.rank F) :
    D.phase E ≤ D.phase F ↔ D.topSlope E ≤ D.topSlope F := by
  rw [D.topSlope_le_topSlope_iff_slope_le hE hF]
  exact D.phase_le_iff_slope_le hE hF

/-- A rank-zero object has honest slope above every positive-rank object's.  On a
surface this is the whole ordering statement available about a skyscraper, and no
phase comparison can reproduce it. -/
theorem topSlope_lt_topSlope_of_rank_pos_of_rank_zero {E F : A}
    (hE : 0 < D.rank E) (hF : D.rank F = 0) : D.topSlope E < D.topSlope F := by
  rw [D.topSlope_of_rank_pos hE, D.topSlope_of_rank_zero hF]
  exact WithTop.coe_lt_top _

/-! ### Rank zero is torsion at every finite cutoff -/

/-- **Every Harder--Narasimhan factor of a rank-zero object has rank zero**, so
the lowest HN slope is `⊤`.  Rank is additive and nonnegative, so rank zero passes
to each chain step and to its cokernel. -/
theorem μMinus_eq_top_of_rank_zero {E : A}
    (F : AbelianWeakHNFiltration D.toWeakStabilityFunction E) (h : D.rank E = 0) :
    F.μMinus = ⊤ := by
  have hn := F.nonempty
  set last : Fin F.n := ⟨F.n - 1, by lia⟩ with hlastdef
  have hlast : F.chain last.succ = ⊤ := by
    have hindex : last.succ = ⟨F.n, by lia⟩ := Fin.ext (by simp [hlastdef]; lia)
    rw [hindex, F.chain_top]
  set i := Subobject.ofLE (F.chain last.castSucc) (F.chain last.succ)
    (le_of_lt (F.chain_strictMono last.castSucc_lt_succ)) with hidef
  have hSE := StabilityFunction.shortExact_of_mono i
  have hmid : D.rank ((F.chain last.succ : Subobject E) : A) = 0 := by
    rw [hlast, D.rank_iso (asIso (⊤ : Subobject E).arrow)]
    exact h
  have hfactor : D.rank (cokernel i) = 0 :=
    (D.rank_eq_zero_of_shortExact hSE hmid).2
  rw [AbelianWeakHNFiltration.μMinus, ← F.factor_slope last]
  exact D.topSlope_of_rank_zero hfactor

/-- **Rank-zero objects are torsion at every finite cutoff.**

The surface counterpart of `SlopeData.mem_hnTors_of_rank_zero`, and strictly
stronger where the two overlap: that one needs `degree_pos_of_rank_zero` to reach
phase one and so restricts to `β < 1`, while this one reads `μ⁻ = ⊤` off
`rank_nonneg` alone and so covers every cutoff short of `⊤` itself. -/
theorem mem_hnTors_of_rank_zero
    (hHN : D.toWeakStabilityFunction.HasHNProperty) {μ₀ : WithTop ℝ} (hμ : μ₀ ≠ ⊤)
    {E : A} (hE : ¬IsZero E) (h : D.rank E = 0) :
    E ∈ WeakStabilityFunctionOn.hnTors D.toWeakStabilityFunction μ₀ := by
  obtain ⟨F⟩ := hHN E hE
  refine Or.inr ⟨F, ?_⟩
  rw [D.μMinus_eq_top_of_rank_zero F h]
  exact Ne.lt_top hμ

end WeakSlopeData

/-! ## The curve case inherits

`SlopeData.toWeakSlopeData` forgets `0 < degree` to `0 ≤ degree`, so a curve lane
gets the `WithTop ℝ` slope and everything above without a second development. -/

namespace SlopeData

variable (D : SlopeData A)

/-- On a curve too, the honest slope is `⊤` exactly at rank zero. -/
theorem toWeakSlopeData_topSlope_eq_top_iff {E : A} :
    D.toWeakSlopeData.topSlope E = ⊤ ↔ D.rank E = 0 :=
  D.toWeakSlopeData.topSlope_eq_top_iff_rank_eq_zero

end SlopeData

end CategoryTheory.Triangulated
