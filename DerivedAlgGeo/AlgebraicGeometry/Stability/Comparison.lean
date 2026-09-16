/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker
import DerivedAlgGeo.AlgebraicGeometry.Stability.Slope.HarderNarasimhan

/-!
# Gieseker stability against μ-slope stability

The two stability notions on `Coh X` are ordered by different data: Gieseker stability by the
whole reduced Hilbert polynomial compared at infinity, μ-stability by a single ratio of Hilbert
coefficients. This file owns everything that mentions both, and is imported by neither.

## What is delivered, and what is not

One implication in one direction: a Gieseker-semistable sheaf is weakly μ-semistable. The
converse — μ-semistable implies Gieseker-semistable — is not delivered here in any form, and
neither is any statement relating the two *strict* notions.

The two theories are therefore compared and **not identified**. `IsGiesekerSemistable` is defined
from the Gieseker order alone, `WeakStabilityFunctionOn.IsSemistable` from the weak slope alone,
and neither definition mentions the other. `Gieseker/Basic.lean` records separately why no
central charge can reproduce the Gieseker order, so the comparison is between *slopes* and
happens here rather than at the level of the stability functions.

## Why purity is what makes the implication true

`WeakStabilityFunctionOn.IsSemistable` quantifies over every nonzero `B : Subobject F` and
compares in `WithTop ℝ`, where a multiplicity-zero subobject has slope `⊤` and would destabilise
`F` — while satisfying the Gieseker order vacuously, because its reduced Hilbert function is the
junk value `0`. The purity conjunct of `IsGiesekerSemistable` is exactly what rules that out:
every nonzero subobject then has positive multiplicity, both slopes are finite, and the
lexicographic criterion read at `P.dim - 1` is the slope comparison. Without purity the statement
is false, so the hypothesis travels with the theorem and is not weakened by the relocation.

This is also where the subsheaf quantifier changes shape. Gieseker stability quantifies over
monomorphisms `G ⟶ F`; the abstract slope theory quantifies over `Subobject F`. The translation
is made here, in the one file that needs both, and is kept out of either definition.

## Placement

MO1.08 (#1319) made `Slope/` and `Gieseker/` siblings over the shared Hilbert-polynomial data,
and this file is the comparison owner that split names. The declarations below were previously
the tail of `Gieseker/MuStability.lean` and of `Gieseker/HarderNarasimhan/Consequences.lean`,
where they were the only reason either module reached the other theory.
-/

universe u

open CategoryTheory Limits CategoryTheory.Triangulated

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

namespace PolarizedVarietyData

variable {P : PolarizedVarietyData k X}

/-! ### The slope, read as a normalized Hilbert coefficient -/

/-- The slope is the normalized Hilbert coefficient one below the top, read in `ℝ`. This holds
without any positivity hypothesis, because both sides take the same junk value at multiplicity
zero. -/
theorem weakSlopeData_slope_eq_normalizedCoefficient (h : MuPositivityData P) (F : Coh X) :
    (P.weakSlopeData h).slope F = ((P.normalizedCoefficient F (P.dim - 1) : ℚ) : ℝ) := by
  rw [weakSlopeData_slope, normalizedCoefficient]
  push_cast
  rfl

/-- The same identification in `WithTop ℝ`, where positive multiplicity is what keeps the slope
finite. -/
theorem weakSlopeData_topSlope_eq_normalizedCoefficient (h : MuPositivityData P) {F : Coh X}
    (hF : 0 < P.multiplicity F) :
    (P.weakSlopeData h).topSlope F =
      ((((P.normalizedCoefficient F (P.dim - 1) : ℚ) : ℝ)) : WithTop ℝ) := by
  have hrank : 0 < (P.weakSlopeData h).rank F := by
    rw [weakSlopeData_rank]
    exact hF
  rw [(P.weakSlopeData h).topSlope_of_rank_pos hrank,
    weakSlopeData_slope_eq_normalizedCoefficient h F]

/-! ### The comparison of the two orders -/

/-- The Gieseker order between sheaves of positive multiplicity implies the slope inequality,
by the lexicographic criterion read at `P.dim - 1`. -/
theorem topSlope_le_of_giesekerLE (h : MuPositivityData P) {F G : Coh X}
    (hF : 0 < P.multiplicity F) (hG : 0 < P.multiplicity G) (hle : P.GiesekerLE F G) :
    (P.weakSlopeData h).topSlope F ≤ (P.weakSlopeData h).topSlope G := by
  rw [weakSlopeData_topSlope_eq_normalizedCoefficient h hF,
    weakSlopeData_topSlope_eq_normalizedCoefficient h hG, WithTop.coe_le_coe, Rat.cast_le]
  exact normalizedCoefficient_pred_le_of_giesekerLE hF hG hle

/-- **Gieseker semistability implies weak μ-semistability.**

The proof uses purity twice and visibly: it is what gives every nonzero subobject positive
multiplicity, so that its slope is finite rather than `⊤`, and it is what puts that subobject
into the Gieseker quantifier with a reduced Hilbert function that is not the junk value. For a
non-pure sheaf the statement is **false**: a nonzero multiplicity-zero subobject has slope `⊤`,
which exceeds every finite slope, while satisfying the Gieseker order vacuously.

Only this direction is delivered. The reverse implication is not in scope. -/
theorem giesekerSemistable_implies_muSemistable (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    (P.weakSlopeData h).toWeakStabilityFunction.IsSemistable F := by
  refine ⟨hF.not_isZero, fun B hB ↦ ?_⟩
  have hmono : Mono (B.arrow) := inferInstance
  have hBpos : 0 < P.multiplicity (B : Coh X) := hF.1.2 (B : Coh X) B.arrow hmono hB
  exact topSlope_le_of_giesekerLE h hBpos hF.multiplicity_pos
    (hF.2 (B : Coh X) B.arrow hmono hB)

/-! ### The Harder–Narasimhan filtration of a Gieseker-semistable sheaf -/

/-- **The one-step Harder–Narasimhan filtration of a Gieseker-semistable sheaf.**

Gieseker semistability implies μ-semistability, and a semistable object is its own filtration.
This closes the loop back to the Gieseker order: the coarser numerical invariant sees no
destabilizing subsheaf either. It needs no `MuHNInput`, because the filtration is exhibited
rather than obtained from the existence theorem. -/
noncomputable def hnTrivialOfGiesekerSemistable (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction F :=
  AbelianWeakHNFiltration.ofSemistable (giesekerSemistable_implies_muSemistable h hF)

/-- **A Gieseker-semistable sheaf has a one-step Harder–Narasimhan filtration.** The propositional
form of `hnTrivialOfGiesekerSemistable`, which is the name #905 asks for; the data itself carries
a camelCase name because mathlib's naming convention forbids underscores in a `def`. -/
theorem giesekerSemistable_implies_hn_trivial (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    Nonempty (AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction F) :=
  ⟨hnTrivialOfGiesekerSemistable h hF⟩

/-- The trivial filtration has exactly one factor. -/
theorem giesekerSemistable_hn_trivial_n (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    (hnTrivialOfGiesekerSemistable h hF).n = 1 := rfl

/-- Both extrema of the trivial filtration are the slope of the sheaf itself. -/
theorem giesekerSemistable_hn_trivial_muPlus (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    (hnTrivialOfGiesekerSemistable h hF).μPlus =
      (P.weakSlopeData h).topSlope F := rfl

/-- Both extrema of the trivial filtration are the slope of the sheaf itself. -/
theorem giesekerSemistable_hn_trivial_muMinus (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    (hnTrivialOfGiesekerSemistable h hF).μMinus =
      (P.weakSlopeData h).topSlope F := rfl

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
