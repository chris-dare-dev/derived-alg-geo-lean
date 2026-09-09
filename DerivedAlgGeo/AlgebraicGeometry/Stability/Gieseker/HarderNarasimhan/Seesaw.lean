/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan.MaximalDestabilizing

/-!
# The see-saw inequality for the μ-slope on `Coh X`

For a short exact sequence `0 ⟶ B ⟶ C ⟶ Q ⟶ 0` of coherent sheaves, the slope of the middle
term lies between the slopes of the ends. This file proves the half of that statement the
Harder–Narasimhan recursion needs: if the sub has slope at most the quotient, then it has slope
at most the whole.

No such inequality exists for the abstract weak slope in `Foundation/StabilityFunction/**`, and
this one is not abstract: it is the mediant inequality for the ratio of two additive integer
invariants, and its `⊤` cases are decided by the geometric input carried by `MuPositivityData`.
It is stated here, for the recursion that consumes it.

## The three cases

Multiplicity and degree coefficient are both additive on short exact sequences, so with
`m = multiplicity` and `d = hilbertDegreeCoefficient` the middle term has `m C = m B + m Q` and
`d C = d B + d Q`.

* `m B = 0`. The sub has slope `⊤`, so the hypothesis forces the quotient to slope `⊤` as well,
  hence `m Q = 0`, hence `m C = 0` and the whole has slope `⊤`.
* `m B > 0` and `m Q = 0`. The whole has `m C = m B`, and the inequality reduces to
  `0 ≤ d Q`, which is exactly `MuPositivityData.degree_nonneg_of_multiplicity_zero`. This is the
  case that fails without that geometric input.
* Both positive. The mediant inequality: `d B / m B ≤ d Q / m Q` gives
  `d B / m B ≤ (d B + d Q) / (m B + m Q)`.
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

/-- Multiplicity is additive on a short exact sequence. -/
theorem multiplicity_shortExact {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    P.multiplicity S.X₂ = P.multiplicity S.X₁ + P.multiplicity S.X₃ :=
  P.hilbertCoefficient_additive S hS P.dim

/-- The degree coefficient is additive on a short exact sequence. -/
theorem hilbertDegreeCoefficient_shortExact {S : ShortComplex (Coh X)} (hS : S.ShortExact) :
    P.hilbertDegreeCoefficient S.X₂ =
      P.hilbertDegreeCoefficient S.X₁ + P.hilbertDegreeCoefficient S.X₃ :=
  P.hilbertCoefficient_additive S hS (P.dim - 1)

/-- **The see-saw inequality.** In a short exact sequence, if the sub has slope at most the
quotient then it has slope at most the whole. See the module docstring for the three cases; the
multiplicity-zero quotient is the one where the geometric input is used, and it is the only case
needing the quotient to be nonzero — the sub may be zero. -/
theorem topSlope_le_of_shortExact (h : MuPositivityData P) {S : ShortComplex (Coh X)}
    (hS : S.ShortExact) (h3 : ¬IsZero S.X₃)
    (hle : (P.weakSlopeData h).topSlope S.X₁ ≤ (P.weakSlopeData h).topSlope S.X₃) :
    (P.weakSlopeData h).topSlope S.X₁ ≤ (P.weakSlopeData h).topSlope S.X₂ := by
  have hm := multiplicity_shortExact (P := P) hS
  have hd := hilbertDegreeCoefficient_shortExact (P := P) hS
  have hnn1 := h.multiplicity_nonneg S.X₁
  have hnn3 := h.multiplicity_nonneg S.X₃
  rcases eq_or_lt_of_le hnn1 with h1zero | h1pos
  · -- the sub has slope `⊤`, so everything in sight does
    have hm1 : P.multiplicity S.X₁ = 0 := h1zero.symm
    rw [weakSlopeData_topSlope_of_multiplicity_zero h hm1] at hle ⊢
    have hm3 : P.multiplicity S.X₃ = 0 := by
      by_contra hne
      have hpos3 : 0 < P.multiplicity S.X₃ := by omega
      rw [weakSlopeData_topSlope_of_multiplicity_pos h hpos3] at hle
      exact (WithTop.coe_ne_top) (top_le_iff.mp hle)
    have hm2 : P.multiplicity S.X₂ = 0 := by omega
    rw [weakSlopeData_topSlope_of_multiplicity_zero h hm2]
  · rcases eq_or_lt_of_le hnn3 with h3zero | h3pos
    · -- the quotient has multiplicity zero: its degree coefficient is nonnegative
      have hm3 : P.multiplicity S.X₃ = 0 := h3zero.symm
      have hm2 : P.multiplicity S.X₂ = P.multiplicity S.X₁ := by omega
      have hd3 : 0 ≤ P.hilbertDegreeCoefficient S.X₃ :=
        h.degree_nonneg_of_multiplicity_zero S.X₃ h3 hm3
      have hpos2 : 0 < P.multiplicity S.X₂ := by omega
      rw [weakSlopeData_topSlope_of_multiplicity_pos h h1pos,
        weakSlopeData_topSlope_of_multiplicity_pos h hpos2, WithTop.coe_le_coe, hm2]
      have hm1r : (0 : ℝ) < (P.multiplicity S.X₁ : ℝ) := by exact_mod_cast h1pos
      have hd3r : (0 : ℝ) ≤ (P.hilbertDegreeCoefficient S.X₃ : ℝ) := by exact_mod_cast hd3
      rw [hd, div_le_div_iff_of_pos_right hm1r]
      push_cast
      linarith
    · -- both ends have positive multiplicity: the mediant inequality
      have hpos2 : 0 < P.multiplicity S.X₂ := by omega
      rw [weakSlopeData_topSlope_of_multiplicity_pos h h1pos,
        weakSlopeData_topSlope_of_multiplicity_pos h h3pos, WithTop.coe_le_coe] at hle
      rw [weakSlopeData_topSlope_of_multiplicity_pos h h1pos,
        weakSlopeData_topSlope_of_multiplicity_pos h hpos2, WithTop.coe_le_coe]
      have hm1r : (0 : ℝ) < (P.multiplicity S.X₁ : ℝ) := by exact_mod_cast h1pos
      have hm3r : (0 : ℝ) < (P.multiplicity S.X₃ : ℝ) := by exact_mod_cast h3pos
      have hm2r : (0 : ℝ) < (P.multiplicity S.X₂ : ℝ) := by exact_mod_cast hpos2
      rw [div_le_div_iff₀ hm1r hm3r] at hle
      rw [div_le_div_iff₀ hm1r hm2r]
      have hmr : (P.multiplicity S.X₂ : ℝ) =
          (P.multiplicity S.X₁ : ℝ) + (P.multiplicity S.X₃ : ℝ) := by exact_mod_cast hm
      have hdr : (P.hilbertDegreeCoefficient S.X₂ : ℝ) =
          (P.hilbertDegreeCoefficient S.X₁ : ℝ) +
            (P.hilbertDegreeCoefficient S.X₃ : ℝ) := by exact_mod_cast hd
      rw [hmr, hdr]
      nlinarith [hle, hm1r, hm3r]

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
