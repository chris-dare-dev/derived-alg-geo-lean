/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.IntrinsicPhases
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.EMetricSpace.Defs

/-!
# The owner slicing distance

The generalized Bridgeland distance on repository-owned slicings is the
supremum of the two intrinsic phase discrepancies.  It defines the intrinsic
pseudo-extended-metric topology on owner slicings.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The generalized distance between two owner slicings. -/
def slicingDist (s t : Slicing C) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E), ENNReal.ofReal
    (max |s.phiPlus C E hE - t.phiPlus C E hE|
      |s.phiMinus C E hE - t.phiMinus C E hE|)

/-- The discrepancy on one nonzero object is bounded by the slicing distance. -/
theorem slicingDistTerm_le (s t : Slicing C) (E : C) (hE : ¬IsZero E) :
    ENNReal.ofReal (max |s.phiPlus C E hE - t.phiPlus C E hE|
      |s.phiMinus C E hE - t.phiMinus C E hE|) ≤ slicingDist C s t :=
  le_iSup_of_le E (le_iSup_of_le hE le_rfl)

/-- The highest-phase discrepancy is bounded by the slicing distance. -/
theorem phiPlusDist_le (s t : Slicing C) (E : C) (hE : ¬IsZero E) :
    ENNReal.ofReal |s.phiPlus C E hE - t.phiPlus C E hE| ≤ slicingDist C s t :=
  (ENNReal.ofReal_le_ofReal (le_max_left _ _)).trans (slicingDistTerm_le C s t E hE)

/-- The lowest-phase discrepancy is bounded by the slicing distance. -/
theorem phiMinusDist_le (s t : Slicing C) (E : C) (hE : ¬IsZero E) :
    ENNReal.ofReal |s.phiMinus C E hE - t.phiMinus C E hE| ≤ slicingDist C s t :=
  (ENNReal.ofReal_le_ofReal (le_max_right _ _)).trans (slicingDistTerm_le C s t E hE)

/-- The owner slicing distance vanishes on the diagonal. -/
@[simp]
theorem slicingDist_self (s : Slicing C) : slicingDist C s s = 0 := by
  simp [slicingDist]

/-- The owner slicing distance is symmetric. -/
theorem slicingDist_symm (s t : Slicing C) : slicingDist C s t = slicingDist C t s := by
  simp only [slicingDist, abs_sub_comm]

/-- The owner slicing distance satisfies the triangle inequality. -/
theorem slicingDist_triangle (s t u : Slicing C) :
    slicingDist C s u ≤ slicingDist C s t + slicingDist C t u := by
  apply iSup_le
  intro E
  apply iSup_le
  intro hE
  let dst : ℝ := max |s.phiPlus C E hE - t.phiPlus C E hE|
    |s.phiMinus C E hE - t.phiMinus C E hE|
  let dtu : ℝ := max |t.phiPlus C E hE - u.phiPlus C E hE|
    |t.phiMinus C E hE - u.phiMinus C E hE|
  have hdst : 0 ≤ dst := le_max_of_le_left (abs_nonneg _)
  have hdtu : 0 ≤ dtu := le_max_of_le_left (abs_nonneg _)
  calc
    ENNReal.ofReal (max |s.phiPlus C E hE - u.phiPlus C E hE|
        |s.phiMinus C E hE - u.phiMinus C E hE|)
        ≤ ENNReal.ofReal (dst + dtu) := by
          apply ENNReal.ofReal_le_ofReal
          apply max_le
          · calc
              |s.phiPlus C E hE - u.phiPlus C E hE| ≤
                  |s.phiPlus C E hE - t.phiPlus C E hE| +
                    |t.phiPlus C E hE - u.phiPlus C E hE| := by
                      rw [show s.phiPlus C E hE - u.phiPlus C E hE =
                        (s.phiPlus C E hE - t.phiPlus C E hE) +
                          (t.phiPlus C E hE - u.phiPlus C E hE) by ring]
                      exact abs_add_le _ _
              _ ≤ dst + dtu := add_le_add (le_max_left _ _) (le_max_left _ _)
          · calc
              |s.phiMinus C E hE - u.phiMinus C E hE| ≤
                  |s.phiMinus C E hE - t.phiMinus C E hE| +
                    |t.phiMinus C E hE - u.phiMinus C E hE| := by
                      rw [show s.phiMinus C E hE - u.phiMinus C E hE =
                        (s.phiMinus C E hE - t.phiMinus C E hE) +
                          (t.phiMinus C E hE - u.phiMinus C E hE) by ring]
                      exact abs_add_le _ _
              _ ≤ dst + dtu := add_le_add (le_max_right _ _) (le_max_right _ _)
    _ = ENNReal.ofReal dst + ENNReal.ofReal dtu := ENNReal.ofReal_add hdst hdtu
    _ ≤ slicingDist C s t + slicingDist C t u :=
      add_le_add (slicingDistTerm_le C s t E hE) (slicingDistTerm_le C t u E hE)

/-- Owner slicings carry the pseudo-extended metric induced by intrinsic phase distance. -/
noncomputable instance : PseudoEMetricSpace (Slicing C) where
  edist := slicingDist C
  edist_self := slicingDist_self C
  edist_comm := slicingDist_symm C
  edist_triangle := slicingDist_triangle C

/-- A strict slicing-distance bound controls the highest intrinsic phase. -/
theorem abs_phiPlus_sub_lt_of_slicingDist (s t : Slicing C) {E : C} (hE : ¬IsZero E)
    {ε : ℝ} (hε : 0 < ε) (hd : slicingDist C s t < ENNReal.ofReal ε) :
    |s.phiPlus C E hE - t.phiPlus C E hE| < ε := by
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp
    ((phiPlusDist_le C s t E hE).trans_lt hd)

/-- A strict slicing-distance bound controls the lowest intrinsic phase. -/
theorem abs_phiMinus_sub_lt_of_slicingDist (s t : Slicing C) {E : C} (hE : ¬IsZero E)
    {ε : ℝ} (hε : 0 < ε) (hd : slicingDist C s t < ENNReal.ofReal ε) :
    |s.phiMinus C E hE - t.phiMinus C E hE| < ε := by
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp
    ((phiMinusDist_le C s t E hE).trans_lt hd)

/-- A nonzero semistable object for a nearby slicing lies in the corresponding
phase window for the original slicing. -/
theorem intervalProp_of_semistable_slicingDist (s t : Slicing C) {E : C} {φ : ℝ}
    (hE : ¬IsZero E) (hP : t.P φ E) {ε : ℝ} (hε : 0 < ε)
    (hd : slicingDist C s t < ENNReal.ofReal ε) :
    s.intervalProp C (φ - ε) (φ + ε) E := by
  have hplus := abs_phiPlus_sub_lt_of_slicingDist C s t hE hε hd
  have hminus := abs_phiMinus_sub_lt_of_slicingDist C s t hE hε hd
  rw [t.phiPlus_eq_of_semistable C E hE φ hP, abs_lt] at hplus
  rw [t.phiMinus_eq_of_semistable C E hE φ hP, abs_lt] at hminus
  obtain ⟨F, hn, hFplus, hFminus⟩ := s.exists_hn_intrinsic_width C hE
  refine Or.inr ⟨F, fun i => ⟨?_, ?_⟩⟩
  · calc
      φ - ε < s.phiMinus C E hE := by linarith [hminus.1]
      _ = F.phiMinus C hn := hFminus.symm
      _ ≤ F.φ i := (F.phase_mem_range C hn i).1
  · calc
      F.φ i ≤ F.phiPlus C hn := (F.phase_mem_range C hn i).2
      _ = s.phiPlus C E hE := hFplus
      _ < φ + ε := by linarith [hplus.2]

/-- Uniform phase bounds give an upper bound for the owner slicing distance. -/
theorem slicingDist_le_of_phase_bounds (s t : Slicing C) {ε : ℝ}
    (hplus : ∀ (E : C) (hE : ¬IsZero E),
      |s.phiPlus C E hE - t.phiPlus C E hE| ≤ ε)
    (hminus : ∀ (E : C) (hE : ¬IsZero E),
      |s.phiMinus C E hE - t.phiMinus C E hE| ≤ ε) :
    slicingDist C s t ≤ ENNReal.ofReal ε := by
  apply iSup_le
  intro E
  apply iSup_le
  intro hE
  exact ENNReal.ofReal_le_ofReal (max_le (hplus E hE) (hminus E hE))

end CategoryTheory.Triangulated
