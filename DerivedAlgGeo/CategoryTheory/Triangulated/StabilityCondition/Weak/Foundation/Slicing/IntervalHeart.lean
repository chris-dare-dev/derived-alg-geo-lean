/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhaseBounds
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseShift
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseTruncation

/-!
# Placing thin owner intervals in shifted hearts

Objects whose intrinsic phases lie in an interval of length at most one belong
to a real phase-shifted owner heart.  These lemmas provide the categorical
bridge used by the small-gap part of deformed hom-vanishing.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Intrinsic phases in `(t,t+1]` place an object in the heart of the slicing
shifted by `t`. -/
theorem Slicing.mem_phaseShiftHeart_of_intrinsic_bounds
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (hminus : t < s.phiMinus C E hE)
    (hplus : s.phiPlus C E hE ≤ t + 1) :
    ((s.phaseShift C t).toTStructure C).heart E := by
  rw [(s.phaseShift C t).toTStructure_heart_iff C E]
  constructor
  · exact (s.phaseShift_gtProp_zero C t E).mpr
      (s.gtProp_of_phiMinus_gt C hE hminus)
  · exact (s.phaseShift_leProp C t 1 E).mpr
      (s.leProp_of_phiPlus_le C hE (by simpa [add_comm] using hplus))

/-- Every object in an open interval of width at most one lies in the heart
based at its lower endpoint. -/
theorem Slicing.mem_phaseShiftHeart_of_intervalProp
    (s : Slicing C) {E : C} {a b : ℝ}
    (hI : s.intervalProp C a b E) (hwidth : b ≤ a + 1) :
    ((s.phaseShift C a).toTStructure C).heart E := by
  by_cases hE : IsZero E
  · rw [(s.phaseShift C a).toTStructure_heart_iff C E]
    exact ⟨Or.inl hE, Or.inl hE⟩
  · apply s.mem_phaseShiftHeart_of_intrinsic_bounds C hE
    · exact s.phiMinus_gt_of_intervalProp C hE hI
    · exact (s.phiPlus_lt_of_intervalProp C hE hI).le.trans hwidth

/-- A shifted-heart object lies above the heart cutoff and below any supplied
upper intrinsic-phase bound. -/
theorem Slicing.gtProp_leProp_of_phaseShiftHeart
    (s : Slicing C) {E : C} {a u : ℝ}
    (hHeart : ((s.phaseShift C a).toTStructure C).heart E)
    (hE : ¬IsZero E) (hu : s.phiPlus C E hE ≤ u) :
    s.gtProp C a E ∧ s.leProp C u E := by
  rw [(s.phaseShift C a).toTStructure_heart_iff C E] at hHeart
  exact ⟨(s.phaseShift_gtProp_zero C a E).mp hHeart.1,
    s.leProp_of_phiPlus_le C hE hu⟩

/-- A shifted-heart object lies below the upper heart cutoff and above any
supplied lower intrinsic-phase bound. -/
theorem Slicing.geProp_leProp_of_phaseShiftHeart
    (s : Slicing C) {E : C} {a l : ℝ}
    (hHeart : ((s.phaseShift C a).toTStructure C).heart E)
    (hE : ¬IsZero E) (hl : l ≤ s.phiMinus C E hE) :
    s.geProp C l E ∧ s.leProp C (a + 1) E := by
  rw [(s.phaseShift C a).toTStructure_heart_iff C E] at hHeart
  refine ⟨s.geProp_of_phiMinus_ge C hE hl, ?_⟩
  simpa [add_comm] using (s.phaseShift_leProp C a 1 E).mp hHeart.2

omit [IsTriangulated C] in
/-- An intrinsic phase window also gives simultaneous old lower and upper
phase-cut membership. -/
theorem Slicing.gtProp_leProp_of_intrinsic_bounds
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {a b : ℝ}
    (hminus : a < s.phiMinus C E hE)
    (hplus : s.phiPlus C E hE ≤ b) :
    s.gtProp C a E ∧ s.leProp C b E :=
  ⟨s.gtProp_of_phiMinus_gt C hE hminus,
    s.leProp_of_phiPlus_le C hE hplus⟩

end CategoryTheory.Triangulated
