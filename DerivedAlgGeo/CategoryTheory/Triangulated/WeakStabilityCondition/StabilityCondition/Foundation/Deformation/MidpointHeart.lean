/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.IntervalHeart

/-!
# Common midpoint hearts for nearby phase windows

Two objects centred at nearby phases lie in one shifted owner heart.  This is
the geometric preparation for factoring a morphism between deformed-slice
objects in the small-gap case.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- The left target interval around two nearby phases has deformed width less
than one. -/
theorem midpoint_left_target_thin
    {ψ₁ ψ₂ ε : ℝ} (hsmall : ψ₁ ≤ ψ₂ + 2 * ε) (hε8 : ε < 1 / 8) :
    (ψ₁ + ε) - ((ψ₁ + ψ₂) / 2 - 1 / 2) + 2 * ε < 1 := by
  linarith

/-- The right target interval around two nearby phases has deformed width
less than one. -/
theorem midpoint_right_target_thin
    {ψ₁ ψ₂ ε : ℝ} (hsmall : ψ₁ ≤ ψ₂ + 2 * ε) (hε8 : ε < 1 / 8) :
    (((ψ₁ + ψ₂) / 2 - 1 / 2) + 1) - (ψ₂ - ε) + 2 * ε < 1 := by
  linarith

/-- The image window between two ordered nearby phases remains thin. -/
theorem midpoint_image_window_thin
    {ψ₁ ψ₂ ε : ℝ} (hgap : ψ₂ < ψ₁)
    (hsmall : ψ₁ ≤ ψ₂ + 2 * ε) (hε8 : ε < 1 / 8) :
    (ψ₂ + ε) - (ψ₁ - ε) + 2 * ε < 1 := by
  linarith

/-- An object intrinsically confined around the larger phase lies in the
common midpoint heart. -/
theorem Slicing.mem_phaseShiftHeart_of_midpoint_left
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {ψ₁ ψ₂ ε : ℝ}
    (hlo : ψ₁ - ε ≤ s.phiMinus C E hE)
    (hhi : s.phiPlus C E hE ≤ ψ₁ + ε)
    (hgap : ψ₂ < ψ₁) (hsmall : ψ₁ ≤ ψ₂ + 2 * ε)
    (hε4 : ε < 1 / 4) :
    ((s.phaseShift C ((ψ₁ + ψ₂) / 2 - 1 / 2)).toTStructure C).heart E := by
  apply s.mem_phaseShiftHeart_of_intrinsic_bounds C hE
  · have : (ψ₁ + ψ₂) / 2 - 1 / 2 < ψ₁ - ε := by
      linarith
    exact this.trans_le hlo
  · have : ψ₁ + ε ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
      linarith
    exact hhi.trans this

/-- An object intrinsically confined around the smaller phase lies in the
same common midpoint heart. -/
theorem Slicing.mem_phaseShiftHeart_of_midpoint_right
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {ψ₁ ψ₂ ε : ℝ}
    (hlo : ψ₂ - ε ≤ s.phiMinus C E hE)
    (hhi : s.phiPlus C E hE ≤ ψ₂ + ε)
    (hgap : ψ₂ < ψ₁) (hsmall : ψ₁ ≤ ψ₂ + 2 * ε)
    (hε4 : ε < 1 / 4) :
    ((s.phaseShift C ((ψ₁ + ψ₂) / 2 - 1 / 2)).toTStructure C).heart E := by
  apply s.mem_phaseShiftHeart_of_intrinsic_bounds C hE
  · have : (ψ₁ + ψ₂) / 2 - 1 / 2 < ψ₂ - ε := by
      linarith
    exact this.trans_le hlo
  · have : ψ₂ + ε ≤ (ψ₁ + ψ₂) / 2 - 1 / 2 + 1 := by
      linarith
    exact hhi.trans this

end CategoryTheory.Triangulated
