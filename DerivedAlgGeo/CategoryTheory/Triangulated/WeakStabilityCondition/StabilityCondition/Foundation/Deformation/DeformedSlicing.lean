/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.GlobalHN

/-!
# The repository-owned deformed slicing

The owner deformed predicate is assembled into a slicing using the sharp Hom
vanishing, shift symmetry, and global HN theorem proved in the preceding
modules.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

/-- The slicing defined by the repository-owned deformed phase predicate. -/
def deformedSlicing
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) : Slicing C where
  P := σ.deformedPred C W hr0 hr1 hW ε
  closedUnderIso := fun ψ =>
    σ.deformedPred_isClosedUnderIsomorphisms C W hr0 hr1 hW ε ψ
  zero_mem := fun ψ =>
    σ.deformedPred_of_isZero C W hr0 hr1 hW ε ψ (isZero_zero C)
  shift_iff := fun ψ X => ⟨
    σ.deformedPred_shift_one C W hr0 hr1 hW,
    σ.deformedPred_of_shift_one C W hr0 hr1 hW⟩
  hom_vanishing := fun ψ₁ ψ₂ A B hgap hA hB f =>
    σ.hom_eq_zero_of_deformedPred C W hr0 hr1 hW
      hε hε2 hε8 hsin hA hB hgap f
  hn_exists := fun E => σ.deformedHN_exists C W hr0 hr1 hW
    hε₀ hε₀16 hWide hε hεhalf hε2 hε8 hsin E

@[simp]
theorem deformedSlicing_P
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) (ψ : ℝ) :
    (σ.deformedSlicing C W hr0 hr1 hW hε₀ hε₀16 hWide
      hε hεhalf hε2 hε8 hsin).P ψ =
      σ.deformedPred C W hr0 hr1 hW ε ψ := rfl

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
