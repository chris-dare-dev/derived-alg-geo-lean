/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.StabilityTopology
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.Theorem

/-!
# Local central-charge lifts

The deformation theorem constructs a stability condition with a prescribed
nearby central charge. This file puts that construction into the topology on
the stability space: using a slightly smaller deformation radius places the
result in any specified larger basic neighborhood.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

/-- A charge satisfying the deformation estimate at radius `δ` lifts to a
stability condition in every larger basic neighborhood of radius `ε`.

The returned point is the canonical repository-owned deformation, so the
central-charge equality is definitional. -/
theorem exists_with_Z_mem_basisNhd
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {δ ε : ℝ} (hδ : 0 < δ) (hδhalf : δ < ε₀ / 2)
    (hδ2 : δ ≤ 1 / 2) (hδ8 : δ < 1 / 8)
    (hδε : δ < ε) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * δ))) :
    ∃ τ : StabilityCondition.WithClassMap C κ,
      τ.Z = W ∧ τ ∈ basisNhd C σ ε := by
  let τ := σ.deformed C W hr0 hr1 hW hε₀ hε₀16 hWide
    hδ hδhalf hδ2 hδ8 hsin
  refine ⟨τ, rfl, ?_⟩
  rw [mem_basisNhd_iff]
  constructor
  · have hsin_le : Real.sin (Real.pi * δ) ≤ Real.sin (Real.pi * ε) := by
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
      · gcongr
    exact lt_of_lt_of_le hsin (ENNReal.ofReal_le_ofReal hsin_le)
  · have hdist := σ.slicingDist_deformed_le C W hr0 hr1 hW
      hε₀ hε₀16 hWide hδ hδhalf hδ2 hδ8 hsin
    exact lt_of_le_of_lt hdist
      ((ENNReal.ofReal_lt_ofReal_iff (lt_trans hδ hδε)).2 hδε)

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
