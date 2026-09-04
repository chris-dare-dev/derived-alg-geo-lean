/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityCondition

/-!
# Uniform finite-length sectors for deformation theory

Local finiteness supplies one uniform interval around every phase. The
deformation argument uses rescaled radii so that both thin sectors of radius
`2 ε` and wide sectors of radius `4 ε` have finite length. This module
extracts those witnesses directly from the owner stability-condition data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Every owner interval of radius `2 ε` has finite length. -/
def SectorFiniteLength (σ : StabilityCondition.WithClassMap C v)
    (ε : ℝ) : Prop :=
  ∀ t : ℝ, ∀ E : σ.slicing.IntervalCat C (t - 2 * ε) (t + 2 * ε),
    σ.slicing.IsFiniteLength C E

/-- Every owner interval of radius `4 ε` has finite length. -/
def WideSectorFiniteLength (σ : StabilityCondition.WithClassMap C v)
    (ε : ℝ) : Prop :=
  ∀ t : ℝ, ∀ E : σ.slicing.IntervalCat C (t - 4 * ε) (t + 4 * ε),
    σ.slicing.IsFiniteLength C E

/-- Owner local finiteness yields a normalized wide deformation radius. -/
theorem exists_wideSectorRadius (σ : StabilityCondition.WithClassMap C v) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧ WideSectorFiniteLength C σ ε := by
  obtain ⟨η, hη, hη2, hfinite⟩ := σ.locallyFinite.intervalFinite
  refine ⟨η / 4, by positivity, by linarith, ?_⟩
  unfold WideSectorFiniteLength
  have hscale : 4 * (η / 4) = η := by ring
  rw [hscale]
  exact hfinite

/-- Owner local finiteness also yields the thin-sector radius used for the
first phase-perturbation construction. -/
theorem exists_sectorRadius (σ : StabilityCondition.WithClassMap C v) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ SectorFiniteLength C σ ε := by
  obtain ⟨η, hη, hη2, hfinite⟩ := σ.locallyFinite.intervalFinite
  refine ⟨η / 2, by positivity, by linarith, ?_⟩
  unfold SectorFiniteLength
  have hscale : 2 * (η / 2) = η := by ring
  rw [hscale]
  exact hfinite

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation
