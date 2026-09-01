/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.StabilitySeminorm
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhaseBounds

/-!
# The owner deformed slicing predicate

This module defines the candidate phase slices associated to a controlled
perturbation of the central charge.  The predicate records the thin old phase
window on which perturbed semistability is witnessed; construction of its HN
filtrations is deliberately left to the subsequent assembly modules.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

/-- The candidate deformed slice of phase `ψ`.  A nonzero object belongs when
it is perturbed-semistable in a thin old interval which envelops `ψ` by the
deformation radius `ε`. -/
def deformedPred (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    (ε ψ : ℝ) : ObjectProperty C :=
  fun E => IsZero E ∨
    ∃ (a b : ℝ) (hab : a < b),
      b - a + 2 * ε < 1 ∧ a + ε ≤ ψ ∧ ψ ≤ b - ε ∧
        (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable E ψ

/-- Every zero object belongs to every owner deformed slice. -/
theorem deformedPred_of_isZero (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    (ε ψ : ℝ) {E : C} (hE : IsZero E) :
    σ.deformedPred C W hr0 hr1 hW ε ψ E :=
  Or.inl hE

/-- The owner deformed slice is invariant under isomorphism. -/
theorem deformedPred_isClosedUnderIsomorphisms
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    (ε ψ : ℝ) :
    (σ.deformedPred C W hr0 hr1 hW ε ψ).IsClosedUnderIsomorphisms where
  of_iso e hE := by
    rcases hE with hzero | ⟨a, b, hab, hthin, hlo, hhi, hSS⟩
    · exact Or.inl ((Iso.isZero_iff e).mp hzero)
    · exact Or.inr ⟨a, b, hab, hthin, hlo, hhi, hSS.ofIso e⟩

/-- A nonzero member of an owner deformed slice exposes its thin interval
witness and perturbed-semistability proof. -/
theorem exists_deformedPred_witness
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} {E : C} (h : σ.deformedPred C W hr0 hr1 hW ε ψ E)
    (hE : ¬IsZero E) :
    ∃ (a b : ℝ) (hab : a < b),
      b - a + 2 * ε < 1 ∧ a + ε ≤ ψ ∧ ψ ≤ b - ε ∧
        (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable E ψ := by
  exact h.resolve_left hE

/-- The perturbed charge of a nonzero owner deformed-slice object does not
vanish. -/
theorem deformedPred_charge_ne
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} {E : C} (h : σ.deformedPred C W hr0 hr1 hW ε ψ E)
    (hE : ¬IsZero E) : W (classOf C κ E) ≠ 0 := by
  obtain ⟨a, b, hab, _, _, _, hSS⟩ :=
    σ.exists_deformedPred_witness C W hr0 hr1 hW h hE
  exact hSS.charge_ne

/-- The perturbed charge of a nonzero deformed-slice object lies on the ray
of its recorded phase. -/
theorem deformedPred_charge_polar
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} {E : C} (h : σ.deformedPred C W hr0 hr1 hW ε ψ E)
    (hE : ¬IsZero E) :
    W (classOf C κ E) = (‖W (classOf C κ E)‖ : ℂ) *
      Complex.exp (↑(Real.pi * ψ) * Complex.I) := by
  obtain ⟨a, b, hab, _, _, _, hSS⟩ :=
    σ.exists_deformedPred_witness C W hr0 hr1 hW h hE
  exact hSS.charge_polar

/-- A nonzero deformed-slice object belongs to an old thin interval whose
endpoints both envelop the new phase. -/
theorem deformedPred_intrinsic_phase_window
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} {E : C} (h : σ.deformedPred C W hr0 hr1 hW ε ψ E)
    (hE : ¬IsZero E) :
    ∃ a b : ℝ, b - a + 2 * ε < 1 ∧ a + ε ≤ ψ ∧ ψ ≤ b - ε ∧
      a < σ.slicing.phiMinus C E hE ∧ σ.slicing.phiPlus C E hE < b := by
  obtain ⟨a, b, hab, hthin, hlo, hhi, hSS⟩ :=
    σ.exists_deformedPred_witness C W hr0 hr1 hW h hE
  exact ⟨a, b, hthin, hlo, hhi,
    σ.slicing.phiMinus_gt_of_intervalProp C hE hSS.interval,
    σ.slicing.phiPlus_lt_of_intervalProp C hE hSS.interval⟩

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
