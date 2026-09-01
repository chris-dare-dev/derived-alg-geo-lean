/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.DeformedPredicate
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.PhaseSum

/-!
# Phase control inside an owner deformed interval

The stability-seminorm estimate controls the perturbed phase of every old
semistable factor.  This module specializes that estimate to the midpoint
branch used by owner skewed stability data and records the interval forms
needed by phase-confinement and HN-assembly arguments.
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

/-- Thinness places every phase in `(a,b)` inside the midpoint branch used by
the owner skewed stability function. -/
theorem midpoint_branch_contains {a b φ ε : ℝ}
    (haφ : a < φ) (hφb : φ < b) (hε : 0 < ε)
    (hthin : b - a + 2 * ε < 1) :
    φ ∈ Set.Ioo ((a + b) / 2 - 1 / 2) ((a + b) / 2 + 1 / 2) := by
  constructor <;> linarith

namespace StabilityCondition.WithClassMap

/-- Every old nonzero semistable factor in a thin witness interval has its
perturbed phase within `ε` of its old phase. -/
theorem skewedPhase_sub_lt_of_stabilitySeminorm
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b φ ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (haφ : a < φ) (hφb : φ < b) :
    |(skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E - φ| < ε := by
  apply relativePhase_perturbation_of_stabilitySeminorm C σ W hP hE
  · exact midpoint_branch_contains haφ hφb hε hthin
  · exact hε
  · exact hε2
  · exact hsin

/-- Interval form of the owner factor phase-control estimate. -/
theorem skewedPhase_mem_interval_of_stabilitySeminorm
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b φ ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (haφ : a < φ) (hφb : φ < b) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
      Set.Ioo (φ - ε) (φ + ε) := by
  have h := σ.skewedPhase_sub_lt_of_stabilitySeminorm C W hr0 hr1 hW hab
    hε hε2 hthin hsin hP hE haφ hφb
  rw [abs_lt] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The thin-witness factor phase lies in the common branch based at the
lower endpoint. -/
theorem skewedPhase_mem_lower_branch
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b φ ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (haφ : a < φ) (hφb : φ < b) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
      Set.Ioo (a - ε) (a - ε + 1) := by
  have hphase := σ.skewedPhase_mem_interval_of_stabilitySeminorm C W hr0 hr1 hW
    hab hε hε2 hthin hsin hP hE haφ hφb
  rcases hphase with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- The thin-witness factor phase lies in the common branch based at the
upper endpoint. -/
theorem skewedPhase_mem_upper_branch
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b φ ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (haφ : a < φ) (hφb : φ < b) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
      Set.Ioo (b + ε - 1) (b + ε) := by
  have hphase := σ.skewedPhase_mem_interval_of_stabilitySeminorm C W hr0 hr1 hW
    hab hε hε2 hthin hsin hP hE haφ hφb
  rcases hphase with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- The perturbed charge of a nonzero object in a thin owner interval cannot
vanish. -/
theorem charge_ne_of_interval
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hI : σ.slicing.intervalProp C a b E) (hE : ¬IsZero E) :
    W (classOf C κ E) ≠ 0 := by
  have him : 0 < rotatedIm (W (classOf C κ E)) (a - ε) := by
    apply σ.slicing.rotatedIm_charge_pos_of_interval C W hI hE
    intro G φ hP hG haφ hφb
    have hphase := σ.skewedPhase_mem_lower_branch C W hr0 hr1 hW hab hε hε2
      hthin hsin hP hG haφ hφb
    exact rotatedIm_pos_of_relativePhase_gt
      ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).nonzero
        G φ haφ hφb hP hG)
      hphase.1 hphase.2
  intro hzero
  simp [hzero, rotatedIm] at him

/-- Phase control on old semistable factors lifts to every nonzero object in
the same thin owner interval. -/
theorem skewedPhase_mem_expanded_interval
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hI : σ.slicing.intervalProp C a b E) (hE : ¬IsZero E) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
      Set.Ioo (a - ε) (b + ε) := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  have hα : F.α = (a + b) / 2 := rfl
  have him_lower : 0 < rotatedIm (W (classOf C κ E)) (a - ε) := by
    apply σ.slicing.rotatedIm_charge_pos_of_interval C W hI hE
    intro G φ hP hG haφ hφb
    have hphase := σ.skewedPhase_mem_lower_branch C W hr0 hr1 hW hab hε hε2
      hthin hsin hP hG haφ hφb
    exact rotatedIm_pos_of_relativePhase_gt (F.nonzero G φ haφ hφb hP hG)
      hphase.1 hphase.2
  have hcharge : W (classOf C κ E) ≠ 0 :=
    σ.charge_ne_of_interval C W hr0 hr1 hW hab hε hε2 hthin hsin hI hE
  let pLower := relativePhase (W (classOf C κ E)) (a - ε)
  have hpLower_mem := relativePhase_mem_Ioc (W (classOf C κ E)) (a - ε)
  have hpLower_hi : pLower < a - ε + 1 := by
    by_contra h
    push Not at h
    have heq : pLower = a - ε + 1 := le_antisymm hpLower_mem.2 h
    have him_zero : rotatedIm (W (classOf C κ E)) (a - ε) = 0 := by
      rw [rotatedIm_eq_norm_mul_sin (W (classOf C κ E)) (a - ε) (a - ε),
        show relativePhase (W (classOf C κ E)) (a - ε) = pLower from rfl,
        heq]
      ring_nf
      simp
    linarith
  have hpLower_gt : a - ε < pLower :=
    relativePhase_gt_of_rotatedIm_pos him_lower ⟨hpLower_mem.1, hpLower_hi⟩
  have hpLower_branch : pLower ∈ Set.Ioc (F.α - 1) (F.α + 1) := by
    constructor
    · calc
        F.α - 1 < a - ε := by rw [hα]; linarith
        _ < pLower := hpLower_gt
    · calc
        pLower ≤ a - ε + 1 := hpLower_hi.le
        _ ≤ F.α + 1 := by rw [hα]; linarith
  have hlower : a - ε < F.phase E := by
    change a - ε < relativePhase (W (classOf C κ E)) F.α
    rw [← relativePhase_eq_of_mem hcharge (a - ε) F.α hpLower_branch]
    exact hpLower_gt
  have him_upper : rotatedIm (W (classOf C κ E)) (b + ε) < 0 := by
    apply σ.slicing.rotatedIm_charge_neg_of_interval C W hI hE
    intro G φ hP hG haφ hφb
    have hphase := σ.skewedPhase_mem_upper_branch C W hr0 hr1 hW hab hε hε2
      hthin hsin hP hG haφ hφb
    exact rotatedIm_neg_of_relativePhase_lt (F.nonzero G φ haφ hφb hP hG)
      hphase.1 hphase.2
  let pUpper := relativePhase (W (classOf C κ E)) (b + ε)
  have hpUpper_mem := relativePhase_mem_Ioc (W (classOf C κ E)) (b + ε)
  have hpUpper_hi : pUpper < b + ε + 1 := by
    by_contra h
    push Not at h
    have heq : pUpper = b + ε + 1 := le_antisymm hpUpper_mem.2 h
    have him_zero : rotatedIm (W (classOf C κ E)) (b + ε) = 0 := by
      rw [rotatedIm_eq_norm_mul_sin (W (classOf C κ E)) (b + ε) (b + ε),
        show relativePhase (W (classOf C κ E)) (b + ε) = pUpper from rfl,
        heq]
      ring_nf
      simp
    linarith
  have hpUpper_lt : pUpper < b + ε :=
    relativePhase_lt_of_rotatedIm_neg him_upper ⟨hpUpper_mem.1, hpUpper_hi⟩
  have hpUpper_branch : pUpper ∈ Set.Ioc (F.α - 1) (F.α + 1) := by
    constructor
    · calc
        F.α - 1 < b + ε - 1 := by rw [hα]; linarith
        _ < pUpper := hpUpper_mem.1
    · calc
        pUpper ≤ b + ε := hpUpper_lt.le
        _ ≤ F.α + 1 := by rw [hα]; linarith
  have hupper : F.phase E < b + ε := by
    change relativePhase (W (classOf C κ E)) F.α < b + ε
    rw [← relativePhase_eq_of_mem hcharge (b + ε) F.α hpUpper_branch]
    exact hpUpper_lt
  exact ⟨hlower, hupper⟩

/-- Two owner skewed functions built from the same perturbed charge select the
same phase whenever the charge is nonzero and one selected phase lies on the
other's branch. -/
theorem skewedPhase_eq_of_mem_branch
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) {E : C}
    (hcharge : W (classOf C κ E) ≠ 0)
    (hbranch :
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
        Set.Ioc
          ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hcd).α - 1)
          ((skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hcd).α + 1)) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E =
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hcd).phase E := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  let G := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hcd
  change relativePhase (W (classOf C κ E)) F.α =
    relativePhase (W (classOf C κ E)) G.α
  exact relativePhase_eq_of_mem hcharge F.α G.α hbranch

/-- Two owner skewed functions agree on a shared nonzero interval object when
the first interval's controlled phase window lies in the second branch. -/
theorem skewedPhase_eq_of_common_interval
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b c d ε : ℝ} (hab : a < b) (hcd : c < d)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hleft : (c + d) / 2 - 1 < a - ε)
    (hright : b + ε ≤ (c + d) / 2 + 1)
    {E : C} (hI : σ.slicing.intervalProp C a b E) (hE : ¬IsZero E) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E =
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hcd).phase E := by
  have hphase := σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab hε hε2
    hthin hsin hI hE
  apply σ.skewedPhase_eq_of_mem_branch C W hr0 hr1 hW hab hcd
    (σ.charge_ne_of_interval C W hr0 hr1 hW hab hε hε2 hthin hsin hI hE)
  change _ ∈ Set.Ioc ((c + d) / 2 - 1) ((c + d) / 2 + 1)
  exact ⟨hleft.trans hphase.1, hphase.2.le.trans hright⟩

/-- Perturbed semistability transports to a narrower interval presentation
when the source phase window lies in the target branch. -/
theorem skewedSemistable_of_subinterval
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b c d ε ψ : ℝ} (hab : a < b) (hcd : c < d)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hleft : (c + d) / 2 - 1 < a - ε)
    (hright : b + ε ≤ (c + d) / 2 + 1)
    (hmono : σ.slicing.intervalProp C c d ≤ σ.slicing.intervalProp C a b)
    {E : C}
    (hI : σ.slicing.intervalProp C c d E)
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
      E ψ) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hcd).IsSemistable
      E ψ := by
  apply hSS.ofCompatibleInterval hI hmono rfl
  · exact (σ.skewedPhase_eq_of_common_interval C W hr0 hr1 hW hab hcd hε hε2
      hthin hsin hleft hright hSS.interval hSS.nonzero).symm
  · intro K hK hKne
    exact (σ.skewedPhase_eq_of_common_interval C W hr0 hr1 hW hab hcd hε hε2
      hthin hsin hleft hright (hmono K hK) hKne).symm

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
