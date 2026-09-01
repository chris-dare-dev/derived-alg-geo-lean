/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.DeformedSlicing
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.SlicingDistance
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Slicing.IntervalFiniteTransfer

/-!
# The repository-owned deformation theorem

This packages the deformed slicing with its perturbed central charge and
proves local finiteness by embedding each small deformed interval into a
uniformly finite old interval.
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

/-- A small interval for the deformed slicing lies in the corresponding
uniformly wide interval for the old slicing. -/
theorem deformed_intervalProp_subset_old_wide
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) (t : ℝ) :
    (σ.deformedSlicing C W hr0 hr1 hW hε₀ hε₀16 hWide
      hε hεhalf hε2 hε8 hsin).intervalProp C (t - ε₀) (t + ε₀) ≤
      σ.slicing.intervalProp C (t - 4 * ε₀) (t + 4 * ε₀) := by
  intro X hX
  rcases hX with hzero | ⟨G, hG⟩
  · exact Or.inl hzero
  · exact σ.slicing.intervalProp_of_postnikovTower C G.toPostnikovTower (fun j => by
      have hP := G.semistable j
      change σ.deformedPred C W hr0 hr1 hW ε (G.φ j) (G.factor j) at hP
      by_cases hj : IsZero (G.factor j)
      · exact Or.inl hj
      · obtain ⟨hminus, hplus⟩ := σ.deformedPred_intrinsic_bounds C W
          hr0 hr1 hW hε hε2 hsin hP hj
        exact σ.slicing.intervalProp_of_intrinsic_phases C hj
          (by linarith [(hG j).1]) (by linarith [(hG j).2]))

/-- The repository-owned deformed slicing is locally finite. -/
theorem deformedSlicing_isLocallyFinite
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    (σ.deformedSlicing C W hr0 hr1 hW hε₀ hε₀16 hWide
      hε hεhalf hε2 hε8 hsin).IsLocallyFinite C := by
  let Q := σ.deformedSlicing C W hr0 hr1 hW hε₀ hε₀16 hWide
    hε hεhalf hε2 hε8 hsin
  apply Slicing.IsLocallyFinite.of_strictFiniteLength C Q hε₀ (by linarith)
  intro t
  letI : Fact (t - ε₀ < t + ε₀) := ⟨by linarith⟩
  letI : Fact ((t + ε₀) - (t - ε₀) ≤ 1) := ⟨by linarith⟩
  letI : Fact (t - 4 * ε₀ < t + 4 * ε₀) := ⟨by linarith⟩
  letI : Fact ((t + 4 * ε₀) - (t - 4 * ε₀) ≤ 1) := ⟨by linarith⟩
  intro E
  have hIncl : Q.intervalProp C (t - ε₀) (t + ε₀) ≤
      σ.slicing.intervalProp C (t - 4 * ε₀) (t + 4 * ε₀) :=
    σ.deformed_intervalProp_subset_old_wide C W hr0 hr1 hW
      hε₀ hε₀16 hWide hε hεhalf hε2 hε8 hsin t
  exact interval_strictFiniteLength_of_inclusion C hIncl (fun Y =>
    Slicing.IntervalCat.isStrictFiniteLength_of_isFiniteLength C (hWide t Y)) E

/-- The canonical stability condition with perturbed central charge and the
repository-owned deformed slicing. -/
def deformed
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    StabilityCondition.WithClassMap C κ where
  toWithClassMap := PreStabilityCondition.WithClassMap.ofStrict
    (σ.deformedSlicing C W hr0 hr1 hW hε₀ hε₀16 hWide
      hε hεhalf hε2 hε8 hsin)
    W
    (fun ψ E hP hE => ⟨‖W (classOf C κ E)‖,
      norm_pos_iff.mpr (σ.deformedPred_charge_ne C W hr0 hr1 hW hP hE),
      σ.deformedPred_charge_polar C W hr0 hr1 hW hP hE⟩)
  locallyFinite := σ.deformedSlicing_isLocallyFinite C W hr0 hr1 hW
    hε₀ hε₀16 hWide hε hεhalf hε2 hε8 hsin

@[simp]
theorem deformed_Z
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    (σ.deformed C W hr0 hr1 hW hε₀ hε₀16 hWide
      hε hεhalf hε2 hε8 hsin).Z = W := rfl

/-- The canonical deformed slicing is at distance at most the deformation
radius from the original slicing. -/
theorem slicingDist_deformed_le
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    slicingDist C σ.slicing
      (σ.deformed C W hr0 hr1 hW hε₀ hε₀16 hWide
        hε hεhalf hε2 hε8 hsin).slicing ≤ ENNReal.ofReal ε := by
  let Q := σ.deformedSlicing C W hr0 hr1 hW hε₀ hε₀16 hWide
    hε hεhalf hε2 hε8 hsin
  have forward : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
      σ.slicing.intervalProp C
        (Q.phiMinus C E hE - ε - δ) (Q.phiPlus C E hE + ε + δ) E := by
    intro E hE δ hδ
    obtain ⟨G, hnG, hfirstG, hlastG⟩ := Q.exists_hn_nonzero_boundaries C hE
    apply σ.slicing.intervalProp_of_postnikovTower C G.toPostnikovTower
    intro i
    by_cases hi : IsZero (G.factor i)
    · exact Or.inl hi
    · have hsem := G.semistable i
      change σ.deformedPred C W hr0 hr1 hW ε (G.φ i) (G.factor i) at hsem
      obtain ⟨hlo, hhi⟩ := σ.deformedPred_intrinsic_bounds C W
        hr0 hr1 hW hε hε2 hsin hsem hi
      have hphaseLo : Q.phiMinus C E hE ≤ G.φ i := by
        rw [Q.phiMinus_eq C E hE G hnG hlastG]
        exact G.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
      have hphaseHi : G.φ i ≤ Q.phiPlus C E hE := by
        rw [Q.phiPlus_eq C E hE G hnG hfirstG]
        exact G.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
      exact σ.slicing.intervalProp_of_intrinsic_phases C hi
        (by linarith) (by linarith)
  have reverse : ∀ (E : C) (hE : ¬IsZero E) (δ : ℝ), 0 < δ →
      Q.intervalProp C
        (σ.slicing.phiMinus C E hE - ε - δ)
        (σ.slicing.phiPlus C E hE + ε + δ) E := by
    intro E hE δ hδ
    obtain ⟨F, hnF, hfirstF, hlastF⟩ :=
      σ.slicing.exists_hn_nonzero_boundaries C hE
    apply Q.intervalProp_of_postnikovTower C F.toPostnikovTower
    intro i
    by_cases hi : IsZero (F.factor i)
    · exact Or.inl hi
    · obtain ⟨G, hG, -⟩ := σ.semistable_has_tight_deformedHN C W
        hr0 hr1 hW (by linarith) hWide hε (by linarith)
        hε2 hε8 hsin (F.semistable i) hi
      refine Or.inr ⟨G, fun j => ⟨?_, ?_⟩⟩
      · have hphaseLo : σ.slicing.phiMinus C E hE ≤ F.φ i := by
          rw [σ.slicing.phiMinus_eq C E hE F hnF hlastF]
          exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
        linarith [(hG j).1]
      · have hphaseHi : F.φ i ≤ σ.slicing.phiPlus C E hE := by
          rw [σ.slicing.phiPlus_eq C E hE F hnF hfirstF]
          exact F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le i.val))
        linarith [(hG j).2]
  change slicingDist C σ.slicing Q ≤ ENNReal.ofReal ε
  apply slicingDist_le_of_phase_bounds C
  · intro E hE
    rw [abs_le]
    constructor
    · by_contra h
      push Not at h
      have hbound := Q.phiPlus_lt_of_intervalProp C hE
        (reverse E hE _ (by linarith :
          (0 : ℝ) < Q.phiPlus C E hE - σ.slicing.phiPlus C E hE - ε))
      linarith
    · by_contra h
      push Not at h
      have hbound := σ.slicing.phiPlus_lt_of_intervalProp C hE
        (forward E hE _ (by linarith :
          (0 : ℝ) < σ.slicing.phiPlus C E hE - Q.phiPlus C E hE - ε))
      linarith
  · intro E hE
    rw [abs_le]
    constructor
    · by_contra h
      push Not at h
      have hbound := σ.slicing.phiMinus_gt_of_intervalProp C hE
        (forward E hE _ (by linarith :
          (0 : ℝ) < Q.phiMinus C E hE - σ.slicing.phiMinus C E hE - ε))
      linarith
    · by_contra h
      push Not at h
      have hbound := Q.phiMinus_gt_of_intervalProp C hE
        (reverse E hE _ (by linarith :
          (0 : ℝ) < σ.slicing.phiMinus C E hE - Q.phiMinus C E hE - ε))
      linarith

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
