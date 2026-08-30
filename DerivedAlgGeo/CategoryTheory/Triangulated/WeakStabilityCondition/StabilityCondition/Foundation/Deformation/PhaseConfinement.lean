/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.DeformedPhaseControl
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.DeformedCuts
import DerivedAlgGeo.CategoryTheory.Triangulated.ExtensionClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.CutoffTruncation

/-!
# Owner phase confinement for perturbed semistable objects

Cutoff triangles inside a thin old phase interval, together with rotated-charge
signs, confine the intrinsic old phases of a perturbed-semistable object.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

/-- The intrinsic highest old phase of an owner perturbed-semistable object
is at most its perturbed phase plus the deformation radius. -/
theorem skewed_phiPlus_le
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε ψ : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C}
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
      E ψ) :
    σ.slicing.phiPlus C E hSS.nonzero ≤ ψ + ε := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  have hphase := σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab
    hε hε2 hthin hsin hSS.interval hSS.nonzero
  rw [hSS.phase_eq] at hphase
  by_contra hbound
  push Not at hbound
  obtain ⟨G, hG⟩ := hSS.interval.resolve_left hSS.nonzero
  have hat : a ≤ ψ + ε := by linarith [hphase.1]
  have htb : ψ + ε < b := hbound.trans
    (σ.slicing.phiPlus_lt_of_intervalProp C hSS.nonzero hSS.interval)
  obtain ⟨X, Y, hX, hY, hXI, hYI, f, g, δ, hT⟩ :=
    σ.slicing.exists_cutoff_truncation_in_interval C G hSS.interval hat htb
  have hXne : ¬IsZero X := by
    intro hzero
    have hEle : σ.slicing.leProp C (ψ + ε) E :=
      σ.slicing.leProp_of_triangle C (ψ + ε) (Or.inl hzero) hY hT
    exact (not_lt_of_ge (σ.slicing.phiPlus_le_of_leProp C hSS.nonzero hEle)) hbound
  have himX : 0 < rotatedIm (W (classOf C κ X)) ψ := by
    obtain ⟨GX, hn, hfirst, hlast⟩ :=
      σ.slicing.exists_hn_nonzero_boundaries C hXne
    apply rotatedIm_charge_pos_of_hn C W GX hn hfirst ψ
    intro i hi
    have haφ : a < GX.φ i := by
      calc
        a < σ.slicing.phiMinus C X hXne :=
          σ.slicing.phiMinus_gt_of_intervalProp C hXne hXI
        _ = GX.phiMinus C hn := σ.slicing.phiMinus_eq C X hXne GX hn hlast
        _ ≤ GX.φ i := (GX.phase_mem_range C hn i).1
    have hφb : GX.φ i < b := by
      calc
        GX.φ i ≤ GX.phiPlus C hn := (GX.phase_mem_range C hn i).2
        _ = σ.slicing.phiPlus C X hXne :=
          (σ.slicing.phiPlus_eq C X hXne GX hn hfirst).symm
        _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hXne hXI
    have htφ : ψ + ε < GX.φ i := by
      calc
        ψ + ε < σ.slicing.phiMinus C X hXne :=
          σ.slicing.phiMinus_gt_of_gtProp C hXne hX
        _ = GX.phiMinus C hn := σ.slicing.phiMinus_eq C X hXne GX hn hlast
        _ ≤ GX.φ i := (GX.phase_mem_range C hn i).1
    have hp := σ.skewedPhase_mem_interval_of_stabilitySeminorm C W hr0 hr1 hW
      hab hε hε2 hthin hsin (GX.semistable i) hi haφ hφb
    apply rotatedIm_pos_of_relativePhase_gt
      (F.nonzero (GX.factor i) (GX.φ i) haφ hφb (GX.semistable i) hi)
    · linarith [hp.1]
    · linarith [hp.2]
  have hphaseX := σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab hε hε2
    hthin hsin hXI hXne
  change relativePhase (W (classOf C κ X)) F.α ∈ Set.Ioo (a - ε) (b + ε)
    at hphaseX
  have hphaseXgt : ψ < F.phase X := by
    apply relativePhase_gt_of_rotatedIm_pos himX
    exact ⟨by linarith [hphaseX.1], by linarith [hphaseX.2]⟩
  have hphaseXle : F.phase X ≤ ψ :=
    hSS.phase_le_of_triangle hT hXI hYI hXne
  linarith

/-- The intrinsic lowest old phase of an owner perturbed-semistable object is
at least its perturbed phase minus the deformation radius. -/
theorem skewed_phiMinus_ge
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε ψ : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C}
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
      E ψ) :
    ψ - ε ≤ σ.slicing.phiMinus C E hSS.nonzero := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  have hphase := σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab
    hε hε2 hthin hsin hSS.interval hSS.nonzero
  rw [hSS.phase_eq] at hphase
  by_cases hlo : ψ - ε ≤ a
  · exact hlo.trans (le_of_lt
      (σ.slicing.phiMinus_gt_of_intervalProp C hSS.nonzero hSS.interval))
  have hat : a ≤ ψ - ε := le_of_not_ge hlo
  by_contra hbound
  push Not at hbound
  obtain ⟨G, hG⟩ := hSS.interval.resolve_left hSS.nonzero
  have htb : ψ - ε < b := by linarith [hphase.2]
  obtain ⟨X, Y, hX, hY, hXI, hYI, f, g, δ, hT⟩ :=
    σ.slicing.exists_cutoff_truncation_in_interval C G hSS.interval hat htb
  have hYne : ¬IsZero Y := by
    intro hzero
    have hEgt : σ.slicing.gtProp C (ψ - ε) E :=
      σ.slicing.gtProp_of_triangle C (ψ - ε) hX (Or.inl hzero) hT
    exact (not_lt_of_ge
      (σ.slicing.phiMinus_gt_of_gtProp C hSS.nonzero hEgt).le) hbound
  have himY : rotatedIm (W (classOf C κ Y)) ψ < 0 := by
    obtain ⟨GY, hn, hfirst, hlast⟩ :=
      σ.slicing.exists_hn_nonzero_boundaries C hYne
    apply rotatedIm_charge_neg_of_hn C W GY hn hfirst ψ
    intro i hi
    have haφ : a < GY.φ i := by
      calc
        a < σ.slicing.phiMinus C Y hYne :=
          σ.slicing.phiMinus_gt_of_intervalProp C hYne hYI
        _ = GY.phiMinus C hn := σ.slicing.phiMinus_eq C Y hYne GY hn hlast
        _ ≤ GY.φ i := (GY.phase_mem_range C hn i).1
    have hφb : GY.φ i < b := by
      calc
        GY.φ i ≤ GY.phiPlus C hn := (GY.phase_mem_range C hn i).2
        _ = σ.slicing.phiPlus C Y hYne :=
          (σ.slicing.phiPlus_eq C Y hYne GY hn hfirst).symm
        _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hYne hYI
    have hφt : GY.φ i ≤ ψ - ε := by
      calc
        GY.φ i ≤ GY.phiPlus C hn := (GY.phase_mem_range C hn i).2
        _ = σ.slicing.phiPlus C Y hYne :=
          (σ.slicing.phiPlus_eq C Y hYne GY hn hfirst).symm
        _ ≤ ψ - ε := σ.slicing.phiPlus_le_of_leProp C hYne hY
    have hp := σ.skewedPhase_mem_interval_of_stabilitySeminorm C W hr0 hr1 hW
      hab hε hε2 hthin hsin (GY.semistable i) hi haφ hφb
    apply rotatedIm_neg_of_relativePhase_lt
      (F.nonzero (GY.factor i) (GY.φ i) haφ hφb (GY.semistable i) hi)
    · linarith [hp.1]
    · linarith [hp.2]
  have himE : rotatedIm (W (classOf C κ E)) ψ = 0 := by
    apply rotatedIm_eq_zero_of_relativePhase_eq
    exact hSS.phase_eq
  have hclass : classOf C κ E = classOf C κ X + classOf C κ Y := by
    simpa only [Triangle.mk] using
      classOf_triangle C κ (Triangle.mk f g δ) hT
  have hchargeSum : W (classOf C κ E) =
      W (classOf C κ X) + W (classOf C κ Y) := by
    rw [hclass, map_add]
  have himSum : rotatedIm (W (classOf C κ E)) ψ =
      rotatedIm (W (classOf C κ X)) ψ +
        rotatedIm (W (classOf C κ Y)) ψ := by
    unfold rotatedIm
    rw [hchargeSum, add_mul, Complex.add_im]
  have himX : 0 < rotatedIm (W (classOf C κ X)) ψ := by linarith
  have hXne : ¬IsZero X := by
    intro hzero
    rw [classOf_isZero C κ hzero, map_zero] at himX
    simp [rotatedIm] at himX
  have hphaseX := σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab hε hε2
    hthin hsin hXI hXne
  change relativePhase (W (classOf C κ X)) F.α ∈ Set.Ioo (a - ε) (b + ε)
    at hphaseX
  have hphaseXgt : ψ < F.phase X := by
    apply relativePhase_gt_of_rotatedIm_pos himX
    exact ⟨by linarith [hphaseX.1], by linarith [hphaseX.2]⟩
  have hphaseXle : F.phase X ≤ ψ :=
    hSS.phase_le_of_triangle hT hXI hYI hXne
  linarith

/-- A nonzero owner deformed-slice object has both intrinsic old phase bounds
predicted by its phase and the deformation radius. -/
theorem deformedPred_intrinsic_bounds
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (h : σ.deformedPred C W hr0 hr1 hW ε ψ E)
    (hE : ¬IsZero E) :
    ψ - ε ≤ σ.slicing.phiMinus C E hE ∧
      σ.slicing.phiPlus C E hE ≤ ψ + ε := by
  obtain ⟨a, b, hab, hthin, haψ, hψb, hSS⟩ :=
    σ.exists_deformedPred_witness C W hr0 hr1 hW h hE
  exact ⟨σ.skewed_phiMinus_ge C W hr0 hr1 hW hab hε hε2 hthin hsin
      hSS,
    σ.skewed_phiPlus_le C W hr0 hr1 hW hab hε hε2 hthin hsin
      hSS⟩

/-- Every owner deformed-slice object lies above its weak old lower phase
cut. -/
theorem deformedPred_geProp
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    σ.deformedPred C W hr0 hr1 hW ε ψ ≤ σ.slicing.geProp C (ψ - ε) := by
  intro E h
  by_cases hE : IsZero E
  · exact Or.inl hE
  · exact σ.slicing.geProp_of_phiMinus_ge C hE
      (σ.deformedPred_intrinsic_bounds C W hr0 hr1 hW hε hε2 hsin h hE).1

/-- Every owner deformed-slice object lies below its weak old upper phase
cut. -/
theorem deformedPred_leProp
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    σ.deformedPred C W hr0 hr1 hW ε ψ ≤ σ.slicing.leProp C (ψ + ε) := by
  intro E h
  by_cases hE : IsZero E
  · exact Or.inl hE
  · exact σ.slicing.leProp_of_phiPlus_le C hE
      (σ.deformedPred_intrinsic_bounds C W hr0 hr1 hW hε hε2 hsin h hE).2

/-- Adding any positive padding turns weak confinement of an owner deformed
slice into membership in an open old phase interval. -/
theorem deformedPred_intervalProp
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ δ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) (hδ : 0 < δ) :
    σ.deformedPred C W hr0 hr1 hW ε ψ ≤
      σ.slicing.intervalProp C (ψ - ε - δ) (ψ + ε + δ) := by
  intro E h
  by_cases hE : IsZero E
  · exact Or.inl hE
  · obtain ⟨hminus, hplus⟩ :=
      σ.deformedPred_intrinsic_bounds C W hr0 hr1 hW hε hε2 hsin h hE
    exact σ.slicing.intervalProp_of_intrinsic_phases C hE
      (by linarith) (by linarith)

/-- An owner HN filtration by deformed slices inside a common phase window
places its ambient object in the corresponding padded old phase interval. -/
theorem intervalProp_of_deformed_hn
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε a b δ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) (hδ : 0 < δ)
    {E : C} (G : HNFiltration C
      (σ.deformedPred C W hr0 hr1 hW ε) E)
    (hphase : ∀ i : Fin G.n, a ≤ G.φ i ∧ G.φ i ≤ b) :
    σ.slicing.intervalProp C (a - ε - δ) (b + ε + δ) E := by
  have hfactors : ∀ i : Fin G.n,
      σ.slicing.intervalProp C (a - ε - δ) (b + ε + δ) (G.factor i) := by
    intro i
    have hI := σ.deformedPred_intervalProp C W hr0 hr1 hW
      (ψ := G.φ i) hε hε2 hsin hδ (G.factor i) (G.semistable i)
    exact σ.slicing.intervalProp_mono C (by linarith [(hphase i).1])
      (by linarith [(hphase i).2]) _ hI
  let Q := σ.slicing.intervalProp C (a - ε - δ) (b + ε + δ)
  have hclosure : ExtensionClosure Q E :=
    ExtensionClosure.ofPostnikovTower (Q := Q) G.toPostnikovTower hfactors
  exact ExtensionClosure.le_of_closed (P := Q) (Q := Q)
    (fun hzero => Or.inl hzero)
    (fun X hX => hX)
    (fun hT hX hY => by
      change σ.slicing.intervalProp C (a - ε - δ) (b + ε + δ) _
      apply σ.slicing.intervalProp_of_gtProp_ltProp C
      · exact σ.slicing.gtProp_of_triangle C (a - ε - δ)
          (σ.slicing.gtProp_of_intervalProp C hX)
          (σ.slicing.gtProp_of_intervalProp C hY) hT
      · exact σ.slicing.ltProp_of_triangle C (b + ε + δ)
          (σ.slicing.ltProp_of_intervalProp C hX)
          (σ.slicing.ltProp_of_intervalProp C hY) hT)
    E hclosure

/-- The extension-closed owner cut `Q(>t)` lies above the old phase cutoff
`t-ε`. -/
theorem deformedGtPred_gtProp
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    σ.deformedGtPred C W hr0 hr1 hW ε t ≤ σ.slicing.gtProp C (t - ε) := by
  apply ExtensionClosure.le_of_closed
  · exact fun hzero => Or.inl hzero
  · intro E hE
    obtain ⟨ψ, htψ, hP⟩ := hE
    by_cases hzero : IsZero E
    · exact Or.inl hzero
    · apply σ.slicing.gtProp_of_phiMinus_gt C hzero
      have hbound :=
        (σ.deformedPred_intrinsic_bounds C W hr0 hr1 hW hε hε2 hsin hP hzero).1
      linarith
  · exact fun hT hX hY =>
      σ.slicing.gtProp_of_triangle C (t - ε) hX hY hT

/-- The extension-closed owner cut `Q(≤t)` lies below the old phase cutoff
`t+ε`. -/
theorem deformedLePred_leProp
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    σ.deformedLePred C W hr0 hr1 hW ε t ≤ σ.slicing.leProp C (t + ε) := by
  apply ExtensionClosure.le_of_closed
  · exact fun hzero => Or.inl hzero
  · intro E hE
    obtain ⟨ψ, hψt, hP⟩ := hE
    by_cases hzero : IsZero E
    · exact Or.inl hzero
    · apply σ.slicing.leProp_of_phiPlus_le C hzero
      have hbound :=
        (σ.deformedPred_intrinsic_bounds C W hr0 hr1 hW hε hε2 hsin hP hzero).2
      linarith
  · exact fun hT hX hY =>
      σ.slicing.leProp_of_triangle C (t + ε) hX hY hT

/-- The extension-closed owner cut `Q(<t)` lies strictly below the old phase
cutoff `t+ε`. -/
theorem deformedLtPred_ltProp
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε))) :
    σ.deformedLtPred C W hr0 hr1 hW ε t ≤ σ.slicing.ltProp C (t + ε) := by
  apply ExtensionClosure.le_of_closed
  · exact fun hzero => Or.inl hzero
  · intro E hE
    obtain ⟨ψ, hψt, hP⟩ := hE
    by_cases hzero : IsZero E
    · exact Or.inl hzero
    · apply σ.slicing.ltProp_of_phiPlus_lt C hzero
      have hbound :=
        (σ.deformedPred_intrinsic_bounds C W hr0 hr1 hW hε hε2 hsin hP hzero).2
      linarith
  · exact fun hT hX hY =>
      σ.slicing.ltProp_of_triangle C (t + ε) hX hY hT

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
