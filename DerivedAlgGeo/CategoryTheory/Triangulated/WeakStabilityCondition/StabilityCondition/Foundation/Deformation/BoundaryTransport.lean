/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.DeformedPhaseControl
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.BoundaryTruncation

/-!
# Boundary transport for owner skewed semistability

Boundary truncations detect when a skewed-semistable object already belongs
to a one-sided smaller target interval.  The owner semistability predicate
tests distinguished triangles directly, so no quasi-abelian strictness layer
is needed for these reductions.
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

omit [IsTriangulated C] in
/-- A thin interval object has phase in the unit branch centred at any
enveloped skewed-semistable phase. -/
theorem skewedPhase_mem_enveloped_branch
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε ψ : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (haψ : a + ε ≤ ψ) (hψb : ψ ≤ b - ε)
    {E : C} (hI : σ.slicing.intervalProp C a b E) (hE : ¬IsZero E) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
      Set.Ioo (ψ - 1) (ψ + 1) := by
  have hphase := σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab
    hε hε2 hthin hsin hI hE
  exact ⟨by linarith [hphase.1], by linarith [hphase.2]⟩

omit [IsTriangulated C] in
/-- A nonzero interval object supported at or above `ψ + ε` has skewed
phase above `ψ` whenever its selected phase lies on the same branch as
`ψ`.  This range-based form is what the highest-phase split recursion uses
before an enveloping interval has been established. -/
theorem skewedPhase_gt_of_geProp_of_phase_range
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε ψ : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hI : σ.slicing.intervalProp C a b E) (hE : ¬IsZero E)
    (hrange :
      (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
        Set.Ioo (ψ - 1) (ψ + 1))
    (hbranch : b + ε < ψ + 1)
    (hge : σ.slicing.geProp C (ψ + ε) E) :
    ψ < (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  obtain ⟨G, hn, hfirst, hlast⟩ :=
    σ.slicing.exists_hn_nonzero_boundaries C hE
  have him : 0 < rotatedIm (W (classOf C κ E)) ψ := by
    apply rotatedIm_charge_pos_of_hn C W G hn hfirst ψ
    intro i hi
    have haφ : a < G.φ i := by
      calc
        a < σ.slicing.phiMinus C E hE :=
          σ.slicing.phiMinus_gt_of_intervalProp C hE hI
        _ = G.phiMinus C hn := σ.slicing.phiMinus_eq C E hE G hn hlast
        _ ≤ G.φ i := (G.phase_mem_range C hn i).1
    have hφb : G.φ i < b := by
      calc
        G.φ i ≤ G.phiPlus C hn := (G.phase_mem_range C hn i).2
        _ = σ.slicing.phiPlus C E hE :=
          (σ.slicing.phiPlus_eq C E hE G hn hfirst).symm
        _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hE hI
    have hψφ : ψ + ε ≤ G.φ i := by
      calc
        ψ + ε ≤ σ.slicing.phiMinus C E hE :=
          σ.slicing.phiMinus_ge_of_geProp C hE hge
        _ = G.phiMinus C hn := σ.slicing.phiMinus_eq C E hE G hn hlast
        _ ≤ G.φ i := (G.phase_mem_range C hn i).1
    have hp := σ.skewedPhase_mem_interval_of_stabilitySeminorm C W hr0 hr1 hW
      hab hε hε2 hthin hsin (G.semistable i) hi haφ hφb
    apply rotatedIm_pos_of_relativePhase_gt
      (F.nonzero (G.factor i) (G.φ i) haφ hφb (G.semistable i) hi)
    · linarith [hp.1]
    · linarith [hp.2, hφb, hbranch]
  exact relativePhase_gt_of_rotatedIm_pos him hrange

omit [IsTriangulated C] in
/-- A nonzero thin interval object supported at or above `ψ + ε` has
skewed phase strictly above `ψ`. -/
theorem skewedPhase_gt_of_geProp
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε ψ : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (haψ : a + ε ≤ ψ) (hψb : ψ ≤ b - ε)
    {E : C} (hI : σ.slicing.intervalProp C a b E) (hE : ¬IsZero E)
    (hge : σ.slicing.geProp C (ψ + ε) E) :
    ψ < (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E := by
  exact σ.skewedPhase_gt_of_geProp_of_phase_range C W hr0 hr1 hW
    hab hε hε2 hthin hsin hI hE
    (σ.skewedPhase_mem_enveloped_branch C W hr0 hr1 hW hab hε hε2
      hthin hsin haψ hψb hI hE) (by linarith) hge

omit [IsTriangulated C] in
/-- A nonzero thin interval object supported at or below `ψ - ε` has
skewed phase strictly below `ψ`. -/
theorem skewedPhase_lt_of_leProp
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε ψ : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (haψ : a + ε ≤ ψ) (hψb : ψ ≤ b - ε)
    {E : C} (hI : σ.slicing.intervalProp C a b E) (hE : ¬IsZero E)
    (hle : σ.slicing.leProp C (ψ - ε) E) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E < ψ := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  obtain ⟨G, hn, hfirst, hlast⟩ :=
    σ.slicing.exists_hn_nonzero_boundaries C hE
  have him : rotatedIm (W (classOf C κ E)) ψ < 0 := by
    apply rotatedIm_charge_neg_of_hn C W G hn hfirst ψ
    intro i hi
    have haφ : a < G.φ i := by
      calc
        a < σ.slicing.phiMinus C E hE :=
          σ.slicing.phiMinus_gt_of_intervalProp C hE hI
        _ = G.phiMinus C hn := σ.slicing.phiMinus_eq C E hE G hn hlast
        _ ≤ G.φ i := (G.phase_mem_range C hn i).1
    have hφb : G.φ i < b := by
      calc
        G.φ i ≤ G.phiPlus C hn := (G.phase_mem_range C hn i).2
        _ = σ.slicing.phiPlus C E hE :=
          (σ.slicing.phiPlus_eq C E hE G hn hfirst).symm
        _ < b := σ.slicing.phiPlus_lt_of_intervalProp C hE hI
    have hφψ : G.φ i ≤ ψ - ε := by
      calc
        G.φ i ≤ G.phiPlus C hn := (G.phase_mem_range C hn i).2
        _ = σ.slicing.phiPlus C E hE :=
          (σ.slicing.phiPlus_eq C E hE G hn hfirst).symm
        _ ≤ ψ - ε := σ.slicing.phiPlus_le_of_leProp C hE hle
    have hp := σ.skewedPhase_mem_interval_of_stabilitySeminorm C W hr0 hr1 hW
      hab hε hε2 hthin hsin (G.semistable i) hi haφ hφb
    apply rotatedIm_neg_of_relativePhase_lt
      (F.nonzero (G.factor i) (G.φ i) haφ hφb (G.semistable i) hi)
    · linarith [hp.1]
    · linarith [hp.2]
  exact relativePhase_lt_of_rotatedIm_neg him
    (σ.skewedPhase_mem_enveloped_branch C W hr0 hr1 hW hab hε hε2
      hthin hsin haψ hψb hI hE)

/-- Skewed semistability excludes an upper-boundary piece above the recorded
phase, so the object belongs to the smaller upper target interval. -/
theorem intervalProp_of_skewedSemistable_upper_target
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b₁ b₂ ε ψ : ℝ} (hab₁ : a < b₁) (hab₂ : a < b₂)
    (hb : b₁ ≤ b₂) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b₂ - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (haψ : a + ε ≤ ψ) (hψb : ψ ≤ b₁ - ε)
    {E : C}
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab₂).IsSemistable
      E ψ) :
    σ.slicing.intervalProp C a b₁ E := by
  obtain ⟨X, Y, f, g, δ, hT, hXge, hYsmall⟩ :=
    σ.slicing.exists_upper_boundary_triangle C hab₁ hSS.interval
  have hb₁a : b₁ ≤ a + 1 := by linarith
  have hXI : σ.slicing.intervalProp C a b₂ X :=
    σ.slicing.intervalProp_of_upper_boundary_triangle C hab₁ hab₂ hb₁a
      hSS.interval hXge hYsmall hT
  have hYI : σ.slicing.intervalProp C a b₂ Y :=
    σ.slicing.intervalProp_mono C le_rfl hb Y hYsmall
  have hXzero : IsZero X := by
    by_contra hXne
    have hge : σ.slicing.geProp C (ψ + ε) X :=
      σ.slicing.geProp_anti C (by linarith) X hXge
    have hgt := σ.skewedPhase_gt_of_geProp C W hr0 hr1 hW hab₂ hε hε2
      hthin hsin haψ (hψb.trans (sub_le_sub_right hb ε)) hXI hXne hge
    have hle := hSS.phase_le_of_triangle hT hXI hYI hXne
    linarith
  exact σ.slicing.intervalProp_of_triangle C (Or.inl hXzero) hYsmall hT

/-- Skewed semistability excludes a lower-boundary quotient below the
recorded phase, so the object belongs to the smaller lower target interval. -/
theorem intervalProp_of_skewedSemistable_lower_target
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a₁ a₂ b ε ψ : ℝ} (ha₁ : a₁ < b) (ha₂ : a₂ < b)
    (ha : a₁ ≤ a₂) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a₁ + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (haψ : a₂ + ε ≤ ψ) (hψb : ψ ≤ b - ε)
    {E : C}
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW ha₁).IsSemistable
      E ψ) :
    σ.slicing.intervalProp C a₂ b E := by
  obtain ⟨X, Y, f, g, δ, hT, hXsmall, hYle⟩ :=
    σ.slicing.exists_lower_boundary_triangle C ha₂ hSS.interval
  have hXI : σ.slicing.intervalProp C a₁ b X :=
    σ.slicing.intervalProp_mono C ha le_rfl X hXsmall
  have hYI : σ.slicing.intervalProp C a₁ b Y :=
    σ.slicing.intervalProp_of_lower_boundary_triangle C ha₂ ha hSS.interval
      hXsmall hYle hT
  have hYzero : IsZero Y := by
    by_contra hYne
    have hle : σ.slicing.leProp C (ψ - ε) Y :=
      σ.slicing.leProp_mono C (by linarith) Y hYle
    have haψ' : a₁ + ε ≤ ψ := by linarith
    have hlt := σ.skewedPhase_lt_of_leProp C W hr0 hr1 hW ha₁ hε hε2
      hthin hsin haψ' hψb hYI hYne hle
    have hYcharge := σ.charge_ne_of_interval C W hr0 hr1 hW ha₁ hε hε2
      hthin hsin hYI hYne
    have hYrange := σ.skewedPhase_mem_enveloped_branch C W hr0 hr1 hW ha₁
      hε hε2 hthin hsin haψ' hψb hYI hYne
    have hXrange : ∀ _ : ¬IsZero X,
        (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW ha₁).phase X ∈
          Set.Ioc (ψ - 1) ψ := by
      intro hXne
      exact ⟨(σ.skewedPhase_mem_enveloped_branch C W hr0 hr1 hW ha₁
        hε hε2 hthin hsin haψ' hψb
        hXI hXne).1, hSS.phase_le_of_triangle hT hXI hYI hXne⟩
    have hq := hSS.phase_le_of_quotient_triangle hT hYcharge hYrange hXrange
    linarith
  exact σ.slicing.intervalProp_of_triangle C hXsmall (Or.inl hYzero) hT

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
