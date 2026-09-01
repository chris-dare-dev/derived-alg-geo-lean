/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Basic.ChargeRay
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.Slope

/-!
# The source slope cutoff of display (14.1)

The phase-cut torsion pair is convenient for slicing arguments, while display
(14.1) of arXiv:1902.08184v4 is parametrized by a finite weak slope
`b : ℝ`.  This module supplies the exact adapter.

The normalized phase of the cutoff is

`slopeCutPhase b = arctan b / pi + 1 / 2`.

For a nonzero heart object, `muPlus` and `muMinus` are the slopes of the
nonzero endpoint factors of a slicing HN filtration.  Their normalized phases
are the intrinsic slicing endpoints `phiPlus` and `phiMinus`; consequently
the paper's classes `{muMinus > b}` and `{muPlus <= b}` are exactly
`P((slopeCutPhase b, 1])` and `P((0, slopeCutPhase b])`.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex
open CategoryTheory.Triangulated.Tilting

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type*} [AddCommGroup Λ]
variable {v : K₀ C →+ Λ}

namespace WeakPreStabilityCondition

/-- On a nonzero slicing-semistable heart object, the normalized weak slope
recovers its slicing phase, including the phase-`1` boundary. -/
theorem weakStabilityFunctionOnHeart_phase_eq_of_mem_P_phi
    (sigma : WeakPreStabilityCondition v) {phi : ℝ}
    (hphi : phi ∈ Set.Ioc (0 : ℝ) 1) (E : C)
    (hP : sigma.slicing.P phi E) (hE : ¬IsZero E) :
    sigma.weakStabilityFunctionOnHeart.phase E = phi := by
  let W := sigma.weakStabilityFunctionOnHeart
  by_cases hone : phi = 1
  · subst phi
    rw [WeakStabilityFunction.phase,
      sigma.slope_eq_top_of_mem_P_one E hP hE,
      weakPhaseOfSlope_top]
  · have hphi' : phi ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨hphi.1, lt_of_le_of_ne hphi.2 hone⟩
    have him := sigma.charge_im_pos_of_mem_P_phi_lt_one hphi' E hP hE
    obtain ⟨m, hm, hcharge⟩ :=
      complex_eq_pos_mul_exp_weakPhaseOfSlope (W.charge E) him
    have hcharge' : W.charge E = (m : ℂ) * Complex.exp
        ((Real.pi * W.phase E : ℂ) * Complex.I) := by
      simpa [WeakStabilityFunction.phase, W.slope_of_im_pos him] using hcharge
    have hWphase : W.phase E ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [WeakStabilityFunction.phase, W.slope_of_im_pos him]
      exact weakPhaseOfSlope_coe_mem_Ioo _
    have hargW : Complex.arg (W.charge E) = Real.pi * W.phase E := by
      rw [hcharge', Complex.arg_real_mul _ hm]
      have hexp : (Real.pi : ℂ) * (W.phase E : ℂ) * Complex.I =
          ((Real.pi * W.phase E : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [hexp, Complex.arg_exp_mul_I, toIocMod_eq_self]
      constructor <;> nlinarith [Real.pi_pos, hWphase.1, hWphase.2]
    have hargPhi :=
      sigma.charge_arg_eq_pi_mul_of_mem_P_phi_lt_one hphi' E hP hE
    rw [hargW] at hargPhi
    nlinarith [Real.pi_pos]

/-- A slicing HN filtration whose first and last factors are nonzero.  It is
used only to name the source extremal slopes; their phase normalizations are
proved independent of this choice below. -/
structure ExtremalHNData
    (sigma : WeakPreStabilityCondition v) (E : C) where
  /-- The chosen slicing HN filtration. -/
  filtration : HNFiltration C sigma.slicing.P E
  /-- The filtration has at least one factor. -/
  n_pos : 0 < filtration.n
  /-- Its largest-phase endpoint factor is nonzero. -/
  first_nonzero : ¬IsZero (filtration.triangle ⟨0, n_pos⟩).obj₃
  /-- Its smallest-phase endpoint factor is nonzero. -/
  last_nonzero : ¬IsZero
    (filtration.triangle ⟨filtration.n - 1, by have := n_pos; lia⟩).obj₃

/-- Choose an HN filtration with nonzero endpoint factors. -/
noncomputable def extremalHNData
    (sigma : WeakPreStabilityCondition v) (E : C) (hE : ¬IsZero E) :
    ExtremalHNData sigma E := by
  let hex := sigma.slicing.exists_hn_nonzero_boundaries C hE
  let F := Classical.choose hex
  let hn := Classical.choose (Classical.choose_spec hex)
  have hend := Classical.choose_spec (Classical.choose_spec hex)
  exact ⟨F, hn, hend.1, hend.2⟩

/-- The maximal HN slope `muPlus` of a nonzero heart object. -/
noncomputable def muPlus
    (sigma : WeakPreStabilityCondition v) (E : C) (hE : ¬IsZero E) :
    WithTop ℝ :=
  let H := sigma.extremalHNData E hE
  sigma.weakStabilityFunctionOnHeart.slope
    (H.filtration.triangle ⟨0, H.n_pos⟩).obj₃

/-- The minimal HN slope `muMinus` of a nonzero heart object. -/
noncomputable def muMinus
    (sigma : WeakPreStabilityCondition v) (E : C) (hE : ¬IsZero E) :
    WithTop ℝ :=
  let H := sigma.extremalHNData E hE
  sigma.weakStabilityFunctionOnHeart.slope
    (H.filtration.triangle
      ⟨H.filtration.n - 1, by have := H.n_pos; lia⟩).obj₃

/-- The normalized phase of `muPlus` is the intrinsic largest slicing
phase. -/
theorem weakPhaseOfSlope_muPlus
    (sigma : WeakPreStabilityCondition v) (E : C)
    (hheart : sigma.slicing.toTStructure.heart E) (hE : ¬IsZero E) :
    weakPhaseOfSlope (sigma.muPlus E hE) =
      sigma.slicing.phiPlus C E hE := by
  let H := sigma.extremalHNData E hE
  let j : Fin H.filtration.n := ⟨0, H.n_pos⟩
  have hbounds := (sigma.slicing.toTStructure_heart_iff C E).mp hheart
  have hplus : sigma.slicing.phiPlus C E hE = H.filtration.φ j :=
    sigma.slicing.phiPlus_eq C E hE H.filtration H.n_pos H.first_nonzero
  have hphi : H.filtration.φ j ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · calc
        0 < sigma.slicing.phiMinus C E hE :=
          sigma.slicing.phiMinus_gt_of_gtProp C hE hbounds.1
        _ ≤ sigma.slicing.phiPlus C E hE :=
          sigma.slicing.phiMinus_le_phiPlus C E hE
        _ = H.filtration.φ j := hplus
    · rw [← hplus]
      exact sigma.slicing.phiPlus_le_of_leProp C hE hbounds.2
  change sigma.weakStabilityFunctionOnHeart.phase
      (H.filtration.triangle j).obj₃ = sigma.slicing.phiPlus C E hE
  rw [hplus]
  exact sigma.weakStabilityFunctionOnHeart_phase_eq_of_mem_P_phi
    hphi _ (H.filtration.semistable j) H.first_nonzero

/-- The normalized phase of `muMinus` is the intrinsic smallest slicing
phase. -/
theorem weakPhaseOfSlope_muMinus
    (sigma : WeakPreStabilityCondition v) (E : C)
    (hheart : sigma.slicing.toTStructure.heart E) (hE : ¬IsZero E) :
    weakPhaseOfSlope (sigma.muMinus E hE) =
      sigma.slicing.phiMinus C E hE := by
  let H := sigma.extremalHNData E hE
  let j : Fin H.filtration.n :=
    ⟨H.filtration.n - 1, by have := H.n_pos; lia⟩
  have hbounds := (sigma.slicing.toTStructure_heart_iff C E).mp hheart
  have hminus : sigma.slicing.phiMinus C E hE = H.filtration.φ j :=
    sigma.slicing.phiMinus_eq C E hE H.filtration H.n_pos H.last_nonzero
  have hphi : H.filtration.φ j ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · rw [← hminus]
      exact sigma.slicing.phiMinus_gt_of_gtProp C hE hbounds.1
    · calc
        H.filtration.φ j = sigma.slicing.phiMinus C E hE := hminus.symm
        _ ≤ sigma.slicing.phiPlus C E hE :=
          sigma.slicing.phiMinus_le_phiPlus C E hE
        _ ≤ 1 := sigma.slicing.phiPlus_le_of_leProp C hE hbounds.2
  change sigma.weakStabilityFunctionOnHeart.phase
      (H.filtration.triangle j).obj₃ = sigma.slicing.phiMinus C E hE
  rw [hminus]
  exact sigma.weakStabilityFunctionOnHeart_phase_eq_of_mem_P_phi
    hphi _ (H.filtration.semistable j) H.last_nonzero

/-- Convert a finite weak-slope cutoff to the normalized phase interval. -/
noncomputable def slopeCutPhase (b : ℝ) : ℝ :=
  weakPhaseOfSlope (b : WithTop ℝ)

theorem slopeCutPhase_mem_Ioo (b : ℝ) :
    slopeCutPhase b ∈ Set.Ioo (0 : ℝ) 1 :=
  weakPhaseOfSlope_coe_mem_Ioo b

/-- The source inequality `muMinus(E) > b` is the strict lower phase
bound at `slopeCutPhase b`. -/
theorem muMinus_gt_iff_phiMinus_gt
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C)
    (hheart : sigma.slicing.toTStructure.heart E) (hE : ¬IsZero E) :
    (b : WithTop ℝ) < sigma.muMinus E hE ↔
      slopeCutPhase b < sigma.slicing.phiMinus C E hE := by
  rw [← sigma.weakPhaseOfSlope_muMinus E hheart hE,
    slopeCutPhase, weakPhaseOfSlope_lt_iff]

/-- The source inequality `muPlus(E) <= b` is the upper phase bound at
`slopeCutPhase b`. -/
theorem muPlus_le_iff_phiPlus_le
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C)
    (hheart : sigma.slicing.toTStructure.heart E) (hE : ¬IsZero E) :
    sigma.muPlus E hE ≤ (b : WithTop ℝ) ↔
      sigma.slicing.phiPlus C E hE ≤ slopeCutPhase b := by
  rw [← sigma.weakPhaseOfSlope_muPlus E hheart hE, slopeCutPhase]
  exact weakPhaseOfSlope_strictMono.le_iff_le.symm

/-- The source torsion class `{E | muMinus(E) > b}`. -/
def slopeTors
    (sigma : WeakPreStabilityCondition v) (b : ℝ) : ObjectProperty C :=
  fun E => IsZero E ∨ ∃ hE : ¬IsZero E,
    sigma.slicing.toTStructure.heart E ∧
      (b : WithTop ℝ) < sigma.muMinus E hE

/-- The source torsion-free class `{E | muPlus(E) <= b}`. -/
def slopeFree
    (sigma : WeakPreStabilityCondition v) (b : ℝ) : ObjectProperty C :=
  fun E => IsZero E ∨ ∃ hE : ¬IsZero E,
    sigma.slicing.toTStructure.heart E ∧
      sigma.muPlus E hE ≤ (b : WithTop ℝ)

theorem slopeTors_iff_phaseTors
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    sigma.slopeTors b E ↔ phaseTors sigma.slicing (slopeCutPhase b) E := by
  let theta := slopeCutPhase b
  have htheta := slopeCutPhase_mem_Ioo b
  constructor
  · rintro (hE | ⟨hE, hheart, hmu⟩)
    · exact ⟨Or.inl hE, Or.inl hE⟩
    · have hbounds := (sigma.slicing.toTStructure_heart_iff C E).mp hheart
      have hphi : theta < sigma.slicing.phiMinus C E hE :=
        (sigma.muMinus_gt_iff_phiMinus_gt b E hheart hE).mp hmu
      exact ⟨sigma.slicing.gtProp_of_phiMinus_gt C hE hphi, hbounds.2⟩
  · intro hphase
    by_cases hE : IsZero E
    · exact Or.inl hE
    · right
      have hheart : sigma.slicing.toTStructure.heart E :=
        mem_heart_of_bounds sigma.slicing
          (sigma.slicing.gtProp_anti C htheta.1.le E hphase.1) hphase.2
      refine ⟨hE, hheart, ?_⟩
      apply (sigma.muMinus_gt_iff_phiMinus_gt b E hheart hE).mpr
      exact sigma.slicing.phiMinus_gt_of_gtProp C hE hphase.1

theorem slopeFree_iff_phaseFree
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (E : C) :
    sigma.slopeFree b E ↔ phaseFree sigma.slicing (slopeCutPhase b) E := by
  let theta := slopeCutPhase b
  have htheta := slopeCutPhase_mem_Ioo b
  constructor
  · rintro (hE | ⟨hE, hheart, hmu⟩)
    · exact ⟨Or.inl hE, Or.inl hE⟩
    · have hbounds := (sigma.slicing.toTStructure_heart_iff C E).mp hheart
      have hphi : sigma.slicing.phiPlus C E hE ≤ theta :=
        (sigma.muPlus_le_iff_phiPlus_le b E hheart hE).mp hmu
      exact ⟨hbounds.1, sigma.slicing.leProp_of_phiPlus_le C hE hphi⟩
  · intro hphase
    by_cases hE : IsZero E
    · exact Or.inl hE
    · right
      have hheart : sigma.slicing.toTStructure.heart E :=
        mem_heart_of_bounds sigma.slicing hphase.1
          (sigma.slicing.leProp_mono C htheta.2.le E hphase.2)
      refine ⟨hE, hheart, ?_⟩
      apply (sigma.muPlus_le_iff_phiPlus_le b E hheart hE).mpr
      exact sigma.slicing.phiPlus_le_of_leProp C hE hphase.2

/-- The torsion pair of display (14.1), parametrized by its real slope
cutoff. -/
noncomputable def slopeTorsionPair
    (sigma : WeakPreStabilityCondition v) (b : ℝ) :
    HeartTorsionPair sigma.slicing.toTStructure :=
  slicingTorsionPair sigma.slicing
    (slopeCutPhase_mem_Ioo b).1.le (slopeCutPhase_mem_Ioo b).2.le

@[simp]
theorem slopeTorsionPair_tors
    (sigma : WeakPreStabilityCondition v) (b : ℝ) :
    (sigma.slopeTorsionPair b).tors = sigma.slopeTors b := by
  funext E
  apply propext
  exact (sigma.slopeTors_iff_phaseTors b E).symm

@[simp]
theorem slopeTorsionPair_free
    (sigma : WeakPreStabilityCondition v) (b : ℝ) :
    (sigma.slopeTorsionPair b).free = sigma.slopeFree b := by
  funext E
  apply propext
  exact (sigma.slopeFree_iff_phaseFree b E).symm

/-- The exact source-slope version of the tilted-heart identification in
display (14.1). -/
theorem slopeTilt_heart_iff
    (sigma : WeakPreStabilityCondition v) (b : ℝ) (X : C) :
    ((sigma.slopeTorsionPair b).tilt).heart X ↔
      ∃ (F T : C) (_ : sigma.slopeFree b F) (_ : sigma.slopeTors b T)
        (f : F⟦(1 : ℤ)⟧ ⟶ X) (g : X ⟶ T)
        (d : T ⟶ F⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
        Triangle.mk f g d ∈ distTriang C := by
  let theta := slopeCutPhase b
  have htheta := slopeCutPhase_mem_Ioo b
  constructor
  · intro hX
    obtain ⟨F, T, hF, hT, f, g, d, hdist⟩ :=
      (slicingTilt_heart_iff sigma.slicing htheta.1.le htheta.2.le X).mp
        (by simpa [slopeTorsionPair, theta] using hX)
    exact ⟨F, T, (sigma.slopeFree_iff_phaseFree b F).mpr hF,
      (sigma.slopeTors_iff_phaseTors b T).mpr hT, f, g, d, hdist⟩
  · rintro ⟨F, T, hF, hT, f, g, d, hdist⟩
    have hX :=
      (slicingTilt_heart_iff sigma.slicing htheta.1.le htheta.2.le X).mpr
        ⟨F, T, (sigma.slopeFree_iff_phaseFree b F).mp hF,
          (sigma.slopeTors_iff_phaseTors b T).mp hT, f, g, d, hdist⟩
    simpa [slopeTorsionPair, theta] using hX

end WeakPreStabilityCondition

end

end CategoryTheory.Triangulated.WeakStabilityCondition
