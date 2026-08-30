/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Action.Continuous
import Mathlib.Topology.Compactness.Compact

/-!
# Joint continuity of the lifted linear action

This file strengthens the fixed-element continuity proved in
`WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Action/Continuous.lean`.  The key estimates are local at the identity:

* `x.shift φ - φ` is uniformly small in `φ` when `x` is close to `1`;
  integer equivariance reduces this to the compact interval `[0, 1]`;
* `actCCLM x.mat - 1` is small in operator norm when `x` is close to `1`.

The general case follows from
`x • τ = x₀ • ((x₀⁻¹ * x) • τ)` and the already-proved continuity of
the action by the fixed element `x₀`.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-! ## Uniform phase displacement near the identity -/

/-- Jointly continuous phase displacement. -/
theorem GLTilde.continuous_shift_displacement :
    Continuous fun p : GLTilde × ℝ ↦ p.1.shift.toOrderIso p.2 - p.2 :=
  GLTilde.continuous_shift_apply.sub continuous_snd

/-- Close to the identity, the lifted phase map is uniformly close to the
identity map on all of `ℝ`. -/
theorem GLTilde.eventually_uniform_shift_displacement {a : ℝ} (ha : 0 < a) :
    Filter.Eventually
      (fun x : GLTilde ↦ ∀ φ : ℝ, |x.shift.toOrderIso φ - φ| < a)
      (nhds (1 : GLTilde)) := by
  let U : Set (GLTilde × ℝ) :=
    {p | |p.1.shift.toOrderIso p.2 - p.2| < a}
  have hU : U ∈ (nhds (1 : GLTilde)) ×ˢ (nhdsSet (Set.Icc (0 : ℝ) 1)) := by
    apply isCompact_Icc.mem_prod_nhdsSet_of_forall
    intro φ hφ
    rw [← nhds_prod_eq]
    have hcont : Continuous fun p : GLTilde × ℝ ↦
        |p.1.shift.toOrderIso p.2 - p.2| :=
      continuous_abs.comp GLTilde.continuous_shift_displacement
    have htarget : Set.Iio a ∈ nhds
        |(1 : GLTilde).shift.toOrderIso φ - φ| := by
      simpa using (Iio_mem_nhds ha : Set.Iio a ∈ nhds (0 : ℝ))
    change (fun p : GLTilde × ℝ ↦
      |p.1.shift.toOrderIso p.2 - p.2|) ⁻¹' Set.Iio a ∈ nhds ((1 : GLTilde), φ)
    exact hcont.continuousAt htarget
  obtain ⟨V, hV, W, hW, hVW⟩ := Filter.mem_prod_iff.mp hU
  apply Filter.mem_of_superset hV
  intro x hx φ
  have hcompact : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |x.shift.toOrderIso t - t| < a := by
    intro t ht
    have htW : t ∈ W := subset_of_mem_nhdsSet hW ht
    have hpair : (x, t) ∈ V ×ˢ W := ⟨hx, htW⟩
    exact hVW hpair
  let t : ℝ := Int.fract φ
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg φ, (Int.fract_lt_one φ).le⟩
  have hshift := NormalizedShift.map_add_int x.shift ⌊φ⌋ t
  have hφ : t + (⌊φ⌋ : ℝ) = φ := Int.fract_add_floor φ
  have hEq : x.shift.toOrderIso φ - φ = x.shift.toOrderIso t - t := by
    rw [← hφ, hshift]
    ring
  rw [hEq]
  exact hcompact t ht

variable [IsTriangulated C]

/-- Phase displacement of `x` plus the original slicing distance controls the
distance from `x • τ` back to the fixed slicing `σ`. -/
theorem slicingDist_smul_le_of_displacement (x : GLTilde)
    (σ τ : StabilityCondition.WithClassMap C v) {a d : ℝ}
    (hdisp : ∀ φ : ℝ, |x.shift.toOrderIso φ - φ| < a)
    (hdist : CategoryTheory.Triangulated.slicingDist C
      σ.slicing τ.slicing < ENNReal.ofReal d) :
    CategoryTheory.Triangulated.slicingDist C
      σ.slicing (x • τ).slicing ≤ ENNReal.ofReal (d + a) := by
  have hd : 0 < d := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hdist)
  apply CategoryTheory.Triangulated.slicingDist_le_of_phase_bounds
  · intro E hE
    change |σ.slicing.phiPlus C E hE -
      (relabel C x.shift τ.slicing).phiPlus C E hE| ≤ d + a
    rw [Slicing.relabel_phiPlus x.shift τ.slicing E hE]
    have hold := CategoryTheory.Triangulated.abs_phiPlus_sub_lt_of_slicingDist
      C σ.slicing τ.slicing hE hd hdist
    calc
      |σ.slicing.phiPlus C E hE -
          x.shift.toOrderIso (τ.slicing.phiPlus C E hE)| =
          |(σ.slicing.phiPlus C E hE - τ.slicing.phiPlus C E hE) -
            (x.shift.toOrderIso (τ.slicing.phiPlus C E hE) -
              τ.slicing.phiPlus C E hE)| := by
                congr 1
                all_goals ring
      _ ≤ |σ.slicing.phiPlus C E hE - τ.slicing.phiPlus C E hE| +
          |x.shift.toOrderIso (τ.slicing.phiPlus C E hE) -
            τ.slicing.phiPlus C E hE| := abs_sub _ _
      _ ≤ d + a := by
        have hold' : |σ.slicing.phiPlus C E hE - τ.slicing.phiPlus C E hE| < d := by
          simpa only [abs_sub_comm] using hold
        exact le_of_lt (add_lt_add hold' (hdisp (τ.slicing.phiPlus C E hE)))
  · intro E hE
    change |σ.slicing.phiMinus C E hE -
      (relabel C x.shift τ.slicing).phiMinus C E hE| ≤ d + a
    rw [Slicing.relabel_phiMinus x.shift τ.slicing E hE]
    have hOld := CategoryTheory.Triangulated.abs_phiMinus_sub_lt_of_slicingDist
      C σ.slicing τ.slicing hE hd hdist
    calc
      |σ.slicing.phiMinus C E hE -
          x.shift.toOrderIso (τ.slicing.phiMinus C E hE)| =
          |(σ.slicing.phiMinus C E hE - τ.slicing.phiMinus C E hE) -
            (x.shift.toOrderIso (τ.slicing.phiMinus C E hE) -
              τ.slicing.phiMinus C E hE)| := by
                congr 1
                all_goals ring
      _ ≤ |σ.slicing.phiMinus C E hE - τ.slicing.phiMinus C E hE| +
          |x.shift.toOrderIso (τ.slicing.phiMinus C E hE) -
            τ.slicing.phiMinus C E hE| := abs_sub _ _
      _ ≤ d + a := by
        have hOld' : |σ.slicing.phiMinus C E hE - τ.slicing.phiMinus C E hE| < d := by
          simpa only [abs_sub_comm] using hOld
        exact le_of_lt (add_lt_add hOld' (hdisp (τ.slicing.phiMinus C E hE)))

/-! ## Operator-norm control of the central charge -/

@[simp]
theorem actCCLM_one : actCCLM (1 : Matrix.GLPos (Fin 2) ℝ) =
    ContinuousLinearMap.id ℝ ℂ := by
  ext z
  simp

/-- The central-charge operator varies continuously in operator norm. -/
theorem GLTilde.continuous_actCCLM :
    Continuous fun x : GLTilde ↦ actCCLM x.mat := by
  rw [continuous_clm_apply]
  intro z
  simp only [actCCLM_apply, actC_apply]
  exact cplxCoord.symm.toLinearMap.continuous_of_finiteDimensional.comp <|
    (continuous_toMatGLPos.comp GLTilde.continuous_toMat).matrix_mulVec continuous_const

/-- The elementary pointwise estimate behind the stability-seminorm bound. -/
theorem norm_actC_sub_div_le (T : Matrix.GLPos (Fin 2) ℝ) (z w : ℂ) (hw : w ≠ 0) :
    ‖actC T (z + w) - w‖ / ‖w‖ ≤
      ‖actCCLM T‖ * (‖z‖ / ‖w‖) +
        ‖actCCLM T - ContinuousLinearMap.id ℝ ℂ‖ := by
  let L := actCCLM T
  let D := L - ContinuousLinearMap.id ℝ ℂ
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hdecomp : actC T (z + w) - w = L z + D w := by
    simp only [L, D, actCCLM_apply, map_add, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply]
    abel
  rw [hdecomp]
  calc
    ‖L z + D w‖ / ‖w‖ ≤ (‖L z‖ + ‖D w‖) / ‖w‖ := by
      gcongr
      exact norm_add_le _ _
    _ = ‖L z‖ / ‖w‖ + ‖D w‖ / ‖w‖ := add_div _ _ _
    _ ≤ (‖L‖ * ‖z‖) / ‖w‖ + (‖D‖ * ‖w‖) / ‖w‖ := by
      gcongr
      · exact L.le_opNorm z
      · exact D.le_opNorm w
    _ = ‖L‖ * (‖z‖ / ‖w‖) + ‖D‖ := by
      field_simp [ne_of_gt hw0]

/-- Simultaneously moving the group element away from the identity and the
stability condition away from `σ` gives this affine seminorm bound. -/
theorem stabSeminorm_near_identity_le (x : GLTilde)
    (σ τ : StabilityCondition.WithClassMap C v) :
    stabilitySeminorm C σ ((x • τ).Z - σ.Z) ≤
      ENNReal.ofReal ‖actCCLM x.mat‖ *
        stabilitySeminorm C σ (τ.Z - σ.Z) +
        ENNReal.ofReal
          ‖actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ‖ := by
  apply iSup_le
  intro E
  apply iSup_le
  intro φ
  apply iSup_le
  intro hP
  apply iSup_le
  intro hE
  have hcharge : σ.charge E ≠ 0 := by
    obtain ⟨m, hm, hZ⟩ := σ.compat φ E hP hE
    rw [hZ]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hm)) (Complex.exp_ne_zero _)
  have hnum : ((x • τ).Z - σ.Z) (classOf C v E) =
      actC x.mat (((τ.Z - σ.Z) (classOf C v E)) + σ.charge E) - σ.charge E := by
    change actC x.mat (τ.Z (classOf C v E)) - σ.Z (classOf C v E) =
      actC x.mat ((τ.Z (classOf C v E) - σ.Z (classOf C v E)) + σ.Z (classOf C v E)) -
        σ.Z (classOf C v E)
    ring_nf
  rw [hnum]
  calc
    ENNReal.ofReal
        (‖actC x.mat (((τ.Z - σ.Z) (classOf C v E)) + σ.charge E) - σ.charge E‖ /
          ‖σ.charge E‖)
        ≤ ENNReal.ofReal
          (‖actCCLM x.mat‖ *
              (‖(τ.Z - σ.Z) (classOf C v E)‖ / ‖σ.charge E‖) +
            ‖actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ‖) :=
      ENNReal.ofReal_le_ofReal (norm_actC_sub_div_le x.mat _ _ hcharge)
    _ = ENNReal.ofReal ‖actCCLM x.mat‖ *
          ENNReal.ofReal (‖(τ.Z - σ.Z) (classOf C v E)‖ / ‖σ.charge E‖) +
        ENNReal.ofReal
          ‖actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ‖ := by
      rw [ENNReal.ofReal_add
          (mul_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) (norm_nonneg _)))
          (norm_nonneg _),
        ENNReal.ofReal_mul (norm_nonneg _)]
    _ ≤ ENNReal.ofReal ‖actCCLM x.mat‖ *
        stabilitySeminorm C σ (τ.Z - σ.Z) +
        ENNReal.ofReal
          ‖actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ‖ := by
      apply add_le_add
      · apply mul_le_mul_right
        exact le_iSup_of_le E <| le_iSup_of_le φ <| le_iSup_of_le hP <|
          le_iSup_of_le hE le_rfl
      · exact le_rfl

/-! ## A uniform basic-neighborhood estimate at the identity -/

/-- For a fixed centre `σ`, group elements sufficiently close to `1` carry one
smaller basic neighborhood of `σ` into any prescribed basic neighborhood of
`σ`.  The source radius is independent of the nearby group element. -/
theorem exists_identity_basisNhd_control
    (σ : StabilityCondition.WithClassMap C v) {e : ℝ}
    (he : 0 < e) (he8 : e < 1 / 8) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 8 ∧
      ∀ᶠ x in nhds (1 : GLTilde),
        Set.MapsTo (fun τ ↦ x • τ)
          (basisNhd C σ d) (basisNhd C σ e) := by
  let S := Real.sin (Real.pi * e)
  have hS : 0 < S := by
    dsimp [S]
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  let a := e / 4
  have ha : 0 < a := by dsimp [a]; linarith
  let η := min 1 (S / 4)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min one_pos (by positivity)
  let dZ := S / (8 * Real.pi)
  have hdZ : 0 < dZ := by
    dsimp [dZ]
    positivity
  let d := min (min (e / 2) dZ) (1 / 16 : ℝ)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (lt_min (by linarith) hdZ) (by norm_num)
  have hd8 : d < 1 / 8 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨d, hd, hd8, ?_⟩
  have hphase := GLTilde.eventually_uniform_shift_displacement (a := a) ha
  have hopCont : Continuous fun x : GLTilde ↦
      ‖actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ‖ :=
    continuous_norm.comp (GLTilde.continuous_actCCLM.sub continuous_const)
  have hop : ∀ᶠ x in nhds (1 : GLTilde),
      ‖actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ‖ < η := by
    have htarget : Set.Iio η ∈ nhds
        ‖actCCLM (1 : GLTilde).mat - ContinuousLinearMap.id ℝ ℂ‖ := by
      simpa using (Iio_mem_nhds hη : Set.Iio η ∈ nhds (0 : ℝ))
    exact hopCont.continuousAt htarget
  filter_upwards [hphase, hop] with x hxPhase hxOp
  intro τ hτ
  constructor
  · have hbound := stabSeminorm_near_identity_le x σ τ
    let D := ‖actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ‖
    let N := ‖actCCLM x.mat‖
    have hDη : D < η := hxOp
    have hD1 : D < 1 := lt_of_lt_of_le hDη (min_le_left _ _)
    have hDS4 : D < S / 4 := lt_of_lt_of_le hDη (min_le_right _ _)
    have hN2 : N < 2 := by
      have hN : N ≤ D + 1 := by
        dsimp [N, D]
        calc
          ‖actCCLM x.mat‖ =
              ‖(actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ) +
                ContinuousLinearMap.id ℝ ℂ‖ := by
                  congr 1
                  exact (sub_add_cancel _ _).symm
          _ ≤ ‖actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ‖ +
              ‖ContinuousLinearMap.id ℝ ℂ‖ := norm_add_le _ _
          _ = ‖actCCLM x.mat - ContinuousLinearMap.id ℝ ℂ‖ + 1 := by
            rw [ContinuousLinearMap.norm_id]
      linarith
    have hsinD : Real.sin (Real.pi * d) ≤ S / 8 := by
      have hsin_le : Real.sin (Real.pi * d) ≤ Real.pi * d := by
        have habs : |Real.sin (Real.pi * d)| ≤ |Real.pi * d| := Real.abs_sin_le_abs
        calc
          Real.sin (Real.pi * d) ≤ |Real.sin (Real.pi * d)| := le_abs_self _
          _ ≤ |Real.pi * d| := habs
          _ = Real.pi * d := abs_of_nonneg (mul_nonneg Real.pi_nonneg (le_of_lt hd))
      have hdZle : d ≤ dZ :=
        le_trans (min_le_left _ _) (min_le_right _ _)
      calc
        Real.sin (Real.pi * d) ≤ Real.pi * d := hsin_le
        _ ≤ Real.pi * dZ := by gcongr
        _ = S / 8 := by
          dsimp [dZ]
          field_simp [Real.pi_ne_zero]
    have hOld : stabilitySeminorm C σ (τ.Z - σ.Z) <
        ENNReal.ofReal (S / 8) :=
      lt_of_lt_of_le hτ.1 (ENNReal.ofReal_le_ofReal hsinD)
    have hProd : ENNReal.ofReal N *
        stabilitySeminorm C σ (τ.Z - σ.Z) <
        ENNReal.ofReal (S / 4) := by
      calc
        ENNReal.ofReal N *
            stabilitySeminorm C σ (τ.Z - σ.Z)
            ≤ ENNReal.ofReal 2 *
              stabilitySeminorm C σ (τ.Z - σ.Z) := by
              gcongr
        _ < ENNReal.ofReal 2 * ENNReal.ofReal (S / 8) := by
          exact ENNReal.mul_lt_mul_right
            (ENNReal.ofReal_ne_zero_iff.mpr (by norm_num)) ENNReal.ofReal_ne_top hOld
        _ = ENNReal.ofReal (S / 4) := by
          rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          ring
    have hDof : ENNReal.ofReal D < ENNReal.ofReal (S / 4) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hDS4
    have hsum : ENNReal.ofReal N *
        stabilitySeminorm C σ (τ.Z - σ.Z) +
        ENNReal.ofReal D < ENNReal.ofReal S := by
      calc
        ENNReal.ofReal N * stabilitySeminorm C σ (τ.Z - σ.Z) + ENNReal.ofReal D
            < ENNReal.ofReal (S / 4) + ENNReal.ofReal (S / 4) :=
              ENNReal.add_lt_add hProd hDof
        _ = ENNReal.ofReal (S / 2) := by
          rw [← ENNReal.ofReal_add (by positivity : 0 ≤ S / 4) (by positivity : 0 ≤ S / 4)]
          congr 1
          ring
        _ < ENNReal.ofReal S :=
          (ENNReal.ofReal_lt_ofReal_iff hS).2 (by linarith)
    exact lt_of_le_of_lt hbound hsum
  · have hslice := slicingDist_smul_le_of_displacement x σ τ hxPhase hτ.2
    have hde : d + a < e := by
      have hde2 : d ≤ e / 2 :=
        le_trans (min_le_left _ _) (min_le_left _ _)
      dsimp [a]
      linarith
    exact lt_of_le_of_lt hslice ((ENNReal.ofReal_lt_ofReal_iff he).2 hde)

/-! ## Joint continuity -/

/-- Joint continuity at `(1, σ)`. -/
theorem continuousAt_smul_identity
    (σ : StabilityCondition.WithClassMap C v) :
    ContinuousAt
      (fun p : GLTilde × StabilityCondition.WithClassMap C v ↦ p.1 • p.2)
      ((1 : GLTilde), σ) := by
  rw [continuousAt_def]
  intro U hU
  have hU' : U ∈ nhds σ := by simpa using hU
  obtain ⟨e, he, he8, heU⟩ :=
    CategoryTheory.Triangulated.exists_basisNhd_subset_of_mem_nhds C σ hU'
  obtain ⟨d, hd, hd8, hmaps⟩ := exists_identity_basisNhd_control σ he he8
  have hdOpen : IsOpen (basisNhd C σ d) :=
    TopologicalSpace.isOpen_generateFrom_of_mem ⟨σ, d, hd, hd8, rfl⟩
  have hdNhd : basisNhd C σ d ∈ nhds σ :=
    hdOpen.mem_nhds
      (self_mem_basisNhd C σ hd (by linarith))
  rw [nhds_prod_eq]
  apply Filter.mem_of_superset (Filter.prod_mem_prod hmaps hdNhd)
  intro p hp
  exact heU (hp.1 hp.2)

/-- The lifted matrix action is jointly continuous at every pair. -/
theorem GLTilde.continuousAt_smul_stability
    (p : GLTilde × StabilityCondition.WithClassMap C v) :
    ContinuousAt
      (fun q : GLTilde × StabilityCondition.WithClassMap C v ↦ q.1 • q.2) p := by
  let translate : GLTilde × StabilityCondition.WithClassMap C v →
      GLTilde × StabilityCondition.WithClassMap C v :=
    fun q ↦ (p.1⁻¹ * q.1, q.2)
  have htranslate : Continuous translate :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hidentity := continuousAt_smul_identity (C := C) (v := v) p.2
  have hinner : ContinuousAt
      (fun q : GLTilde × StabilityCondition.WithClassMap C v ↦
        q.1 • q.2) (translate p) := by
    simpa [translate] using hidentity
  have hfixed : Continuous fun τ : StabilityCondition.WithClassMap C v ↦ p.1 • τ :=
    p.1.continuous_const_smul_stability
  have hcomp := hfixed.continuousAt.comp' (hinner.comp' htranslate.continuousAt)
  convert hcomp using 1
  funext q
  simp [translate, mul_smul]

/-- The genuine joint action map `GLTilde × Stabᵥ(C) → Stabᵥ(C)` is
continuous. -/
theorem GLTilde.continuous_smul_stability :
    Continuous fun p : GLTilde × StabilityCondition.WithClassMap C v ↦ p.1 • p.2 :=
  continuous_iff_continuousAt.mpr GLTilde.continuousAt_smul_stability

/-- Joint continuity, strengthening `gltildeContinuousConstSMulStability`. -/
noncomputable instance gltildeContinuousSMulStability :
    ContinuousSMul GLTilde (StabilityCondition.WithClassMap C v) where
  continuous_smul := GLTilde.continuous_smul_stability

/-! ## The combined continuous action -/

/-- Autoequivalence classes carry the standard discrete topology when they
are regarded as a symmetry group. -/
noncomputable instance autPairQuotTopologicalSpace :
    TopologicalSpace (AutPairQuot v) := ⊥

noncomputable instance autPairQuotDiscreteTopology :
    DiscreteTopology (AutPairQuot v) := discreteTopology_bot _

/-- With the discrete topology on autoequivalence classes, their action is
jointly continuous. -/
theorem AutPairQuot.continuous_smul_stability :
    Continuous fun p : AutPairQuot v × StabilityCondition.WithClassMap C v ↦
      p.1 • p.2 := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [continuousAt_def]
  intro U hU
  have hconst : Continuous fun τ : StabilityCondition.WithClassMap C v ↦ p.1 • τ :=
    continuous_const_smul p.1
  have hpre : (fun τ : StabilityCondition.WithClassMap C v ↦ p.1 • τ) ⁻¹' U ∈
      nhds p.2 := hconst.continuousAt hU
  have hsingle : ({p.1} : Set (AutPairQuot v)) ∈ nhds p.1 :=
    (isOpen_discrete {p.1}).mem_nhds (Set.mem_singleton p.1)
  rw [nhds_prod_eq]
  apply Filter.mem_of_superset (Filter.prod_mem_prod hsingle hpre)
  intro q hq
  have hq1 : q.1 = p.1 := Set.mem_singleton_iff.mp hq.1
  change q.1 • q.2 ∈ U
  rw [hq1]
  exact hq.2

noncomputable instance autPairQuotContinuousSMulStability :
    ContinuousSMul (AutPairQuot v) (StabilityCondition.WithClassMap C v) where
  continuous_smul := AutPairQuot.continuous_smul_stability

/-- The direct-product symmetry group acts jointly continuously when the
autoequivalence factor has its standard discrete topology. -/
theorem continuous_combined_smul_stability :
    Continuous fun p : (GLTilde × AutPairQuot v) ×
        StabilityCondition.WithClassMap C v ↦ p.1 • p.2 := by
  change Continuous fun p : (GLTilde × AutPairQuot v) ×
      StabilityCondition.WithClassMap C v ↦ p.1.1 • (p.1.2 • p.2)
  have hAut : Continuous fun p : (GLTilde × AutPairQuot v) ×
      StabilityCondition.WithClassMap C v ↦ p.1.2 • p.2 :=
    AutPairQuot.continuous_smul_stability.comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact GLTilde.continuous_smul_stability.comp
    ((continuous_fst.comp continuous_fst).prodMk hAut)

noncomputable instance combinedContinuousSMulStability :
    ContinuousSMul (GLTilde × AutPairQuot v)
      (StabilityCondition.WithClassMap C v) where
  continuous_smul := continuous_combined_smul_stability

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
