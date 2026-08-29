/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Combined.Topology
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Topology.Group
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Continuity of each lifted linear action map

Every fixed element of `GLTilde` acts continuously, hence by a homeomorphism,
on the Bridgeland stability space.  The proof follows the two coordinates in
the definition of `basisNhd`:

* uniform continuity of `NormalizedShift` controls `slicingDist`;
* the operator norms of `actC T` and `actC T⁻¹` control `stabSeminorm`.

The resulting instance is `ContinuousConstSMul`: continuity in the stability
condition for every fixed group element.  The separate, stronger joint
statement is proved in `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Action/JointContinuous.lean`.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.Deformation

namespace CategoryTheory.Triangulated.StabilityCondition.GroupAction

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

namespace Slicing

/-- Relabelling applies the normalized shift to the largest HN phase. -/
theorem relabel_phiPlus (f : NormalizedShift) (s : Slicing C) (E : C)
    (hE : ¬IsZero E) :
    (relabel C f s).phiPlus C E hE = f.toOrderIso (s.phiPlus C E hE) := by
  obtain ⟨G, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hE
  let F : HNFiltration C (relabel C f s).P E :=
    { toPostnikovTower := G.toPostnikovTower
      φ := fun j ↦ f.toOrderIso (G.φ j)
      hφ := fun _ _ h ↦ f.toOrderIso.lt_iff_lt.mpr (G.hφ h)
      semistable := fun j ↦ by
        show s.P (f⁻¹.toOrderIso (f.toOrderIso (G.φ j))) _
        rw [NormalizedShift.inv_apply, OrderIso.symm_apply_apply]
        exact G.semistable j }
  rw [(relabel C f s).phiPlus_eq C E hE F hn hfirst,
    s.phiPlus_eq C E hE G hn hfirst]
  rfl

/-- Relabelling applies the normalized shift to the smallest HN phase. -/
theorem relabel_phiMinus (f : NormalizedShift) (s : Slicing C) (E : C)
    (hE : ¬IsZero E) :
    (relabel C f s).phiMinus C E hE = f.toOrderIso (s.phiMinus C E hE) := by
  obtain ⟨G, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hE
  let F : HNFiltration C (relabel C f s).P E :=
    { toPostnikovTower := G.toPostnikovTower
      φ := fun j ↦ f.toOrderIso (G.φ j)
      hφ := fun _ _ h ↦ f.toOrderIso.lt_iff_lt.mpr (G.hφ h)
      semistable := fun j ↦ by
        show s.P (f⁻¹.toOrderIso (f.toOrderIso (G.φ j))) _
        rw [NormalizedShift.inv_apply, OrderIso.symm_apply_apply]
        exact G.semistable j }
  rw [(relabel C f s).phiMinus_eq C E hE F hn hlast,
    s.phiMinus_eq C E hE G hn hlast]
  rfl

end Slicing

/-- A uniform source radius controlling the slicing distance after a fixed
phase relabelling. -/
theorem exists_slicingDist_relabel_control (f : NormalizedShift) {e : ℝ}
    (he : 0 < e) :
    ∃ d : ℝ, 0 < d ∧ ∀ s₁ s₂ : Slicing C,
      CategoryTheory.Triangulated.slicingDist C s₁ s₂ < ENNReal.ofReal d →
      CategoryTheory.Triangulated.slicingDist C
        (relabel C f s₁) (relabel C f s₂) < ENNReal.ofReal e := by
  obtain ⟨d, hd, hmod⟩ := Metric.uniformContinuous_iff.mp f.uniformContinuous (e / 2) (by linarith)
  refine ⟨d, hd, fun s₁ s₂ hdist ↦ ?_⟩
  have hle : CategoryTheory.Triangulated.slicingDist C
      (relabel C f s₁) (relabel C f s₂) ≤
      ENNReal.ofReal (e / 2) := by
    apply CategoryTheory.Triangulated.slicingDist_le_of_phase_bounds
    · intro E hE
      rw [Slicing.relabel_phiPlus f s₁ E hE, Slicing.relabel_phiPlus f s₂ E hE]
      rw [← Real.dist_eq]
      exact le_of_lt (hmod (by
        rw [Real.dist_eq]
        exact CategoryTheory.Triangulated.abs_phiPlus_sub_lt_of_slicingDist
          C s₁ s₂ hE hd hdist))
    · intro E hE
      rw [Slicing.relabel_phiMinus f s₁ E hE, Slicing.relabel_phiMinus f s₂ E hE]
      rw [← Real.dist_eq]
      exact le_of_lt (hmod (by
        rw [Real.dist_eq]
        exact CategoryTheory.Triangulated.abs_phiMinus_sub_lt_of_slicingDist
          C s₁ s₂ hE hd hdist))
  exact lt_of_le_of_lt hle ((ENNReal.ofReal_lt_ofReal_iff he).2 (by linarith))

/-! ## Central-charge operator bounds -/

/-- The real-linear central-charge action as a continuous linear map. -/
noncomputable def actCCLM (T : Matrix.GLPos (Fin 2) ℝ) : ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (actC T)

@[simp]
theorem actCCLM_apply (T : Matrix.GLPos (Fin 2) ℝ) (z : ℂ) :
    actCCLM T z = actC T z := rfl

theorem actC_inv_apply (T : Matrix.GLPos (Fin 2) ℝ) (z : ℂ) :
    actC T⁻¹ (actC T z) = z := by
  simpa using (actC_mul T⁻¹ T z).symm

/-- A deliberately nonzero condition bound.  The added `1` avoids a separate
positivity proof for the operator norms. -/
noncomputable def actCCondition (T : Matrix.GLPos (Fin 2) ℝ) : ℝ :=
  ‖actCCLM T‖ * ‖actCCLM T⁻¹‖ + 1

theorem actCCondition_pos (T : Matrix.GLPos (Fin 2) ℝ) : 0 < actCCondition T := by
  unfold actCCondition
  positivity

/-- The condition-number estimate used by `stabSeminorm`. -/
theorem norm_actC_div_norm_actC_le (T : Matrix.GLPos (Fin 2) ℝ)
    (z w : ℂ) (hw : w ≠ 0) :
    ‖actC T z‖ / ‖actC T w‖ ≤ actCCondition T * (‖z‖ / ‖w‖) := by
  let p := ‖actCCLM T‖
  let q := ‖actCCLM T⁻¹‖
  have hp : 0 ≤ p := norm_nonneg _
  have hq : 0 ≤ q := norm_nonneg _
  have hw0 : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hTw : actC T w ≠ 0 := by
    intro h
    apply hw
    rw [← actC_inv_apply T w, h, map_zero]
  have hTw0 : 0 < ‖actC T w‖ := norm_pos_iff.mpr hTw
  have hz0 : 0 ≤ ‖z‖ / ‖w‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hforward : ‖actC T z‖ ≤ p * ‖z‖ := (actCCLM T).le_opNorm z
  have hinverse : ‖w‖ ≤ q * ‖actC T w‖ := by
    calc
      ‖w‖ = ‖actC T⁻¹ (actC T w)‖ := congrArg norm (actC_inv_apply T w).symm
      _ ≤ q * ‖actC T w‖ := (actCCLM T⁻¹).le_opNorm (actC T w)
  apply (div_le_iff₀ hTw0).2
  calc
    ‖actC T z‖ ≤ p * ‖z‖ := hforward
    _ = (p * (‖z‖ / ‖w‖)) * ‖w‖ := by field_simp
    _ ≤ (p * (‖z‖ / ‖w‖)) * (q * ‖actC T w‖) :=
      mul_le_mul_of_nonneg_left hinverse (mul_nonneg hp hz0)
    _ = (p * q) * (‖z‖ / ‖w‖) * ‖actC T w‖ := by ring
    _ ≤ actCCondition T * (‖z‖ / ‖w‖) * ‖actC T w‖ := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · unfold actCCondition
          change p * q ≤ p * q + 1
          linarith
        · exact hz0
      · exact norm_nonneg _

variable [IsTriangulated C]

/-- A fixed matrix action expands the stability seminorm by at most its
condition bound. -/
theorem stabSeminorm_gltilde_le (x : GLTilde)
    (σ τ : StabilityCondition.WithClassMap C v) :
    stabilitySeminorm C (x • σ) ((x • τ).Z - (x • σ).Z) ≤
      ENNReal.ofReal (actCCondition x.mat) * stabilitySeminorm C σ (τ.Z - σ.Z) := by
  apply iSup_le
  intro E
  apply iSup_le
  intro φ
  apply iSup_le
  intro hP
  change σ.slicing.P (x.shift⁻¹.toOrderIso φ) E at hP
  apply iSup_le
  intro hE
  have hcharge : σ.charge E ≠ 0 := by
    obtain ⟨m, hm, hZ⟩ := σ.compat (x.shift⁻¹.toOrderIso φ) E hP hE
    rw [hZ]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hm)) (Complex.exp_ne_zero _)
  have hnum : ((x • τ).Z - (x • σ).Z) (classOf C v E) =
      actC x.mat ((τ.Z - σ.Z) (classOf C v E)) := by
    change actC x.mat (τ.Z (classOf C v E)) - actC x.mat (σ.Z (classOf C v E)) =
      actC x.mat (τ.Z (classOf C v E) - σ.Z (classOf C v E))
    exact (map_sub (actC x.mat) _ _).symm
  have hden : (x • σ).charge E = actC x.mat (σ.charge E) := rfl
  rw [hnum, hden]
  calc
    ENNReal.ofReal
        (‖actC x.mat ((τ.Z - σ.Z) (classOf C v E))‖ / ‖actC x.mat (σ.charge E)‖)
        ≤ ENNReal.ofReal (actCCondition x.mat *
          (‖(τ.Z - σ.Z) (classOf C v E)‖ / ‖σ.charge E‖)) :=
      ENNReal.ofReal_le_ofReal (norm_actC_div_norm_actC_le x.mat _ _ hcharge)
    _ = ENNReal.ofReal (actCCondition x.mat) *
        ENNReal.ofReal (‖(τ.Z - σ.Z) (classOf C v E)‖ / ‖σ.charge E‖) :=
      ENNReal.ofReal_mul (le_of_lt (actCCondition_pos x.mat))
    _ ≤ ENNReal.ofReal (actCCondition x.mat) * stabilitySeminorm C σ (τ.Z - σ.Z) := by
      apply mul_le_mul_right
      apply le_iSup_of_le E
      apply le_iSup_of_le (x.shift⁻¹.toOrderIso φ)
      apply le_iSup_of_le hP
      apply le_iSup_of_le hE
      rfl

/-! ## Basic neighborhoods and continuity -/

/-- For a fixed `GLTilde` element, every target radius admits one source
radius that works at every centre. -/
theorem exists_gltilde_basisNhd_control (x : GLTilde) {e : ℝ}
    (he : 0 < e) (he8 : e < 1 / 8) :
    ∃ d : ℝ, 0 < d ∧ d < 1 / 8 ∧
      ∀ σ : StabilityCondition.WithClassMap C v,
        Set.MapsTo (fun τ ↦ x • τ) (basisNhd C σ d) (basisNhd C (x • σ) e) := by
  obtain ⟨dS, hdS, hS⟩ := exists_slicingDist_relabel_control (C := C) x.shift he
  let K := actCCondition x.mat
  have hK : 0 < K := actCCondition_pos x.mat
  have hsin : 0 < Real.sin (Real.pi * e) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  let dZ := Real.sin (Real.pi * e) / (2 * K * Real.pi)
  have hdZ : 0 < dZ := by
    dsimp [dZ]
    positivity
  let d := min (min dS dZ) (1 / 16 : ℝ)
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min (lt_min hdS hdZ) (by norm_num)
  have hd8 : d < 1 / 8 := by
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  refine ⟨d, hd, hd8, fun σ τ hτ ↦ ?_⟩
  constructor
  · have hbound := stabSeminorm_gltilde_le x σ τ
    have hK0 : ENNReal.ofReal K ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hK)
    have hKtop : ENNReal.ofReal K ≠ ⊤ := ENNReal.ofReal_ne_top
    have hmul := ENNReal.mul_lt_mul_left hK0 hKtop hτ.1
    have hsin_le : Real.sin (Real.pi * d) ≤ Real.pi * d := by
      have habs : |Real.sin (Real.pi * d)| ≤ |Real.pi * d| := Real.abs_sin_le_abs
      calc
        Real.sin (Real.pi * d) ≤ |Real.sin (Real.pi * d)| := le_abs_self _
        _ ≤ |Real.pi * d| := habs
        _ = Real.pi * d := abs_of_nonneg (mul_nonneg Real.pi_nonneg (le_of_lt hd))
    have hdZle : d ≤ dZ := le_trans (min_le_left _ _) (min_le_right _ _)
    have hreal : K * Real.sin (Real.pi * d) < Real.sin (Real.pi * e) := by
      calc
        K * Real.sin (Real.pi * d) ≤ K * (Real.pi * d) :=
          mul_le_mul_of_nonneg_left hsin_le (le_of_lt hK)
        _ ≤ K * (Real.pi * dZ) := by gcongr
        _ = Real.sin (Real.pi * e) / 2 := by
          dsimp [dZ]
          field_simp
        _ < Real.sin (Real.pi * e) := by linarith
    exact lt_of_le_of_lt hbound <| lt_of_lt_of_le
      (by
        calc
          ENNReal.ofReal K * stabilitySeminorm C σ (τ.Z - σ.Z)
              < ENNReal.ofReal K * ENNReal.ofReal (Real.sin (Real.pi * d)) := by
                simpa [mul_comm] using hmul
          _ = ENNReal.ofReal (K * Real.sin (Real.pi * d)) :=
            (ENNReal.ofReal_mul (le_of_lt hK)).symm
          _ < ENNReal.ofReal (Real.sin (Real.pi * e)) :=
            (ENNReal.ofReal_lt_ofReal_iff hsin).2 hreal)
      le_rfl
  · apply hS σ.slicing τ.slicing
    exact lt_of_lt_of_le hτ.2 (ENNReal.ofReal_le_ofReal (min_le_left (min dS dZ) _ |>.trans
      (min_le_left dS dZ)))

/-- Every fixed `GLTilde` element acts continuously on the stability space. -/
theorem GLTilde.continuous_const_smul_stability (x : GLTilde) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ x • σ := by
  rw [continuous_generateFrom_iff]
  rintro U ⟨ξ, e, he, he8, rfl⟩
  rw [isOpen_iff_mem_nhds]
  intro τ hτ
  change x • τ ∈ basisNhd C ξ e at hτ
  obtain ⟨r, hr, hr8, hsub⟩ :=
    exists_basisNhd_subset_basisNhd C ξ (x • τ) he he8 hτ
  obtain ⟨d, hd, hd8, hmap⟩ := exists_gltilde_basisNhd_control (C := C) (v := v) x hr hr8
  refine mem_nhds_iff.mpr ⟨basisNhd C τ d, ?_, ?_,
    self_mem_basisNhd C τ hd (by linarith)⟩
  · exact fun ρ hρ ↦ hsub (hmap τ hρ)
  · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨τ, d, hd, hd8, rfl⟩

noncomputable instance gltildeContinuousConstSMulStability :
    ContinuousConstSMul GLTilde (StabilityCondition.WithClassMap C v) where
  continuous_const_smul := GLTilde.continuous_const_smul_stability

/-- The direct-product symmetry action is continuous in the stability-condition
variable for every fixed pair. -/
noncomputable instance combinedContinuousConstSMulStability :
    ContinuousConstSMul (GLTilde × AutPairQuot v)
      (StabilityCondition.WithClassMap C v) where
  continuous_const_smul p := by
    change Continuous fun σ : StabilityCondition.WithClassMap C v ↦ p.1 • (p.2 • σ)
    exact p.1.continuous_const_smul_stability.comp (continuous_const_smul p.2)

/-- A named homeomorphism for the action of each fixed lifted matrix. -/
noncomputable def GLTilde.stabilityHomeomorph (x : GLTilde) :
    StabilityCondition.WithClassMap C v ≃ₜ StabilityCondition.WithClassMap C v :=
  Homeomorph.smul x

/-- A named homeomorphism for each element of the combined symmetry group. -/
noncomputable def combinedStabilityHomeomorph (p : GLTilde × AutPairQuot v) :
    StabilityCondition.WithClassMap C v ≃ₜ StabilityCondition.WithClassMap C v :=
  Homeomorph.smul p

end

end CategoryTheory.Triangulated.StabilityCondition.GroupAction
