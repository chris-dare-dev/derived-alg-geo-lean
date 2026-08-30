/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Covering.Map
import Mathlib.Topology.Algebra.Group.Basic

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Topological-group structure on the lifted general linear group

The topology on `GLTilde` was transported from the global coordinates

```
  ℝ × (0, ∞) × ℝ × (0, ∞).
```

This file proves that the already-defined group operations are continuous for
that topology.  The main point is joint continuity of phase evaluation
`(x, φ) ↦ x.shift φ`.  In global coordinates the normalized upper-triangular
lift is

```
  φ + (arg (W φ) - arg (W 0)) / π,
```

so the potentially discontinuous global branch `arg (cA)` cancels.  Every
`W φ` lies in the open right half-plane, where `arg` is continuous.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open Complex Matrix Real Set Topology

/-! ## The normalized upper-triangular lift -/

theorem upperSectionZero_shift_apply (r : PositiveReal) (b : ℝ) (d : PositiveReal)
    (φ : ℝ) :
    (upperSectionZero r b d).shift.toOrderIso φ =
      lift (upperGLPos r b d) φ - lift (upperGLPos r b d) 0 := by
  simp only [upperSectionZero, GLTilde.mul_shift, NormalizedShift.mul_apply, deck_shift,
    deckShift_apply, sect, liftShift_apply]
  rw [upperDeckIndex_spec]
  push_cast
  ring

/-- Phase evaluation written entirely in the global coordinates. -/
noncomputable def coordinateShift (c : GLTildeCoordinates) (φ : ℝ) : ℝ :=
  φ + ((Wmap (upperGLPos c.2.1 c.2.2.1 c.2.2.2) φ).arg -
    (Wmap (upperGLPos c.2.1 c.2.2.1 c.2.2.2) 0).arg) / Real.pi + c.1

theorem glTildeOfCoordinates_shift_apply (c : GLTildeCoordinates) (φ : ℝ) :
    (glTildeOfCoordinates c).shift.toOrderIso φ = coordinateShift c φ := by
  rw [glTildeOfCoordinates, GLTilde.mul_shift, NormalizedShift.mul_apply,
    liftedRotation, phaseTranslation_apply, upperSectionZero_shift_apply]
  simp only [coordinateShift, lift]
  ring

private theorem continuous_cA : Continuous (cA : Matrix.GLPos (Fin 2) ℝ → ℂ) := by
  have h : Continuous fun T : Matrix.GLPos (Fin 2) ℝ =>
      ((toMat T 0 0 + toMat T 1 1) / 2,
        (toMat T 1 0 - toMat T 0 1) / 2) :=
    ((continuous_toMatGLPos.matrix_elem 0 0).add
      (continuous_toMatGLPos.matrix_elem 1 1) |>.div_const 2).prodMk
        ((continuous_toMatGLPos.matrix_elem 1 0).sub
          (continuous_toMatGLPos.matrix_elem 0 1) |>.div_const 2)
  convert Complex.equivRealProdCLM.symm.continuous.comp h using 1
  funext T
  apply Complex.ext <;>
    simp [cA, Complex.equivRealProdCLM_symm_apply]

private theorem continuous_cB : Continuous (cB : Matrix.GLPos (Fin 2) ℝ → ℂ) := by
  have h : Continuous fun T : Matrix.GLPos (Fin 2) ℝ =>
      ((toMat T 0 0 - toMat T 1 1) / 2,
        (toMat T 1 0 + toMat T 0 1) / 2) :=
    ((continuous_toMatGLPos.matrix_elem 0 0).sub
      (continuous_toMatGLPos.matrix_elem 1 1) |>.div_const 2).prodMk
        ((continuous_toMatGLPos.matrix_elem 1 0).add
          (continuous_toMatGLPos.matrix_elem 0 1) |>.div_const 2)
  convert Complex.equivRealProdCLM.symm.continuous.comp h using 1
  funext T
  apply Complex.ext <;>
    simp [cB, Complex.equivRealProdCLM_symm_apply]

private theorem continuous_ratio : Continuous (ratio : Matrix.GLPos (Fin 2) ℝ → ℂ) := by
  exact continuous_cB.div continuous_cA cA_ne_zero

private theorem continuous_cexpI : Continuous cexpI := by
  exact Complex.continuous_exp.comp <|
    Complex.continuous_ofReal.mul continuous_const

private theorem continuous_upperGLPos :
    Continuous fun c : GLTildeCoordinates => upperGLPos c.2.1 c.2.2.1 c.2.2.2 := by
  rw [continuous_induced_rng, Units.continuous_iff]
  constructor
  · apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> simp [upperGLPos, upperMatrix] <;> fun_prop
  · have hr : Continuous fun c : GLTildeCoordinates => ((c.2.1 : ℝ)⁻¹) :=
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).inv₀
        (fun c => ne_of_gt c.2.1.2))
    have hd : Continuous fun c : GLTildeCoordinates => ((c.2.2.2 : ℝ)⁻¹) :=
      ((continuous_subtype_val.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd))).inv₀
          (fun c => ne_of_gt c.2.2.2.2))
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [upperGLPos, upperMatrixInv] <;> fun_prop

private theorem continuous_coordinateWmap :
    Continuous fun p : GLTildeCoordinates × ℝ =>
      Wmap (upperGLPos p.1.2.1 p.1.2.2.1 p.1.2.2.2) p.2 := by
  have hr : Continuous fun p : GLTildeCoordinates × ℝ =>
      ratio (upperGLPos p.1.2.1 p.1.2.2.1 p.1.2.2.2) :=
    continuous_ratio.comp (continuous_upperGLPos.comp continuous_fst)
  have he : Continuous fun p : GLTildeCoordinates × ℝ =>
      cexpI (-(2 * Real.pi * p.2)) :=
    continuous_cexpI.comp (by fun_prop)
  have hOne : Continuous fun _ : GLTildeCoordinates × ℝ => (1 : ℂ) :=
    continuous_const
  convert hOne.add (hr.mul he) using 1
  funext p
  rfl

private theorem continuous_coordinateWmap_zero :
    Continuous fun c : GLTildeCoordinates =>
      Wmap (upperGLPos c.2.1 c.2.2.1 c.2.2.2) 0 := by
  have hr : Continuous fun c : GLTildeCoordinates =>
      ratio (upperGLPos c.2.1 c.2.2.1 c.2.2.2) :=
    continuous_ratio.comp continuous_upperGLPos
  have hOne : Continuous fun _ : GLTildeCoordinates => (1 : ℂ) :=
    continuous_const
  have hExp : Continuous fun _ : GLTildeCoordinates => cexpI (-(2 * Real.pi * 0)) :=
    continuous_const
  convert hOne.add (hr.mul hExp) using 1
  funext c
  rfl

private theorem continuous_coordinateShift_uncurry :
    Continuous fun p : GLTildeCoordinates × ℝ => coordinateShift p.1 p.2 := by
  apply continuous_iff_continuousAt.mpr
  intro p
  have hφ : ContinuousAt (fun q : GLTildeCoordinates × ℝ =>
      (Wmap (upperGLPos q.1.2.1 q.1.2.2.1 q.1.2.2.2) q.2).arg) p := by
    have harg := Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr <|
      Or.inl (Wmap_re_pos (upperGLPos p.1.2.1 p.1.2.2.1 p.1.2.2.2) p.2))
    exact ContinuousAt.comp' (f := fun q : GLTildeCoordinates × ℝ =>
      Wmap (upperGLPos q.1.2.1 q.1.2.2.1 q.1.2.2.2) q.2)
        harg continuous_coordinateWmap.continuousAt
  have h0 : ContinuousAt (fun q : GLTildeCoordinates × ℝ =>
      (Wmap (upperGLPos q.1.2.1 q.1.2.2.1 q.1.2.2.2) 0).arg) p := by
    have hW : Continuous fun q : GLTildeCoordinates × ℝ =>
        Wmap (upperGLPos q.1.2.1 q.1.2.2.1 q.1.2.2.2) 0 :=
      continuous_coordinateWmap_zero.comp continuous_fst
    have harg := Complex.continuousAt_arg (Complex.mem_slitPlane_iff.mpr <|
      Or.inl (Wmap_re_pos (upperGLPos p.1.2.1 p.1.2.2.1 p.1.2.2.2) 0))
    exact ContinuousAt.comp' (f := fun q : GLTildeCoordinates × ℝ =>
      Wmap (upperGLPos q.1.2.1 q.1.2.2.1 q.1.2.2.2) 0) harg hW.continuousAt
  exact continuousAt_snd.add ((hφ.sub h0).div_const Real.pi) |>.add
    (continuousAt_fst.fst)

/-! ## Joint phase evaluation -/

/-- Evaluation of the phase relabelling is jointly continuous in the lifted
matrix and the phase. -/
theorem GLTilde.continuous_shift_apply :
    Continuous fun p : GLTilde × ℝ => p.1.shift.toOrderIso p.2 := by
  have h := continuous_coordinateShift_uncurry.comp
    ((glTildeCoordinateHomeomorph.continuous.comp continuous_fst).prodMk continuous_snd)
  convert h using 1
  funext p
  change p.1.shift.toOrderIso p.2 =
    coordinateShift (glTildeCoordinates p.1) p.2
  rw [← glTildeOfCoordinates_shift_apply]
  exact congrArg (fun x : GLTilde => x.shift.toOrderIso p.2)
    (glTildeOfCoordinates_coordinates p.1).symm

/-! ## Continuous group operations -/

private theorem continuous_alignedMatrix_of_continuous {X : Type*} [TopologicalSpace X]
    {f : X → GLTilde} (hmat : Continuous fun x => (f x).mat)
    (hzero : Continuous fun x => (f x).shift.toOrderIso 0) :
    Continuous fun x => alignedMatrix (f x) := by
  apply Continuous.matrix_mul
  · exact continuous_rotationMatrix.comp (continuous_neg.comp hzero)
  · exact continuous_toMatGLPos.comp hmat

private theorem continuous_glTildeCoordinates_of_continuous {X : Type*} [TopologicalSpace X]
    {f : X → GLTilde} (hmat : Continuous fun x => (f x).mat)
    (hzero : Continuous fun x => (f x).shift.toOrderIso 0) :
    Continuous fun x => glTildeCoordinates (f x) := by
  have ha := continuous_alignedMatrix_of_continuous hmat hzero
  exact hzero.prodMk <|
    ((ha.matrix_elem 0 0).subtype_mk _).prodMk <|
      (ha.matrix_elem 0 1).prodMk ((ha.matrix_elem 1 1).subtype_mk _)

private theorem continuous_mul_glTilde : Continuous fun p : GLTilde × GLTilde => p.1 * p.2 := by
  rw [← glTildeCoordinateHomeomorph.comp_continuous_iff]
  change Continuous fun p : GLTilde × GLTilde => glTildeCoordinates (p.1 * p.2)
  apply continuous_glTildeCoordinates_of_continuous
  · convert continuous_mul.comp
      (GLTilde.continuous_toMat.comp continuous_fst |>.prodMk
        (GLTilde.continuous_toMat.comp continuous_snd)) using 1
    funext p
    simp only [Function.comp_apply, GLTilde.mul_mat]
  · have hy0 : Continuous fun p : GLTilde × GLTilde => p.2.shift.toOrderIso 0 :=
      GLTilde.continuous_shift_apply.comp
        (continuous_snd.prodMk (continuous_const : Continuous fun _ : GLTilde × GLTilde =>
          (0 : ℝ)))
    have h := GLTilde.continuous_shift_apply.comp (continuous_fst.prodMk hy0)
    convert h using 1
    funext p
    simp only [GLTilde.mul_shift, NormalizedShift.mul_apply, Function.comp_apply]

/-! ## Inversion in the upper-triangular coordinates -/

/-- The positive-diagonal upper-triangular coordinates of the inverse. -/
private noncomputable def inverseUpperCoordinates (c : GLTildeCoordinates) :
    GLTildeCoordinates :=
  (0,
    ⟨(c.2.1 : ℝ)⁻¹, by
      change 0 < (c.2.1 : ℝ)⁻¹
      exact inv_pos.mpr c.2.1.2⟩,
    -((c.2.1 : ℝ)⁻¹ * c.2.2.1 * (c.2.2.2 : ℝ)⁻¹),
    ⟨(c.2.2.2 : ℝ)⁻¹, by
      change 0 < (c.2.2.2 : ℝ)⁻¹
      exact inv_pos.mpr (c.2.2.2).2⟩)

private theorem continuous_inverseUpperCoordinates : Continuous inverseUpperCoordinates := by
  have hr : Continuous fun c : GLTildeCoordinates => ((c.2.1 : ℝ)⁻¹) :=
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).inv₀
      (fun c => ne_of_gt c.2.1.2))
  have hb : Continuous fun c : GLTildeCoordinates => c.2.2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hd : Continuous fun c : GLTildeCoordinates => ((c.2.2.2 : ℝ)⁻¹) :=
    ((continuous_subtype_val.comp
      (continuous_snd.comp (continuous_snd.comp continuous_snd))).inv₀
        (fun c => ne_of_gt c.2.2.2.2))
  have hzero : Continuous fun _ : GLTildeCoordinates => (0 : ℝ) := continuous_const
  exact hzero.prodMk <|
    (hr.subtype_mk _).prodMk <|
      ((hr.mul hb |>.mul hd).neg).prodMk (hd.subtype_mk _)

private theorem upperGLPos_inv_eq (c : GLTildeCoordinates) :
    (upperGLPos c.2.1 c.2.2.1 c.2.2.2)⁻¹ =
      upperGLPos (inverseUpperCoordinates c).2.1
        (inverseUpperCoordinates c).2.2.1 (inverseUpperCoordinates c).2.2.2 := by
  apply Subtype.ext
  apply Units.ext
  change upperMatrixInv c.2.1 c.2.2.1 c.2.2.2 =
    upperMatrix (inverseUpperCoordinates c).2.1
      (inverseUpperCoordinates c).2.2.1 (inverseUpperCoordinates c).2.2.2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrixInv, upperMatrix, inverseUpperCoordinates]

private theorem upperSectionZero_inv_eq (c : GLTildeCoordinates) :
    (upperSectionZero c.2.1 c.2.2.1 c.2.2.2)⁻¹ =
      upperSectionZero (inverseUpperCoordinates c).2.1
        (inverseUpperCoordinates c).2.2.1 (inverseUpperCoordinates c).2.2.2 := by
  apply GLTilde.ext_mat_shift_zero
  · simpa only [GLTilde.inv_mat, upperSectionZero_mat] using upperGLPos_inv_eq c
  · rw [GLTilde.inv_shift, NormalizedShift.inv_apply, OrderIso.symm_apply_eq]
    simp

private theorem liftedRotation_inv_shift_zero (θ : ℝ) :
    ((liftedRotation θ)⁻¹).shift.toOrderIso 0 = -θ := by
  rw [GLTilde.inv_shift, NormalizedShift.inv_apply, OrderIso.symm_apply_eq]
  simp [liftedRotation]

private theorem glTildeOfCoordinates_inv_shift_zero (c : GLTildeCoordinates) :
    ((glTildeOfCoordinates c)⁻¹).shift.toOrderIso 0 =
      coordinateShift (inverseUpperCoordinates c) (-c.1) := by
  rw [glTildeOfCoordinates, _root_.mul_inv_rev, upperSectionZero_inv_eq,
    GLTilde.mul_shift, NormalizedShift.mul_apply, liftedRotation_inv_shift_zero]
  rw [upperSectionZero_shift_apply]
  simp only [coordinateShift, inverseUpperCoordinates, lift]
  ring

private theorem continuous_inv_shift_zero :
    Continuous fun x : GLTilde => (x⁻¹).shift.toOrderIso 0 := by
  have hc : Continuous fun c : GLTildeCoordinates =>
      coordinateShift (inverseUpperCoordinates c) (-c.1) :=
    continuous_coordinateShift_uncurry.comp <|
      continuous_inverseUpperCoordinates.prodMk (continuous_neg.comp continuous_fst)
  have h := hc.comp glTildeCoordinateHomeomorph.continuous
  convert h using 1
  funext x
  change (x⁻¹).shift.toOrderIso 0 =
    coordinateShift (inverseUpperCoordinates (glTildeCoordinates x))
      (-(glTildeCoordinates x).1)
  rw [← glTildeOfCoordinates_inv_shift_zero]
  exact congrArg (fun y : GLTilde => (y⁻¹).shift.toOrderIso 0)
    (glTildeOfCoordinates_coordinates x).symm

private theorem continuous_inv_glTilde : Continuous fun x : GLTilde => x⁻¹ := by
  rw [← glTildeCoordinateHomeomorph.comp_continuous_iff]
  change Continuous fun x : GLTilde => glTildeCoordinates x⁻¹
  apply continuous_glTildeCoordinates_of_continuous
  · convert continuous_inv.comp GLTilde.continuous_toMat using 1
    funext x
    simp only [Function.comp_apply, GLTilde.inv_mat]
  · exact continuous_inv_shift_zero

/-- The transported global-coordinate topology is compatible with the group
operations. -/
noncomputable instance GLTilde.isTopologicalGroup : IsTopologicalGroup GLTilde where
  continuous_mul := continuous_mul_glTilde
  continuous_inv := continuous_inv_glTilde

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
