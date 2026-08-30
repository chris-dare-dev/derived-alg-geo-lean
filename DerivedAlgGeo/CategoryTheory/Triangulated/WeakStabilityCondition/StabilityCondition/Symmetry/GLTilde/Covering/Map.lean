/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Covering.SourceTopology
import MathFormalContract
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homeomorph.Lemmas

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The lifted group as a covering of the positive general linear group

This file completes the topological part of the universal-cover construction.
The base has coordinates

```
  S¹ × (0, ∞) × ℝ × (0, ∞),
```

obtained from the direction and length of the first column, followed by the
coordinates of the second column in the resulting oriented orthonormal frame.
In these coordinates the matrix projection is the product of

```
  θ ↦ exp(π θ) : ℝ → S¹
```

with the identity on the remaining three coordinates.  The first map is the
standard exponential covering; the product and coordinate homeomorphisms
therefore give the required covering map.

`WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Topology/Group.lean` supplies the final compatibility layer by
proving that the transported topology makes `GLTilde` a topological group.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open Complex Matrix Real Set Topology

/-! ## Circle-valued rotations -/

/-- Rotation matrix whose first column is the point `z` of the unit circle. -/
def circleMatrix (z : Circle) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(z : ℂ).re, -(z : ℂ).im; (z : ℂ).im, (z : ℂ).re]

/-- The transpose/inverse of `circleMatrix`. -/
def circleMatrixInv (z : Circle) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(z : ℂ).re, (z : ℂ).im; -(z : ℂ).im, (z : ℂ).re]

@[simp]
theorem circleMatrix_det (z : Circle) : (circleMatrix z).det = 1 := by
  have hz := Circle.normSq_coe z
  simpa [circleMatrix, Matrix.det_fin_two_of, Complex.normSq_apply] using hz

@[simp]
theorem circleMatrix_mul_inv (z : Circle) : circleMatrix z * circleMatrixInv z = 1 := by
  have hz : (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im = 1 := by
    simpa [Complex.normSq_apply] using Circle.normSq_coe z
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circleMatrix, circleMatrixInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [hz]

@[simp]
theorem circleMatrix_inv_mul (z : Circle) : circleMatrixInv z * circleMatrix z = 1 := by
  have hz : (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im = 1 := by
    simpa [Complex.normSq_apply] using Circle.normSq_coe z
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circleMatrix, circleMatrixInv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith [hz]

/-- A circle-valued rotation as an element of `GL⁺(2, ℝ)`. -/
noncomputable def circleGLPos (z : Circle) : Matrix.GLPos (Fin 2) ℝ :=
  ⟨⟨circleMatrix z, circleMatrixInv z, circleMatrix_mul_inv z, circleMatrix_inv_mul z⟩,
    by simp⟩

@[simp]
theorem circleGLPos_mat (z : Circle) : toMat (circleGLPos z) = circleMatrix z := rfl

/-! ## Global coordinates on the base -/

/-- Coordinates on `GL⁺(2, ℝ)`: first-column direction and radius, followed by
the coordinates of the second column in that oriented orthonormal frame. -/
abbrev GLPosCoordinates := Circle × PositiveReal × ℝ × PositiveReal

/-- The first column of a positive-determinant matrix, regarded as a complex number. -/
def firstColumnComplex (T : Matrix.GLPos (Fin 2) ℝ) : ℂ :=
  ⟨toMat T 0 0, toMat T 1 0⟩

theorem firstColumnComplex_ne_zero (T : Matrix.GLPos (Fin 2) ℝ) :
    firstColumnComplex T ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [firstColumnComplex] at hre him
  have hdet := T.2
  change 0 < (toMat T).det at hdet
  rw [Matrix.det_fin_two] at hdet
  simp [hre, him] at hdet

/-- The positive length of the first column. -/
noncomputable def firstColumnRadius (T : Matrix.GLPos (Fin 2) ℝ) : PositiveReal :=
  ⟨‖firstColumnComplex T‖, norm_pos_iff.mpr (firstColumnComplex_ne_zero T)⟩

/-- The direction of the first column. -/
noncomputable def firstColumnDirection (T : Matrix.GLPos (Fin 2) ℝ) : Circle :=
  ⟨((‖firstColumnComplex T‖⁻¹ : ℝ) : ℂ) * firstColumnComplex T, by
    change ((‖firstColumnComplex T‖⁻¹ : ℝ) : ℂ) * firstColumnComplex T ∈
      Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, norm_mul, norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (firstColumnComplex_ne_zero T)⟩

@[simp]
theorem firstColumnDirection_re (T : Matrix.GLPos (Fin 2) ℝ) :
    ((firstColumnDirection T : Circle) : ℂ).re =
      toMat T 0 0 / (firstColumnRadius T : ℝ) := by
  rw [show ((firstColumnDirection T : Circle) : ℂ) =
      ((‖firstColumnComplex T‖⁻¹ : ℝ) : ℂ) * firstColumnComplex T by rfl]
  change (((‖firstColumnComplex T‖⁻¹ : ℝ) : ℂ) * firstColumnComplex T).re =
    toMat T 0 0 / ‖firstColumnComplex T‖
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    firstColumnComplex]
  rw [div_eq_mul_inv, mul_comm]

@[simp]
theorem firstColumnDirection_im (T : Matrix.GLPos (Fin 2) ℝ) :
    ((firstColumnDirection T : Circle) : ℂ).im =
      toMat T 1 0 / (firstColumnRadius T : ℝ) := by
  rw [show ((firstColumnDirection T : Circle) : ℂ) =
      ((‖firstColumnComplex T‖⁻¹ : ℝ) : ℂ) * firstColumnComplex T by rfl]
  change (((‖firstColumnComplex T‖⁻¹ : ℝ) : ℂ) * firstColumnComplex T).im =
    toMat T 1 0 / ‖firstColumnComplex T‖
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    firstColumnComplex]
  rw [div_eq_mul_inv, mul_comm]

/-- Component of the second column along the normalized first column. -/
noncomputable def secondColumnAlong (T : Matrix.GLPos (Fin 2) ℝ) : ℝ :=
  ((firstColumnDirection T : Circle) : ℂ).re * toMat T 0 1 +
    ((firstColumnDirection T : Circle) : ℂ).im * toMat T 1 1

/-- Component of the second column along the positively oriented normal. -/
noncomputable def secondColumnPerp (T : Matrix.GLPos (Fin 2) ℝ) : ℝ :=
  -(((firstColumnDirection T : Circle) : ℂ).im * toMat T 0 1) +
    ((firstColumnDirection T : Circle) : ℂ).re * toMat T 1 1

theorem secondColumnPerp_pos (T : Matrix.GLPos (Fin 2) ℝ) : 0 < secondColumnPerp T := by
  have hr : 0 < (firstColumnRadius T : ℝ) := (firstColumnRadius T).2
  have hdet := T.2
  change 0 < (toMat T).det at hdet
  rw [Matrix.det_fin_two] at hdet
  rw [secondColumnPerp, firstColumnDirection_re, firstColumnDirection_im,
    div_mul_eq_mul_div, div_mul_eq_mul_div]
  have : -((toMat T 1 0 * toMat T 0 1) / (firstColumnRadius T : ℝ)) +
      (toMat T 0 0 * toMat T 1 1) / (firstColumnRadius T : ℝ) =
      (toMat T 0 0 * toMat T 1 1 - toMat T 0 1 * toMat T 1 0) /
        (firstColumnRadius T : ℝ) := by ring
  rw [this]
  exact div_pos hdet hr

/-- Coordinates of a positive-determinant matrix. -/
noncomputable def glPosCoordinates (T : Matrix.GLPos (Fin 2) ℝ) : GLPosCoordinates :=
  (firstColumnDirection T, firstColumnRadius T, secondColumnAlong T,
    ⟨secondColumnPerp T, secondColumnPerp_pos T⟩)

/-- Reconstruct a positive-determinant matrix from its circle coordinates. -/
noncomputable def glPosOfCoordinates (c : GLPosCoordinates) : Matrix.GLPos (Fin 2) ℝ :=
  circleGLPos c.1 * upperGLPos c.2.1 c.2.2.1 c.2.2.2

@[simp]
theorem glPosOfCoordinates_mat (c : GLPosCoordinates) :
    toMat (glPosOfCoordinates c) = circleMatrix c.1 *
      upperMatrix c.2.1 c.2.2.1 c.2.2.2 := by
  simp [glPosOfCoordinates, toMat_mul]

private theorem norm_firstColumn_glPosOfCoordinates (c : GLPosCoordinates) :
    ‖firstColumnComplex (glPosOfCoordinates c)‖ = (c.2.1 : ℝ) := by
  rcases c with ⟨z, r, b, d⟩
  rw [show firstColumnComplex (glPosOfCoordinates (z, r, b, d)) =
      (r : ℂ) * (z : ℂ) by
    apply Complex.ext <;>
      simp [firstColumnComplex, glPosOfCoordinates_mat, circleMatrix, upperMatrix,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring]
  have hr : 0 < (r : ℝ) := r.2
  change ‖(r : ℂ) * (z : ℂ)‖ = (r : ℝ)
  rw [norm_mul, norm_real, Real.norm_of_nonneg hr.le, Circle.norm_coe, mul_one]

@[simp]
theorem firstColumnDirection_glPosOfCoordinates (c : GLPosCoordinates) :
    firstColumnDirection (glPosOfCoordinates c) = c.1 := by
  rcases c with ⟨z, r, b, d⟩
  apply Circle.ext
  rw [show ((firstColumnDirection (glPosOfCoordinates (z, r, b, d)) : Circle) : ℂ) =
      ((‖firstColumnComplex (glPosOfCoordinates (z, r, b, d))‖⁻¹ : ℝ) : ℂ) *
        firstColumnComplex (glPosOfCoordinates (z, r, b, d)) by rfl]
  rw [show firstColumnComplex (glPosOfCoordinates (z, r, b, d)) =
      (r : ℂ) * (z : ℂ) by
    apply Complex.ext <;>
      simp [firstColumnComplex, glPosOfCoordinates_mat, circleMatrix, upperMatrix,
        Matrix.mul_apply, Fin.sum_univ_two] <;> ring]
  have hr : 0 < (r : ℝ) := r.2
  rw [show ‖(r : ℂ) * (z : ℂ)‖ = (r : ℝ) by
    rw [norm_mul, norm_real, Real.norm_of_nonneg hr.le, Circle.norm_coe, mul_one]]
  rw [← mul_assoc, ← Complex.ofReal_mul]
  simp [ne_of_gt hr]

@[simp]
theorem secondColumnAlong_glPosOfCoordinates (c : GLPosCoordinates) :
    secondColumnAlong (glPosOfCoordinates c) = c.2.2.1 := by
  rcases c with ⟨z, r, b, d⟩
  have hz : (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im = 1 := by
    simpa [Complex.normSq_apply] using Circle.normSq_coe z
  rw [secondColumnAlong, firstColumnDirection_glPosOfCoordinates]
  simp [glPosOfCoordinates_mat, circleMatrix, upperMatrix, Matrix.mul_apply,
    Fin.sum_univ_two]
  calc
    (z : ℂ).re * ((z : ℂ).re * b - (z : ℂ).im * (d : ℝ)) +
        (z : ℂ).im * ((z : ℂ).im * b + (z : ℂ).re * d) =
      ((z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im) * b := by ring
    _ = b := by rw [hz]; ring

@[simp]
theorem secondColumnPerp_glPosOfCoordinates (c : GLPosCoordinates) :
    secondColumnPerp (glPosOfCoordinates c) = c.2.2.2 := by
  rcases c with ⟨z, r, b, d⟩
  have hz : (z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im = 1 := by
    simpa [Complex.normSq_apply] using Circle.normSq_coe z
  rw [secondColumnPerp, firstColumnDirection_glPosOfCoordinates]
  simp [glPosOfCoordinates_mat, circleMatrix, upperMatrix, Matrix.mul_apply,
    Fin.sum_univ_two]
  calc
    -((z : ℂ).im * ((z : ℂ).re * b - (z : ℂ).im * (d : ℝ))) +
        (z : ℂ).re * ((z : ℂ).im * b + (z : ℂ).re * d) =
      ((z : ℂ).re * (z : ℂ).re + (z : ℂ).im * (z : ℂ).im) * d := by ring
    _ = d := by rw [hz]; ring

@[simp]
theorem glPosCoordinates_ofCoordinates (c : GLPosCoordinates) :
    glPosCoordinates (glPosOfCoordinates c) = c := by
  rcases c with ⟨z, r, b, d⟩
  apply Prod.ext
  · exact firstColumnDirection_glPosOfCoordinates _
  · apply Prod.ext
    · apply Subtype.ext
      exact norm_firstColumn_glPosOfCoordinates _
    · apply Prod.ext
      · exact secondColumnAlong_glPosOfCoordinates _
      · apply Subtype.ext
        exact secondColumnPerp_glPosOfCoordinates _

theorem glPosOfCoordinates_coordinates (T : Matrix.GLPos (Fin 2) ℝ) :
    glPosOfCoordinates (glPosCoordinates T) = T := by
  have hr : 0 < (firstColumnRadius T : ℝ) := (firstColumnRadius T).2
  have hr0 : (firstColumnRadius T : ℝ) ≠ 0 := ne_of_gt hr
  have hnorm : (firstColumnRadius T : ℝ) ^ 2 =
      toMat T 0 0 ^ 2 + toMat T 1 0 ^ 2 := by
    simp [firstColumnRadius, firstColumnComplex, Complex.sq_norm]
    ring
  apply Subtype.ext
  apply Units.ext
  change toMat (glPosOfCoordinates (glPosCoordinates T)) = toMat T
  rw [glPosOfCoordinates_mat]
  ext i j
  fin_cases i <;> fin_cases j
  · simp [glPosCoordinates, circleMatrix, upperMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      firstColumnDirection_re, hr0]
  · simp [glPosCoordinates, circleMatrix, upperMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      secondColumnAlong, secondColumnPerp, firstColumnDirection_re,
      firstColumnDirection_im]
    field_simp [hr0]
    rw [hnorm]
    ring
  · simp [glPosCoordinates, circleMatrix, upperMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      firstColumnDirection_im, hr0]
  · simp [glPosCoordinates, circleMatrix, upperMatrix, Matrix.mul_apply, Fin.sum_univ_two,
      secondColumnAlong, secondColumnPerp, firstColumnDirection_re,
      firstColumnDirection_im]
    field_simp [hr0]
    rw [hnorm]
    ring

/-! ## The base-coordinate homeomorphism -/

/-- The underlying matrix of an element of `GL⁺(2, ℝ)` depends continuously
on that element. -/
theorem continuous_toMatGLPos :
    Continuous (toMat : Matrix.GLPos (Fin 2) ℝ → Matrix (Fin 2) (Fin 2) ℝ) :=
  Units.continuous_val.comp continuous_subtype_val

private theorem continuous_firstColumnComplex : Continuous firstColumnComplex := by
  have h : Continuous fun T : Matrix.GLPos (Fin 2) ℝ =>
      (toMat T 0 0, toMat T 1 0) :=
    (continuous_apply 0 |>.comp (continuous_apply 0 |>.comp continuous_toMatGLPos)).prodMk
      (continuous_apply 0 |>.comp (continuous_apply 1 |>.comp continuous_toMatGLPos))
  convert Complex.equivRealProdCLM.symm.continuous.comp h using 1
  funext T
  apply Complex.ext <;>
    simp [firstColumnComplex, Complex.equivRealProdCLM_symm_apply]

private theorem continuous_firstColumnDirection : Continuous firstColumnDirection := by
  apply Continuous.subtype_mk
  have hInv : Continuous fun T : Matrix.GLPos (Fin 2) ℝ => ‖firstColumnComplex T‖⁻¹ :=
    (continuous_norm.comp continuous_firstColumnComplex).inv₀
      (fun T ↦ norm_ne_zero_iff.mpr (firstColumnComplex_ne_zero T))
  exact (Complex.continuous_ofReal.comp hInv).mul continuous_firstColumnComplex

private theorem continuous_glPosCoordinates : Continuous glPosCoordinates := by
  have hz : Continuous fun T : Matrix.GLPos (Fin 2) ℝ =>
      ((firstColumnDirection T : Circle) : ℂ) :=
    continuous_subtype_val.comp continuous_firstColumnDirection
  apply Continuous.prodMk continuous_firstColumnDirection
  apply Continuous.prodMk
  · exact Continuous.subtype_mk (continuous_norm.comp continuous_firstColumnComplex) _
  apply Continuous.prodMk
  · exact ((Complex.continuous_re.comp hz).mul
      (continuous_apply 1 |>.comp (continuous_apply 0 |>.comp continuous_toMatGLPos))).add
      ((Complex.continuous_im.comp hz).mul
        (continuous_apply 1 |>.comp (continuous_apply 1 |>.comp continuous_toMatGLPos)))
  · apply Continuous.subtype_mk
    · exact ((Complex.continuous_im.comp hz).mul
        (continuous_apply 1 |>.comp (continuous_apply 0 |>.comp continuous_toMatGLPos))).neg.add
        ((Complex.continuous_re.comp hz).mul
          (continuous_apply 1 |>.comp (continuous_apply 1 |>.comp continuous_toMatGLPos)))

private theorem continuous_glPosOfCoordinates : Continuous glPosOfCoordinates := by
  rw [continuous_induced_rng, Units.continuous_iff]
  constructor
  · change Continuous fun c : GLPosCoordinates => toMat (glPosOfCoordinates c)
    simp only [glPosOfCoordinates_mat]
    apply Continuous.matrix_mul
    · apply continuous_matrix
      intro i j
      fin_cases i <;> fin_cases j <;> simp [circleMatrix] <;> fun_prop
    · apply continuous_matrix
      intro i j
      fin_cases i <;> fin_cases j <;> simp [upperMatrix] <;> fun_prop
  · have hr : Continuous fun c : GLPosCoordinates => ((c.2.1 : ℝ)⁻¹) :=
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).inv₀
        (fun c => ne_of_gt c.2.1.2))
    have hd : Continuous fun c : GLPosCoordinates => ((c.2.2.2 : ℝ)⁻¹) :=
      ((continuous_subtype_val.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd))).inv₀
          (fun c => ne_of_gt c.2.2.2.2))
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [glPosOfCoordinates, circleGLPos, circleMatrixInv, upperGLPos, upperMatrixInv,
        Matrix.mul_apply, Fin.sum_univ_two] <;>
      fun_prop

/-- Global coordinates on `GL⁺(2, ℝ)`. -/
noncomputable def glPosCoordinateHomeomorph :
    Matrix.GLPos (Fin 2) ℝ ≃ₜ GLPosCoordinates where
  toFun := glPosCoordinates
  invFun := glPosOfCoordinates
  left_inv := glPosOfCoordinates_coordinates
  right_inv := glPosCoordinates_ofCoordinates
  continuous_toFun := continuous_glPosCoordinates
  continuous_invFun := continuous_glPosOfCoordinates

/-! ## Products of covering maps -/

/-- A covering map remains a covering map after taking its product with an
identity map. -/
theorem isCoveringMap_prodMap_id {E X Y : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [TopologicalSpace Y] {f : E → X} (hf : IsCoveringMap f) :
    IsCoveringMap (Prod.map f (id : Y → Y)) := by
  intro xy
  obtain ⟨hdisc, U, hxU, hU, hfU, H, hH⟩ := hf xy.1
  let I := f ⁻¹' ({xy.1} : Set X)
  apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := I)
  have hpre : Prod.map f (id : Y → Y) ⁻¹' (U ×ˢ Set.univ) =
      (f ⁻¹' U) ×ˢ Set.univ := by
    ext p
    simp [Prod.map]
  let reassoc : ((U × I) × Y) ≃ₜ ((U × Y) × I) :=
    (Homeomorph.prodAssoc U I Y).trans <|
      ((Homeomorph.refl U).prodCongr (Homeomorph.prodComm I Y)).trans <|
        (Homeomorph.prodAssoc U Y I).symm
  let base : (U ×ˢ (Set.univ : Set Y)) ≃ₜ U × Y :=
    (Homeomorph.Set.prod U Set.univ).trans <|
      (Homeomorph.refl U).prodCongr (Homeomorph.Set.univ Y)
  let K : (Prod.map f (id : Y → Y) ⁻¹' (U ×ˢ Set.univ)) ≃ₜ
      (U ×ˢ Set.univ) × I :=
    (Homeomorph.setCongr hpre).trans <|
      (Homeomorph.Set.prod (f ⁻¹' U) Set.univ).trans <|
        (H.prodCongr (Homeomorph.Set.univ Y)).trans <|
          reassoc.trans (base.symm.prodCongr (Homeomorph.refl I))
  refine ⟨hdisc, U ×ˢ Set.univ, ⟨hxU, Set.mem_univ _⟩, hU.prod isOpen_univ,
    hpre ▸ hfU.prod isOpen_univ, K, ?_⟩
  intro e
  change (K e).1.1 = Prod.map f id e
  apply Prod.ext
  · exact hH ⟨e.1.1, e.2.1⟩
  · rfl

/-! ## The standard phase covering -/

/-- The direction on the unit circle represented by a lifted phase. -/
noncomputable def phaseCircle (θ : ℝ) : Circle := Circle.exp (Real.pi * θ)

theorem phaseCircle_isCoveringMap : IsCoveringMap phaseCircle := by
  have h := Circle.isCoveringMap_exp.comp_homeomorph
    (Homeomorph.mulLeft₀ Real.pi Real.pi_ne_zero)
  change IsCoveringMap (fun θ : ℝ ↦ Circle.exp (Real.pi * θ))
  simpa [Function.comp_def, Homeomorph.coe_mulLeft₀] using h

/-- The standard product covering in the global coordinates. -/
noncomputable def coordinateProjection : GLTildeCoordinates → GLPosCoordinates :=
  Prod.map phaseCircle id

theorem coordinateProjection_isCoveringMap : IsCoveringMap coordinateProjection := by
  exact isCoveringMap_prodMap_id phaseCircle_isCoveringMap

/-! ## Conjugating the matrix projection to the standard cover -/

theorem phaseCircle_coe (θ : ℝ) : ((phaseCircle θ : Circle) : ℂ) =
    Real.cos (Real.pi * θ) + Real.sin (Real.pi * θ) * I := by
  change Complex.exp ((Real.pi * θ : ℝ) * I) =
    Real.cos (Real.pi * θ) + Real.sin (Real.pi * θ) * I
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

@[simp]
theorem circleMatrix_phaseCircle (θ : ℝ) :
    circleMatrix (phaseCircle θ) = rotationMatrix θ := by
  have hre : ((phaseCircle θ : Circle) : ℂ).re = Real.cos (Real.pi * θ) := by
    change (Complex.exp (((Real.pi * θ : ℝ) : ℂ) * I)).re = Real.cos (Real.pi * θ)
    exact Complex.exp_ofReal_mul_I_re _
  have him : ((phaseCircle θ : Circle) : ℂ).im = Real.sin (Real.pi * θ) := by
    change (Complex.exp (((Real.pi * θ : ℝ) : ℂ) * I)).im = Real.sin (Real.pi * θ)
    exact Complex.exp_ofReal_mul_I_im _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [circleMatrix, rotationMatrix, hre, him]

theorem glPosOfCoordinates_coordinateProjection (c : GLTildeCoordinates) :
    glPosOfCoordinates (coordinateProjection c) = (glTildeOfCoordinates c).mat := by
  apply Subtype.ext
  apply Units.ext
  change toMat (glPosOfCoordinates (coordinateProjection c)) =
    toMat (glTildeOfCoordinates c).mat
  rw [glPosOfCoordinates_mat, glTildeOfCoordinates_mat]
  simp [coordinateProjection, matrixOfCoordinates, Prod.map]

theorem coordinateProjection_apply_glTildeCoordinates (x : GLTilde) :
    coordinateProjection (glTildeCoordinateHomeomorph x) =
      glPosCoordinateHomeomorph x.mat := by
  apply glPosCoordinateHomeomorph.symm.injective
  rw [glPosCoordinateHomeomorph.symm_apply_apply]
  change glPosOfCoordinates (coordinateProjection (glTildeCoordinates x)) = x.mat
  rw [glPosOfCoordinates_coordinateProjection]
  exact congrArg GLTilde.mat (glTildeOfCoordinates_coordinates x)

/-- The matrix projection is a covering map for the global-coordinate topology. -/
theorem GLTilde.isCoveringMap_toMat : IsCoveringMap GLTilde.mat := by
  have h := (coordinateProjection_isCoveringMap.comp_homeomorph
    glTildeCoordinateHomeomorph).homeomorph_comp glPosCoordinateHomeomorph.symm
  convert h using 1
  funext x
  apply glPosCoordinateHomeomorph.injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  exact (coordinateProjection_apply_glTildeCoordinates x).symm

/-- The data comprising the universal-cover statement: the matrix projection
is a surjective covering map and its source is simply connected. -/
@[discharges "gltilde-universal-cover"]
theorem GLTilde.universalCoverData :
    IsCoveringMap GLTilde.mat ∧
      Function.Surjective GLTilde.mat ∧ SimplyConnectedSpace GLTilde :=
  ⟨GLTilde.isCoveringMap_toMat, toMatHom_surjective, inferInstance⟩

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
