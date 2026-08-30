/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.GLTilde.Covering.Surjectivity
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Source topology and simple connectedness of the lifted group

This file begins the topological half of the universal-cover theorem.  The
group-theoretic half is in `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Fibre.lean` and `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Surjectivity.lean`.

The useful coordinates do not require a computation of `π₁(S¹)`.  If
`x = (T, f) : GLTilde`, rotate the first column of `T` backwards through the
lifted angle `f(0)`.  Compatibility says that the resulting matrix has the
form

```
  !![r, b; 0, d]     with r > 0 and d > 0.
```

Conversely, an angle and such an upper-triangular matrix determine a unique
compatible lift.  Thus `GLTilde` has global coordinates

```
  ℝ × (0, ∞) × ℝ × (0, ∞),
```

which are contractible.  We transport the product topology through this
coordinate equivalence and obtain `ContractibleSpace GLTilde`, hence
`SimplyConnectedSpace GLTilde`.

`WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Map.lean` continues from these coordinates, gives global circle
coordinates on `GL⁺(2, ℝ)`, and proves that the matrix projection is a
covering map. `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Topology/Group.lean` then proves that multiplication
and inversion are continuous for the transported topology.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open Matrix Real Set

/-! ## Rotations and lifted rotations -/

/-- Counterclockwise rotation through angle `π θ`. -/
noncomputable def rotationMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (Real.pi * θ), -Real.sin (Real.pi * θ);
     Real.sin (Real.pi * θ),  Real.cos (Real.pi * θ)]

@[simp]
theorem rotationMatrix_det (θ : ℝ) : (rotationMatrix θ).det = 1 := by
  simp [rotationMatrix, Matrix.det_fin_two_of]
  nlinarith [Real.sin_sq_add_cos_sq (Real.pi * θ)]

theorem rotationMatrix_mulVec_rayVec (θ φ : ℝ) :
    rotationMatrix θ *ᵥ rayVec φ = rayVec (φ + θ) := by
  ext i
  fin_cases i <;>
    simp [rotationMatrix, rayVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      mul_add, Real.cos_add, Real.sin_add] <;> ring

@[simp]
theorem rotationMatrix_neg_mul (θ : ℝ) :
    rotationMatrix (-θ) * rotationMatrix θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg,
      Real.sin_neg] <;>
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * θ)]

@[simp]
theorem rotationMatrix_mul_neg (θ : ℝ) :
    rotationMatrix θ * rotationMatrix (-θ) = 1 := by
  simpa only [neg_neg] using rotationMatrix_neg_mul (-θ)

/-- Rotation as an element of `GL⁺(2, ℝ)`. -/
noncomputable def rotationGLPos (θ : ℝ) : Matrix.GLPos (Fin 2) ℝ :=
  ⟨⟨rotationMatrix θ, rotationMatrix (-θ),
      rotationMatrix_mul_neg θ, rotationMatrix_neg_mul θ⟩,
    by simp⟩

@[simp]
theorem rotationGLPos_mat (θ : ℝ) : toMat (rotationGLPos θ) = rotationMatrix θ := rfl

/-- Translation of the phase line through `θ`. -/
def phaseTranslation (θ : ℝ) : NormalizedShift where
  toOrderIso := OrderIso.addRight θ
  map_add_one φ := by simp [OrderIso.addRight]; ring

@[simp]
theorem phaseTranslation_apply (θ φ : ℝ) :
    (phaseTranslation θ).toOrderIso φ = φ + θ := rfl

theorem compatible_rotation (θ : ℝ) : Compatible (rotationGLPos θ) (phaseTranslation θ) := by
  intro φ
  rw [rotationGLPos_mat, rotationMatrix_mulVec_rayVec, phaseTranslation_apply]
  exact OnRay.refl _

/-- Rotation together with its tautological lift to the phase line. -/
noncomputable def liftedRotation (θ : ℝ) : GLTilde :=
  ⟨rotationGLPos θ, phaseTranslation θ, compatible_rotation θ⟩

@[simp] theorem liftedRotation_mat (θ : ℝ) : (liftedRotation θ).mat = rotationGLPos θ := rfl
@[simp] theorem liftedRotation_shift_zero (θ : ℝ) :
    (liftedRotation θ).shift.toOrderIso 0 = θ := by simp [liftedRotation]

/-! ## A lift is determined by its matrix and one lifted phase -/

/-- Two compatible lifts of the same matrix agreeing at phase zero are equal.

The unique deck-factorisation reduces this to injectivity of `ℤ → ℝ`. -/
theorem GLTilde.ext_mat_shift_zero {x y : GLTilde} (hmat : x.mat = y.mat)
    (hzero : x.shift.toOrderIso 0 = y.shift.toOrderIso 0) : x = y := by
  obtain ⟨m, hxm, -⟩ := existsUnique_deck_mul_sect x
  obtain ⟨n, hyn, -⟩ := existsUnique_deck_mul_sect y
  have hxm0 := congrArg (fun z : GLTilde => z.shift.toOrderIso 0) hxm
  have hyn0 := congrArg (fun z : GLTilde => z.shift.toOrderIso 0) hyn
  simp only [GLTilde.mul_shift, NormalizedShift.mul_apply, deck_shift, deckShift_apply,
    sect, liftShift_apply] at hxm0 hyn0
  have hmnR : (m : ℝ) = (n : ℝ) := by
    rw [hmat] at hxm0
    linarith
  have hmn : m = n := by exact_mod_cast hmnR
  rw [hxm, hyn, hmat, hmn]

/-! ## Upper-triangular representatives -/

/-- Positive real numbers, with their standard subspace topology. -/
abbrev PositiveReal := Set.Ioi (0 : ℝ)

/-- Global coordinates for `GLTilde`: angle, first diagonal, shear, second diagonal. -/
abbrev GLTildeCoordinates := ℝ × PositiveReal × ℝ × PositiveReal

/-- The upper-triangular matrix represented by the last three coordinates. -/
def upperMatrix (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![(r : ℝ), b; 0, (d : ℝ)]

@[simp]
theorem upperMatrix_det (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    (upperMatrix r b d).det = (r : ℝ) * d := by
  simp [upperMatrix, Matrix.det_fin_two_of]

/-- The explicit inverse of `upperMatrix`. -/
noncomputable def upperMatrixInv (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![(r : ℝ)⁻¹, -((r : ℝ)⁻¹ * b * (d : ℝ)⁻¹); 0, (d : ℝ)⁻¹]

@[simp]
theorem upperMatrix_mul_inv (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    upperMatrix r b d * upperMatrixInv r b d = 1 := by
  have hr : (r : ℝ) ≠ 0 := ne_of_gt r.2
  have hd : (d : ℝ) ≠ 0 := ne_of_gt d.2
  ext i j
  all_goals fin_cases i <;> fin_cases j
  all_goals simp [upperMatrix, upperMatrixInv, Matrix.mul_apply, Fin.sum_univ_two, hr, hd]
  field_simp
  ring

@[simp]
theorem upperMatrix_inv_mul (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    upperMatrixInv r b d * upperMatrix r b d = 1 := by
  have hr : (r : ℝ) ≠ 0 := ne_of_gt r.2
  have hd : (d : ℝ) ≠ 0 := ne_of_gt d.2
  ext i j
  all_goals fin_cases i <;> fin_cases j
  all_goals simp [upperMatrix, upperMatrixInv, Matrix.mul_apply, Fin.sum_univ_two, hr, hd]

/-- A positive-diagonal upper-triangular matrix as an element of `GL⁺(2, ℝ)`. -/
noncomputable def upperGLPos (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    Matrix.GLPos (Fin 2) ℝ :=
  ⟨⟨upperMatrix r b d, upperMatrixInv r b d,
      upperMatrix_mul_inv r b d, upperMatrix_inv_mul r b d⟩,
    by simpa [upperMatrix_det] using mul_pos r.2 d.2⟩

@[simp]
theorem upperGLPos_mat (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    toMat (upperGLPos r b d) = upperMatrix r b d := rfl

/-! ## Extracting coordinates -/

/-- Rotate the first column of `x.mat` back through its lifted phase at zero. -/
noncomputable def alignedMatrix (x : GLTilde) : Matrix (Fin 2) (Fin 2) ℝ :=
  rotationMatrix (-x.shift.toOrderIso 0) * toMat x.mat

private theorem alignedMatrix_firstColumn (x : GLTilde) :
    ∃ r : ℝ, 0 < r ∧ alignedMatrix x *ᵥ rayVec 0 = r • rayVec 0 := by
  obtain ⟨r, hr, hx⟩ := x.compat 0
  refine ⟨r, hr, ?_⟩
  rw [alignedMatrix, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul,
    rotationMatrix_mulVec_rayVec]
  simp

theorem alignedMatrix_zero_zero_pos (x : GLTilde) : 0 < alignedMatrix x 0 0 := by
  obtain ⟨r, hr, h⟩ := alignedMatrix_firstColumn x
  have h0 := congrFun h 0
  have h0' : alignedMatrix x 0 0 = r := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rayVec] using h0
  rwa [h0']

@[simp]
theorem alignedMatrix_one_zero (x : GLTilde) : alignedMatrix x 1 0 = 0 := by
  obtain ⟨r, -, h⟩ := alignedMatrix_firstColumn x
  have h1 := congrFun h 1
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rayVec] using h1

private theorem alignedMatrix_det (x : GLTilde) :
    (alignedMatrix x).det = (toMat x.mat).det := by
  rw [alignedMatrix, Matrix.det_mul, rotationMatrix_det, one_mul]

theorem alignedMatrix_one_one_pos (x : GLTilde) : 0 < alignedMatrix x 1 1 := by
  have hdet : 0 < (alignedMatrix x).det := by rw [alignedMatrix_det]; exact x.mat.2
  rw [Matrix.det_fin_two, alignedMatrix_one_zero, mul_zero, sub_zero] at hdet
  rcases mul_pos_iff.mp hdet with h | h
  · exact h.2
  · linarith [alignedMatrix_zero_zero_pos x]

/-- The global coordinate map. -/
noncomputable def glTildeCoordinates (x : GLTilde) : GLTildeCoordinates :=
  (x.shift.toOrderIso 0,
    ⟨alignedMatrix x 0 0, alignedMatrix_zero_zero_pos x⟩,
    alignedMatrix x 0 1,
    ⟨alignedMatrix x 1 1, alignedMatrix_one_one_pos x⟩)

/-- Rebuild the underlying matrix from the four coordinates. -/
noncomputable def matrixOfCoordinates (c : GLTildeCoordinates) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  rotationMatrix c.1 * upperMatrix c.2.1 c.2.2.1 c.2.2.2

private theorem alignedMatrix_eq_upper (x : GLTilde) :
    alignedMatrix x = upperMatrix (glTildeCoordinates x).2.1
      (glTildeCoordinates x).2.2.1 (glTildeCoordinates x).2.2.2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glTildeCoordinates, upperMatrix, alignedMatrix_one_zero]

theorem matrixOfCoordinates_apply (x : GLTilde) :
    matrixOfCoordinates (glTildeCoordinates x) = toMat x.mat := by
  rw [matrixOfCoordinates, ← alignedMatrix_eq_upper]
  simp only [glTildeCoordinates]
  rw [alignedMatrix, ← Matrix.mul_assoc, rotationMatrix_mul_neg, Matrix.one_mul]

/-! ## Reconstructing a lift from coordinates -/

private theorem upper_mulVec_rayVec_zero (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    upperMatrix r b d *ᵥ rayVec 0 = (r : ℝ) • rayVec 0 := by
  ext i
  fin_cases i <;>
    simp [upperMatrix, rayVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The canonical lift of a positive-diagonal upper-triangular matrix has an
even value at zero.  We will remove this deck displacement. -/
private theorem upper_lift_zero_even (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    ∃ n : ℤ, lift (upperGLPos r b d) 0 = 2 * n := by
  have hcompat := compatible_liftShift (upperGLPos r b d) 0
  rw [upperGLPos_mat, upper_mulVec_rayVec_zero] at hcompat
  obtain ⟨s, hs, hEq⟩ := hcompat
  have honRay : OnRay (rayVec 0) (rayVec (lift (upperGLPos r b d) 0)) := by
    refine ⟨s / (r : ℝ), div_pos hs r.2, ?_⟩
    ext i
    have hi := congrFun hEq i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    have hr : (r : ℝ) ≠ 0 := ne_of_gt r.2
    rw [div_mul_eq_mul_div, eq_div_iff hr]
    simpa [liftShift_apply, mul_comm] using hi
  have hRay : rayVec 0 = rayVec (lift (upperGLPos r b d) 0) :=
    rayVec_eq_of_onRay honRay
  obtain ⟨n, hn⟩ := (rayVec_eq_iff 0 (lift (upperGLPos r b d) 0)).mp hRay
  refine ⟨-n, ?_⟩
  push_cast
  linarith

/-- The deck displacement of the canonical upper-triangular lift. -/
noncomputable def upperDeckIndex (r : PositiveReal) (b : ℝ) (d : PositiveReal) : ℤ :=
  Classical.choose (upper_lift_zero_even r b d)

/-- The chosen deck index removes exactly the value at zero of the canonical
upper-triangular lift. -/
theorem upperDeckIndex_spec (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    lift (upperGLPos r b d) 0 = 2 * upperDeckIndex r b d :=
  Classical.choose_spec (upper_lift_zero_even r b d)

/-- The compatible lift of an upper-triangular matrix normalized to take `0`
to `0`. -/
noncomputable def upperSectionZero (r : PositiveReal) (b : ℝ) (d : PositiveReal) : GLTilde :=
  deck (-upperDeckIndex r b d) * sect (upperGLPos r b d)

@[simp]
theorem upperSectionZero_mat (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    (upperSectionZero r b d).mat = upperGLPos r b d := by
  simp [upperSectionZero]

@[simp]
theorem upperSectionZero_shift_zero (r : PositiveReal) (b : ℝ) (d : PositiveReal) :
    (upperSectionZero r b d).shift.toOrderIso 0 = 0 := by
  simp only [upperSectionZero, GLTilde.mul_shift, NormalizedShift.mul_apply, deck_shift,
    deckShift_apply, sect, liftShift_apply]
  rw [upperDeckIndex_spec]
  push_cast
  ring

/-- Reconstruct a compatible lift from its four global coordinates. -/
noncomputable def glTildeOfCoordinates (c : GLTildeCoordinates) : GLTilde :=
  liftedRotation c.1 * upperSectionZero c.2.1 c.2.2.1 c.2.2.2

@[simp]
theorem glTildeOfCoordinates_shift_zero (c : GLTildeCoordinates) :
    (glTildeOfCoordinates c).shift.toOrderIso 0 = c.1 := by
  simp [glTildeOfCoordinates]

theorem glTildeOfCoordinates_mat (c : GLTildeCoordinates) :
    toMat (glTildeOfCoordinates c).mat = matrixOfCoordinates c := by
  simp [glTildeOfCoordinates, matrixOfCoordinates, toMat_mul]

@[simp]
theorem alignedMatrix_glTildeOfCoordinates (c : GLTildeCoordinates) :
    alignedMatrix (glTildeOfCoordinates c) = upperMatrix c.2.1 c.2.2.1 c.2.2.2 := by
  rw [alignedMatrix, glTildeOfCoordinates_shift_zero, glTildeOfCoordinates_mat,
    matrixOfCoordinates, ← Matrix.mul_assoc, rotationMatrix_neg_mul, Matrix.one_mul]

@[simp]
theorem glTildeCoordinates_ofCoordinates (c : GLTildeCoordinates) :
    glTildeCoordinates (glTildeOfCoordinates c) = c := by
  rcases c with ⟨θ, r, b, d⟩
  apply Prod.ext
  · exact glTildeOfCoordinates_shift_zero _
  · apply Prod.ext
    · apply Subtype.ext
      simp [glTildeCoordinates, upperMatrix]
    · apply Prod.ext
      · simp [glTildeCoordinates, upperMatrix]
      · apply Subtype.ext
        simp [glTildeCoordinates, upperMatrix]

theorem glTildeCoordinates_injective : Function.Injective glTildeCoordinates := by
  intro x y hxy
  have hmat0 : toMat x.mat = toMat y.mat := by
    rw [← matrixOfCoordinates_apply x, ← matrixOfCoordinates_apply y, hxy]
  have hmat : x.mat = y.mat := by
    apply Subtype.ext
    exact Units.ext hmat0
  apply GLTilde.ext_mat_shift_zero hmat
  exact congrArg _root_.Prod.fst hxy

theorem glTildeCoordinates_surjective : Function.Surjective glTildeCoordinates :=
  fun c => ⟨glTildeOfCoordinates c, glTildeCoordinates_ofCoordinates c⟩

/-- The global coordinate equivalence for `GLTilde`. -/
noncomputable def glTildeCoordinateEquiv : GLTilde ≃ GLTildeCoordinates :=
  Equiv.ofBijective glTildeCoordinates
    ⟨glTildeCoordinates_injective, glTildeCoordinates_surjective⟩

@[simp]
theorem glTildeCoordinateEquiv_apply (x : GLTilde) :
    glTildeCoordinateEquiv x = glTildeCoordinates x := rfl

/-! ## Topology and simple connectedness -/

/-- The topology transported from
`ℝ × (0,∞) × ℝ × (0,∞)` by the global coordinate equivalence. -/
noncomputable instance GLTilde.topologicalSpace : TopologicalSpace GLTilde :=
  TopologicalSpace.induced glTildeCoordinateEquiv inferInstance

/-- The global coordinates as a homeomorphism. -/
noncomputable def glTildeCoordinateHomeomorph : GLTilde ≃ₜ GLTildeCoordinates :=
  glTildeCoordinateEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

/-- Rotation matrices depend continuously on their lifted angle. -/
theorem continuous_rotationMatrix : Continuous rotationMatrix := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rotationMatrix] <;> fun_prop

private theorem continuous_matrixOfCoordinates : Continuous matrixOfCoordinates := by
  apply Continuous.matrix_mul
  · exact continuous_rotationMatrix.comp continuous_fst
  · apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j <;> simp [upperMatrix] <;> fun_prop

private theorem continuous_glTildeOfCoordinates_mat :
    Continuous fun c : GLTildeCoordinates => (glTildeOfCoordinates c).mat := by
  rw [continuous_induced_rng, Units.continuous_iff]
  constructor
  · change Continuous fun c => toMat (glTildeOfCoordinates c).mat
    simpa only [glTildeOfCoordinates_mat] using continuous_matrixOfCoordinates
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
      simp [glTildeOfCoordinates, liftedRotation, rotationGLPos, upperSectionZero,
        upperGLPos, upperMatrixInv, rotationMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;>
      fun_prop

@[simp]
theorem glTildeOfCoordinates_coordinates (x : GLTilde) :
    glTildeOfCoordinates (glTildeCoordinates x) = x := by
  apply glTildeCoordinates_injective
  simp

/-- The matrix projection is continuous for the global-coordinate topology. -/
theorem GLTilde.continuous_toMat : Continuous GLTilde.mat := by
  have h := continuous_glTildeOfCoordinates_mat.comp glTildeCoordinateHomeomorph.continuous
  have heq : (fun c : GLTildeCoordinates => (glTildeOfCoordinates c).mat) ∘
      glTildeCoordinateHomeomorph = GLTilde.mat := by
    funext x
    exact congrArg GLTilde.mat (glTildeOfCoordinates_coordinates x)
  rw [heq] at h
  exact h

noncomputable instance GLTilde.contractibleSpace : ContractibleSpace GLTilde := by
  letI : ContractibleSpace PositiveReal :=
    (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by simp⟩
  exact glTildeCoordinateHomeomorph.contractibleSpace

/-- **The space underlying Bridgeland's pair presentation is simply
connected.**

This proves the formerly missing simple-connectedness fact.  The covering-map
theorem is proved separately in `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Map.lean`. -/
noncomputable instance GLTilde.simplyConnectedSpace : SimplyConnectedSpace GLTilde :=
  SimplyConnectedSpace.ofContractible GLTilde

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
