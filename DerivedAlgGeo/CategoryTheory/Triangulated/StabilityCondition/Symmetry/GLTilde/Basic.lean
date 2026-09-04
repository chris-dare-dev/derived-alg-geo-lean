/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.NormalizedShift
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The lifted general linear group as compatible pairs

Bridgeland presents the universal cover of `GL⁺(2, ℝ)` concretely, as pairs
`(T, f)` with `T ∈ GL⁺(2, ℝ)` and `f` a normalized shift, subject to `T` and
`f` inducing the same map on the circle of phases.

The circle is `ℝ / 2ℤ`, embedded in `ℝ²` by `φ ↦ (cos πφ, sin πφ)`. The factor
`π` (not `2π`) is Bridgeland's phase convention: a semistable object of phase
`φ` has central charge on the ray at angle `πφ`, so `φ ↦ φ + 1` is the
antipodal map — the shift functor `[1]`. `rayVec_add_one` below is exactly
that statement, and it is the reason `NormalizedShift` demands
`f (φ + 1) = f φ + 1`.

"Same map on the circle" is then: `T` sends the ray through `rayVec φ` to the
ray through `rayVec (f φ)`.

## What is proved across this development

This file proves that the compatible pairs form a group under componentwise
multiplication, and that the type is nonempty (`compat_one` is the witness).
The companion files prove the covering-space properties:

* **Fibre `ℤ`** — **proved**, in `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Fibre.lean`. The kernel of the
  projection is exactly the deck transformations `φ ↦ φ + 2n`.
* **Surjectivity of the projection** — **proved**, in `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Surjectivity.lean`. Every
  `T` of positive determinant carries a compatible phase relabelling.
* **Simple connectedness** — **proved**, in `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/SourceTopology.lean`, by global
  coordinates `ℝ × (0,∞) × ℝ × (0,∞)` and contractibility.
* **Covering-map property** — **proved**, in `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Covering/Map.lean`. Global base
  coordinates identify the projection with the standard exponential cover
  `ℝ → S¹` times an identity map.

Thus `GLTilde.universalCoverData` packages the surjective covering-map and
simple-connectedness properties, while `exact_deckHom_toMatHom` packages the
extension with fibre `ℤ`. `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Topology/Group.lean` proves continuity of
multiplication and inversion and installs `IsTopologicalGroup GLTilde`.

The `WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Action/PreStability.lean` and
`WeakStabilityCondition/StabilityCondition/Symmetry/GLTilde/Action/Stability.lean` files use this
group to define and prove the action on stability conditions.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open Matrix Real

/-! ## The phase circle -/

/-- The unit vector at phase `φ`: the ray at angle `π φ`.

The `π`, rather than `2π`, is Bridgeland's phase convention — see the module
docstring. -/
noncomputable def rayVec (φ : ℝ) : Fin 2 → ℝ :=
  ![Real.cos (π * φ), Real.sin (π * φ)]

/-- Advancing the phase by one is the antipodal map.

This is the compatibility between `NormalizedShift`'s `+1`-equivariance and
the shift functor `[1]`: adding `1` to a phase negates the central charge. -/
theorem rayVec_add_one (φ : ℝ) : rayVec (φ + 1) = -rayVec φ := by
  ext i
  fin_cases i <;>
    simp [rayVec, mul_add, mul_one, Real.cos_add_pi, Real.sin_add_pi]

/-- Phase vectors are never zero, so they really do determine rays. -/
theorem rayVec_ne_zero (φ : ℝ) : rayVec φ ≠ 0 := by
  intro h
  have hc : Real.cos (π * φ) = 0 := congrFun h 0
  have hs : Real.sin (π * φ) = 0 := congrFun h 1
  have hpyth := Real.sin_sq_add_cos_sq (π * φ)
  rw [hs, hc] at hpyth
  norm_num at hpyth

/-! ## Rays -/

/-- `v` lies on the same ray as `w`: a positive multiple of it.

Deliberately not Mathlib's `SameRay`, which admits the zero vector. Every
vector here is a `rayVec`, hence nonzero, and the strict version keeps the
closure proofs free of degenerate cases. -/
def OnRay (v w : Fin 2 → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ v = r • w

namespace OnRay

theorem refl (v : Fin 2 → ℝ) : OnRay v v :=
  ⟨1, one_pos, (one_smul ℝ v).symm⟩

theorem trans {u v w : Fin 2 → ℝ} (h₁ : OnRay u v) (h₂ : OnRay v w) :
    OnRay u w := by
  obtain ⟨r, hr, rfl⟩ := h₁
  obtain ⟨s, hs, rfl⟩ := h₂
  exact ⟨r * s, mul_pos hr hs, by rw [smul_smul]⟩

end OnRay

/-! ## Compatible pairs -/

/-- The matrix underlying an element of `GL⁺(2, ℝ)`. -/
def toMat (T : Matrix.GLPos (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ((T : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)

@[simp]
theorem toMat_mul (T U : Matrix.GLPos (Fin 2) ℝ) :
    toMat (T * U) = toMat T * toMat U := rfl

@[simp]
theorem toMat_one : toMat 1 = 1 := rfl

/-- `T` and `f` induce the same map on the circle of phases: `T` carries the
ray at phase `φ` to the ray at phase `f φ`. -/
def Compatible (T : Matrix.GLPos (Fin 2) ℝ) (f : NormalizedShift) : Prop :=
  ∀ φ : ℝ, OnRay (toMat T *ᵥ rayVec φ) (rayVec (f.toOrderIso φ))

theorem compat_one : Compatible 1 1 := by
  intro φ
  simp only [toMat_one, Matrix.one_mulVec, NormalizedShift.one_apply]
  exact OnRay.refl _

theorem compat_mul {T U : Matrix.GLPos (Fin 2) ℝ} {f g : NormalizedShift}
    (hT : Compatible T f) (hU : Compatible U g) :
    Compatible (T * U) (f * g) := by
  intro φ
  obtain ⟨s, hs, hUφ⟩ := hU φ
  obtain ⟨r, hr, hTφ⟩ := hT (g.toOrderIso φ)
  refine ⟨s * r, mul_pos hs hr, ?_⟩
  rw [NormalizedShift.mul_apply, toMat_mul, ← Matrix.mulVec_mulVec, hUφ,
    Matrix.mulVec_smul, hTφ, smul_smul]

theorem compat_inv {T : Matrix.GLPos (Fin 2) ℝ} {f : NormalizedShift}
    (hT : Compatible T f) : Compatible T⁻¹ f⁻¹ := by
  intro ψ
  obtain ⟨r, hr, hTφ⟩ := hT (f.toOrderIso.symm ψ)
  rw [OrderIso.apply_symm_apply] at hTφ
  refine ⟨r⁻¹, inv_pos.mpr hr, ?_⟩
  rw [NormalizedShift.inv_apply]
  -- Undo `T` by group multiplication rather than `Matrix.inv`: the nonsingular
  -- inverse never has to appear.
  have key : toMat T⁻¹ *ᵥ (toMat T *ᵥ rayVec (f.toOrderIso.symm ψ))
      = rayVec (f.toOrderIso.symm ψ) := by
    rw [Matrix.mulVec_mulVec, ← toMat_mul, inv_mul_cancel, toMat_one,
      Matrix.one_mulVec]
  rw [hTφ, Matrix.mulVec_smul] at key
  rw [← key, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-! ## The group -/

/-- `G̃L⁺(2, ℝ)` in Bridgeland's concrete presentation: a matrix of positive
determinant together with a phase relabelling that agrees with it on the
circle.

The covering-map and simple-connectedness properties are proved in the
companion topology files and packaged by `GLTilde.universalCoverData`. -/
structure GLTilde where
  /-- The linear part, acting on central charges. -/
  mat : Matrix.GLPos (Fin 2) ℝ
  /-- The phase relabelling, acting on slicings. -/
  shift : NormalizedShift
  /-- The two agree on the circle of phases. -/
  compat : Compatible mat shift

namespace GLTilde

variable {x y : GLTilde}

/-- `compat` is a `Prop`, so the two data fields determine the pair.

Named `ext'`: Lean auto-generates `GLTilde.ext` for the structure. -/
@[ext]
theorem ext' (hm : x.mat = y.mat) (hs : x.shift = y.shift) : x = y := by
  cases x
  cases y
  subst hm
  subst hs
  rfl

-- `noncomputable`: `Matrix.GLPos` membership is a `0 < det` condition, and
-- `ℝ`'s `LinearOrder` is noncomputable. Nothing here is meant to run.
noncomputable instance group : Group GLTilde where
  mul x y := ⟨x.mat * y.mat, x.shift * y.shift, compat_mul x.compat y.compat⟩
  one := ⟨1, 1, compat_one⟩
  inv x := ⟨x.mat⁻¹, x.shift⁻¹, compat_inv x.compat⟩
  mul_assoc _ _ _ := ext' (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul _ := ext' (one_mul _) (one_mul _)
  mul_one _ := ext' (mul_one _) (mul_one _)
  inv_mul_cancel _ := ext' (inv_mul_cancel _) (inv_mul_cancel _)

@[simp] theorem mul_mat (x y : GLTilde) : (x * y).mat = x.mat * y.mat := rfl
@[simp] theorem mul_shift (x y : GLTilde) : (x * y).shift = x.shift * y.shift := rfl
@[simp] theorem one_mat : (1 : GLTilde).mat = 1 := rfl
@[simp] theorem one_shift : (1 : GLTilde).shift = 1 := rfl
@[simp] theorem inv_mat (x : GLTilde) : x⁻¹.mat = x.mat⁻¹ := rfl
@[simp] theorem inv_shift (x : GLTilde) : x⁻¹.shift = x.shift⁻¹ := rfl

/-- Projection to the linear part. A group hom by construction. -/
def toMatHom : GLTilde →* Matrix.GLPos (Fin 2) ℝ where
  toFun := GLTilde.mat
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection to the phase relabelling. A group hom by construction.

Step 3 composes the `Slicing` action with this. -/
def toShiftHom : GLTilde →* NormalizedShift where
  toFun := GLTilde.shift
  map_one' := rfl
  map_mul' _ _ := rfl

end GLTilde

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
