/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.Slope
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.K3

/-! # The slope API on the rank-one K3 model -/

namespace AlgebraicGeometry.Numerical.Examples

/-- The hyperplane class as a polarisation of the K3 numerical ring. -/
noncomputable def k3Polarization (d : ℕ) (hd : d ≠ 0) :
    Polarization (surfaceNumericalRing (2 * (d : ℚ))) where
  cls := H
  cls_mem := H_mem_piece_one
  degree_pow_pos := by
    have : (surfaceNumericalRing (2 * (d : ℚ))).degree (H ^ 2) = 2 * (d : ℚ) :=
      surfaceDegree_Hsq _
    rw [this]
    have : (0 : ℚ) < (d : ℚ) := by
      exact_mod_cast Nat.pos_of_ne_zero hd
    linarith

/-- The `H`-degree on the K3 model is `2d` times the `ch₁` coefficient. -/
theorem degH_k3 (d : ℕ) (hd : d ≠ 0) (E : SurfaceNum) :
    degH (k3NumericalVariety d) (k3Polarization d hd) E = 2 * (d : ℚ) * (E 1 : ℚ) := by
  show (surfaceNumericalRing (2 * (d : ℚ))).degree
      (algebraMap ℚ SurfaceRing (k3ChCoeff E 1) * H * H ^ 1) = _
  rw [pow_one, mul_assoc, ← pow_two,
    NumericalRingData.degree_algebraMap_mul, surfaceDegree_Hsq]
  show (E 1 : ℚ) * (2 * (d : ℚ)) = _
  ring

end AlgebraicGeometry.Numerical.Examples
