/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.K3
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.RankOne

/-!
# A K3 surface of Picard rank one

The first model of `NumericalVarietyData` in dimension two. Before it, every statement in
`DerivedAlgGeo/AlgebraicGeometry/Numerical/Specializations/Surface.lean` and
`DerivedAlgGeo/AlgebraicGeometry/Numerical/RiemannRoch/K3.lean` was conditional on a
`NumericalVarietyData 2 A N` existing at all — only the dimension-zero point had been exhibited.

The surface is a K3 `X` with `Pic X = ℤ·H` and `H² = 2d`. The ring, grading and degree map
come from `Numerical/Examples/Surface/RankOne.lean`; all this file supplies is the Todd class

`td(X) = 1 + 0 + (1/d)·H²`,

so that `td₁ = 0` and `∫_X td₂ = 2` — which is exactly `K3.IsK3`, proved here rather than
assumed.

`d` is a parameter, not fixed to 1: the Bridgeland wall structure on a K3 depends on the
degree. It is a natural number rather than a rational because `χ` must land in `ℤ` —
Riemann–Roch on this model reads `χ(r, c, s) = 2r + 2ds`.
-/

open Polynomial Submodule Set

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- Chern-character coefficients: the class `(r, c, s)` has `ch = r + c·H + s·H²`. -/
noncomputable def k3ChCoeff (E : SurfaceNum) : ℕ → ℚ
  | 0 => (E 0 : ℚ)
  | 1 => (E 1 : ℚ)
  | 2 => (E 2 : ℚ)
  | _ + 3 => 0

theorem k3ChCoeff_add (E F : SurfaceNum) (i : ℕ) :
    k3ChCoeff (E + F) i = k3ChCoeff E i + k3ChCoeff F i := by
  match i with
  | 0 | 1 => simp only [k3ChCoeff, Pi.add_apply, Int.cast_add]
  | 2 => simp only [k3ChCoeff, Pi.add_apply, Int.cast_add]
  | _ + 3 => simp only [k3ChCoeff, add_zero]

/-- The Todd class of a K3: `td₁ = 0`, and `td₂` normalised so that `∫_X td₂ = 2`. -/
noncomputable def k3Todd (d : ℚ) : ℕ → SurfaceRing
  | 0 => 1
  | 1 => 0
  | 2 => algebraMap ℚ SurfaceRing (1 / d) * H ^ 2
  | _ + 3 => 0

theorem k3Todd_mem (d : ℚ) (i : ℕ) :
    k3Todd d i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 => exact surface_one_mem
  | 1 => exact Submodule.zero_mem _
  | 2 => exact algebraMap_mul_mem _ Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

theorem k3Todd_sum (d : ℚ) :
    (∑ j ∈ Finset.range (2 + 1), k3Todd d j)
      = 1 + algebraMap ℚ SurfaceRing 0 * H + algebraMap ℚ SurfaceRing (1 / d) * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp [k3Todd]

/-- **The model.** A K3 surface of degree `H² = 2d`, `d > 0`. -/
@[reducible]
noncomputable def k3NumericalVariety (d : ℕ) :
    NumericalVarietyData 2 SurfaceRing SurfaceNum where
  ring := surfaceNumericalRing (2 * (d : ℚ))
  rank := { toFun := fun E => E 0, map_zero' := rfl, map_add' := fun _ _ => rfl }
  chComp := surfaceCh k3ChCoeff
  chComp_mem := surfaceCh_mem k3ChCoeff
  chComp_zero := fun _ => rfl
  chComp_add := surfaceCh_add k3ChCoeff k3ChCoeff_add
  toddComp := k3Todd (d : ℚ)
  toddComp_mem := k3Todd_mem (d : ℚ)
  toddComp_zero := rfl
  chi :=
    { toFun := fun E => 2 * E 0 + 2 * (d : ℤ) * E 2
      map_zero' := by simp
      map_add' := by intro a b; show 2 * (a 0 + b 0) + 2 * (d : ℤ) * (a 2 + b 2) = _; ring }

/-- The explicit K3 presentation satisfies Hirzebruch--Riemann--Roch. -/
theorem k3NumericalVariety_satisfiesHRR (d : ℕ) (hd : d ≠ 0) :
    (k3NumericalVariety d).SatisfiesHRR := by
  refine ⟨fun E => ?_⟩
  show ((2 * E 0 + 2 * (d : ℤ) * E 2 : ℤ) : ℚ) = surfaceDegree (2 * (d : ℚ)) _
  rw [surfaceCh_sum, k3Todd_sum, surfaceDegree_ch_mul_todd]
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  show _ = 2 * (d : ℚ) * ((E 0 : ℚ) * (1 / (d : ℚ)) + (E 1 : ℚ) * 0 + (E 2 : ℚ))
  push_cast
  field_simp
  ring

/-- The model really is a K3: `td₁ = 0` and `∫_X td₂ = χ(O_X) = 2`.

With this presentation and its two property witnesses, every theorem in
`DerivedAlgGeo/AlgebraicGeometry/Numerical/RiemannRoch/K3.lean` — Riemann–Roch, the Mukai
self-pairing, `⟨v,v⟩ = ∫Δ − 2r²` — is a statement about an object that exists. -/
theorem k3_isK3 (d : ℕ) (hd : d ≠ 0) :
    K3.IsK3 (k3NumericalVariety d) := by
  refine ⟨rfl, ?_⟩
  show surfaceDegree (2 * (d : ℚ)) (algebraMap ℚ SurfaceRing (1 / (d : ℚ)) * H ^ 2) = 2
  rw [surfaceDegree_algebraMap_mul, surfaceDegree_Hsq]
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  field_simp

end Examples

end AlgebraicGeometry.Numerical
