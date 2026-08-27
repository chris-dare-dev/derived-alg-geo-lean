/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.RankOne

/-!
# The projective-plane numerical model

A second model of `NumericalVarietyData` in dimension two, with a **nontrivial canonical class**.

That is the point of it. The K3 model has `td₁ = 0`, so the `∫_X c₁(E)·td₁(X)` term of
`Surface.chi_eq` is multiplied by zero there and a sign error in it would go undetected. On
`ℙ²`, `K = −3H` gives `td₁ = −K/2 = (3/2)H`, and the term carries weight.

The model: `Pic ℙ² = ℤ·H` with `H² = 1`, and

`td(ℙ²) = 1 + (3/2)·H + H²`,  so  `∫ td₂ = χ(O_{ℙ²}) = 1`.

## The lattice

`ch₂` is a **half-integer** on `ℙ²`: `ch₂ = (c₁² − 2c₂)/2`, which is odd over two whenever
`c₁` is odd. So `N` cannot be `ℤ³` with `ch₂` as the third coordinate and still have `χ`
land in `ℤ`. The numerical Grothendieck group is the sublattice where `3c₁ + 2ch₂` is even;
substituting `2ch₂ = c₁ + 2v` parametrises it by `ℤ³` again, and this model uses those
coordinates:

`(r, c, v)  ↦  ch = r + c·H + (c/2 + v)·H²`,  `χ = r + 2c + v`.

The check that the parametrisation is right is `p2Chi_lineBundle`: it recovers
`χ(O(nH)) = (n+1)(n+2)/2`.
-/

open Polynomial Submodule Set

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- Chern-character coefficients on `ℙ²`. The half-integer in codimension two is what forces
the `(r, c, v)` coordinates — see the module docstring. -/
noncomputable def p2ChCoeff (E : SurfaceNum) : ℕ → ℚ
  | 0 => (E 0 : ℚ)
  | 1 => (E 1 : ℚ)
  | 2 => (E 1 : ℚ) / 2 + (E 2 : ℚ)
  | _ + 3 => 0

theorem p2ChCoeff_add (E F : SurfaceNum) (i : ℕ) :
    p2ChCoeff (E + F) i = p2ChCoeff E i + p2ChCoeff F i := by
  match i with
  | 0 | 1 => simp only [p2ChCoeff, Pi.add_apply, Int.cast_add]
  | 2 =>
    simp only [p2ChCoeff, Pi.add_apply, Int.cast_add]
    ring
  | _ + 3 => simp only [p2ChCoeff, add_zero]

/-- The Todd class of `ℙ²`: `td₁ = −K/2 = (3/2)H` and `td₂ = H²`, so `∫ td₂ = χ(O) = 1`. -/
noncomputable def p2Todd : ℕ → SurfaceRing
  | 0 => 1
  | 1 => algebraMap ℚ SurfaceRing (3 / 2) * H
  | 2 => H ^ 2
  | _ + 3 => 0

theorem p2Todd_mem (i : ℕ) : p2Todd i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 => exact surface_one_mem
  | 1 => exact algebraMap_mul_mem _ H_mem_piece_one
  | 2 => exact Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

theorem p2Todd_sum :
    (∑ j ∈ Finset.range (2 + 1), p2Todd j)
      = 1 + algebraMap ℚ SurfaceRing (3 / 2) * H + algebraMap ℚ SurfaceRing 1 * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp [p2Todd]

/-- `∫_{ℙ²} td₂ = χ(O_{ℙ²}) = 1`. -/
theorem p2_chi_structureSheaf : surfaceDegree 1 (p2Todd 2) = 1 := by
  show surfaceDegree 1 (H ^ 2) = 1
  rw [surfaceDegree_Hsq]

/-- The Euler characteristic on `ℙ²`, in the `(r, c, v)` coordinates. -/
def p2Chi (E : SurfaceNum) : ℤ := E 0 + 2 * E 1 + E 2

/-- **The model.** `ℙ²`, with `H² = 1` and `td = 1 + (3/2)H + H²`. -/
@[reducible]
noncomputable def p2NumericalVariety : NumericalVarietyData 2 SurfaceRing SurfaceNum where
  ring := surfaceNumericalRing 1
  rank := { toFun := fun E => E 0, map_zero' := rfl, map_add' := fun _ _ => rfl }
  chComp := surfaceCh p2ChCoeff
  chComp_mem := surfaceCh_mem p2ChCoeff
  chComp_zero := fun _ => rfl
  chComp_add := surfaceCh_add p2ChCoeff p2ChCoeff_add
  toddComp := p2Todd
  toddComp_mem := p2Todd_mem
  toddComp_zero := rfl
  chi :=
    { toFun := p2Chi
      map_zero' := rfl
      map_add' := by
        intro a b
        show a 0 + b 0 + 2 * (a 1 + b 1) + (a 2 + b 2)
          = (a 0 + 2 * a 1 + a 2) + (b 0 + 2 * b 1 + b 2)
        ring }

/-- The explicit projective-plane presentation satisfies Hirzebruch--Riemann--Roch. -/
theorem p2NumericalVariety_satisfiesHRR : p2NumericalVariety.SatisfiesHRR := by
  refine ⟨fun E => ?_⟩
  show ((p2Chi E : ℤ) : ℚ) = surfaceDegree 1 _
  rw [surfaceCh_sum, p2Todd_sum, surfaceDegree_ch_mul_todd]
  show ((E 0 + 2 * E 1 + E 2 : ℤ) : ℚ)
    = 1 * ((E 0 : ℚ) * 1 + (E 1 : ℚ) * (3 / 2) + ((E 1 : ℚ) / 2 + (E 2 : ℚ)))
  push_cast
  ring

/-- **Riemann–Roch on `ℙ²` reproduces `χ(O(nH)) = (n+1)(n+2)/2`.**

`O(nH)` is the class `(1, n, m)` with `2m = n(n−1)`: its Chern character is
`1 + nH + (n²/2)H²`, and this model records `ch₂ = c/2 + v`. Stated doubled to stay in `ℤ`.

This is the check that `Surface.chi_eq`'s `c₁·td₁` term is right — the K3 model, where
`td₁ = 0`, cannot see it. -/
theorem p2Chi_lineBundle (n m : ℤ) (hm : 2 * m = n * (n - 1)) :
    2 * p2Chi ![1, n, m] = (n + 1) * (n + 2) := by
  show 2 * (1 + 2 * n + m) = (n + 1) * (n + 2)
  linear_combination hm

/-- The class `(1, n, m)` with `2m = n(n−1)` really has `ch₂ = n²/2`, i.e. really is
`O(nH)`. Without this, `p2Chi_lineBundle` would only be arithmetic about a triple. -/
theorem p2ChCoeff_lineBundle (n m : ℤ) (hm : 2 * m = n * (n - 1)) :
    p2ChCoeff ![1, n, m] 2 = (n : ℚ) ^ 2 / 2 := by
  show (n : ℚ) / 2 + (m : ℚ) = (n : ℚ) ^ 2 / 2
  have h : (2 : ℚ) * (m : ℚ) = (n : ℚ) * ((n : ℚ) - 1) := by exact_mod_cast hm
  linarith

end Examples

end AlgebraicGeometry.Numerical
