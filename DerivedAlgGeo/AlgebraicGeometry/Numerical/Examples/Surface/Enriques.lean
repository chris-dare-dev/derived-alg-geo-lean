/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.Abelian

/-!
# A numerical Enriques surface of Picard rank one

The fourth surface model: the Todd class

`td(Y) = 1 + 0 + (1/(2d))·H²`,

so that `td₁ = 0` and `∫_Y td₂ = χ(O_Y) = 1` — strictly between the K3's `2`
and the abelian surface's `0`. Riemann–Roch on this model reads
`χ(r, c, s) = r + 2ds`.

## What the numerical shadow cannot see

On an Enriques surface `2K_Y = 0` with `K_Y ≠ 0` in `Pic` — the geometric
formulation is the business of the geometric surface lane, and no bridge from
this numerical model is claimed in either direction. Torsion dies in the
numerical quotient, so here `td₁ = -K/2` is *zero*, exactly as it is for the
abelian surface: `td₁` cannot detect the torsion —
`enriquesToddComp_one` and `abelianToddComp_one` are the same equation. What
separates the two models is `∫td₂ = 1` versus `0`, not anything `ω_Y`-shaped.

The carrier is the shared Picard-rank-one lattice of
`Examples/Surface/RankOne.lean` — "a new model costs a Todd class and nothing
else." A genuine Enriques surface has `Num(Y) = U ⊕ E₈(−1)` of rank ten; this
file is the rank-one slice spanned by a single polarisation class `H` with
`H² = 2d`, which is consistent because the Enriques lattice is even. The rank
ten lattice and its isotropic sequences are a separate lane. As
`AlgebraicGeometry/Surface/K3.lean` records for its own model in "What this
file does not do", the numerical-to-geometric bridge is
Hirzebruch–Riemann–Roch and does not exist at the pin.

The rank coefficient is `∫td₂ = 1` rather than the K3's `2` or the abelian
surface's `0`, so `χ` increases by exactly one when the rank does: `χ` is onto
`ℤ` here, lands in `2ℤ` on the K3 model, and cannot see the rank at all on
the abelian one.

## Main definitions

* `enriquesNumericalVariety` — the model.
* `k3EnriquesAbelianPresentations` — the three presentations on one carrier.

## Main results

* `enriquesNumericalVariety_satisfiesHRR` — the presentation satisfies HRR.
* `enriquesChiStructureSheaf` — `∫_Y td₂ = χ(O_Y) = 1`.
* `enriquesToddComp_one` — `td₁ = 0`: the canonical class is numerically
  trivial, though not trivial in `Pic`.
* the pairwise `χ(O)` distinctions `2 ≠ 1 ≠ 0` between the three rank-one
  models.

## References

* Li, Nuer, Stellari, Zhao, *A refined Derived Torelli Theorem for Enriques
  surfaces*, arXiv:1912.04332.
-/

open Polynomial Submodule Set
open DerivedAlgGeo.LinearAlgebra

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- The Todd class of an Enriques surface: `td₁ = 0` because the 2-torsion
canonical class is numerically trivial, and `td₂` normalised so that
`∫_Y td₂ = 1`. -/
noncomputable def enriquesTodd (d : ℚ) : ℕ → SurfaceRing
  | 0 => 1
  | 1 => 0
  | 2 => algebraMap ℚ SurfaceRing (1 / (2 * d)) * H ^ 2
  | _ + 3 => 0

theorem enriquesTodd_mem (d : ℚ) (i : ℕ) :
    enriquesTodd d i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 => exact surface_one_mem
  | 1 => exact Submodule.zero_mem _
  | 2 => exact algebraMap_mul_mem _ Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

theorem enriquesTodd_sum (d : ℚ) :
    (∑ j ∈ Finset.range (2 + 1), enriquesTodd d j)
      = 1 + algebraMap ℚ SurfaceRing 0 * H
        + algebraMap ℚ SurfaceRing (1 / (2 * d)) * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp [enriquesTodd]

/-- **The model.** A numerical Enriques surface with polarisation degree
`H² = 2d`, `d > 0`. -/
@[reducible]
noncomputable def enriquesNumericalVariety (d : ℕ) :
    NumericalVarietyData 2 SurfaceRing SurfaceNum where
  ring := surfaceNumericalRing (2 * (d : ℚ))
  rank := { toFun := fun E => E 0, map_zero' := rfl, map_add' := fun _ _ => rfl }
  chComp := surfaceCh k3ChCoeff
  chComp_mem := surfaceCh_mem k3ChCoeff
  chComp_zero := fun _ => rfl
  chComp_add := surfaceCh_add k3ChCoeff k3ChCoeff_add
  toddComp := enriquesTodd (d : ℚ)
  toddComp_mem := enriquesTodd_mem (d : ℚ)
  toddComp_zero := rfl
  chi :=
    { toFun := fun E => E 0 + 2 * (d : ℤ) * E 2
      map_zero' := by simp
      map_add' := by
        intro a b
        show (a 0 + b 0) + 2 * (d : ℤ) * (a 2 + b 2) = _
        ring }

/-- The explicit Enriques presentation satisfies Hirzebruch--Riemann--Roch:
the rank term survives with coefficient `∫td₂ = 1`.

`hd` is load-bearing, not bookkeeping: at `d = 0` the degree map is
`0 • coord` while `χ(E) = E 0`, so HRR is *false* there, not merely
unprovable. Contrast `abelianNumericalVariety_satisfiesHRR`, which needs no
such hypothesis because its `χ` degenerates with the degree. -/
theorem enriquesNumericalVariety_satisfiesHRR (d : ℕ) (hd : d ≠ 0) :
    (enriquesNumericalVariety d).SatisfiesHRR := by
  refine ⟨fun E => ?_⟩
  show ((E 0 + 2 * (d : ℤ) * E 2 : ℤ) : ℚ) = surfaceDegree (2 * (d : ℚ)) _
  rw [surfaceCh_sum, enriquesTodd_sum, surfaceDegree_ch_mul_todd]
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  show _ = 2 * (d : ℚ) * ((E 0 : ℚ) * (1 / (2 * (d : ℚ))) + (E 1 : ℚ) * 0 + (E 2 : ℚ))
  push_cast
  field_simp
  ring

/-- `td₁ = 0`: the 2-torsion canonical class of an Enriques surface is
numerically trivial. The same equation holds for the abelian model with a
different geometric reason behind it — see the module docstring. -/
theorem enriquesToddComp_one (d : ℕ) :
    (enriquesNumericalVariety d).toddComp 1 = 0 := rfl

/-- `∫_Y td₂ = χ(O_Y) = 1`. Stated as two theorems with `enriquesToddComp_one`
because — like abelian surfaces and unlike K3s — numerical Enriques surfaces
have no property class in this library to inhabit. `hd` is needed because
`(1/(2d)) · ∫H² = 1` fails at `d = 0`, where the degree map is zero. -/
theorem enriquesChiStructureSheaf (d : ℕ) (hd : d ≠ 0) :
    Surface.chiStructureSheaf (enriquesNumericalVariety d) = 1 := by
  show surfaceDegree (2 * (d : ℚ))
    (algebraMap ℚ SurfaceRing (1 / (2 * (d : ℚ))) * H ^ 2) = 1
  rw [surfaceDegree_algebraMap_mul, surfaceDegree_Hsq]
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  field_simp

/-- Three numerical presentations on the same carriers coexist as ordinary
data, extending `k3AndAbelianPresentations`. This is a regression test against
making any presentation a global instance. -/
noncomputable def k3EnriquesAbelianPresentations (d : ℕ) :
    NumericalVarietyData 2 SurfaceRing SurfaceNum ×
      NumericalVarietyData 2 SurfaceRing SurfaceNum ×
        NumericalVarietyData 2 SurfaceRing SurfaceNum :=
  (k3NumericalVariety d, enriquesNumericalVariety d, abelianNumericalVariety d)

/-- The Enriques and K3 models are provably different data: `1 ≠ 2`. -/
theorem chiStructureSheaf_enriques_ne_k3 (d : ℕ) (hd : d ≠ 0) :
    Surface.chiStructureSheaf (enriquesNumericalVariety d) ≠
      Surface.chiStructureSheaf (k3NumericalVariety d) := by
  rw [enriquesChiStructureSheaf d hd, k3ChiStructureSheaf d hd]
  norm_num

/-- The Enriques and abelian models are provably different data: `1 ≠ 0`.
This is the pair the `td₁ = 0` equation cannot separate, so `∫td₂` is the
*only* numerical invariant doing so. -/
theorem chiStructureSheaf_enriques_ne_abelian (d : ℕ) (hd : d ≠ 0) :
    Surface.chiStructureSheaf (enriquesNumericalVariety d) ≠
      Surface.chiStructureSheaf (abelianNumericalVariety d) := by
  rw [enriquesChiStructureSheaf d hd, abelianChiStructureSheaf d]
  norm_num

/-- The K3 and abelian models are provably different data: `2 ≠ 0`. Completes
the pairwise distinction of the three rank-one surface models. -/
theorem chiStructureSheaf_k3_ne_abelian (d : ℕ) (hd : d ≠ 0) :
    Surface.chiStructureSheaf (k3NumericalVariety d) ≠
      Surface.chiStructureSheaf (abelianNumericalVariety d) := by
  rw [k3ChiStructureSheaf d hd, abelianChiStructureSheaf d]
  norm_num

end Examples

end AlgebraicGeometry.Numerical
