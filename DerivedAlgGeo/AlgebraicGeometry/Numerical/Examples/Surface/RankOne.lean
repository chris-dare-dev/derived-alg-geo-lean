/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.General
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.GradedBasis
import Mathlib.RingTheory.AdjoinRoot

/-!
# The intersection ring of a Picard-rank-one surface

Every smooth projective surface with `Pic X = ℤ·H` has the same numerical intersection ring
up to the one number `∫_X H²`: it is `ℚ[t]/(t³)` with `t = H`, graded by codimension, and
the degree map is pinned by where it sends `H²`.

So the ring, its grading, the Chern character in the basis `1, H, H²`, and the degree map on
the normal form are all shared. What distinguishes one surface from another is only the
**Todd class**, and that is what the individual model files supply:

* `Examples/Surface/K3.lean` — `td = 1 + 0 + (1/d)H²` on a K3 of degree `H² = 2d`;
* `Examples/Surface/ProjectivePlane.lean` — `td = 1 + (3/2)H + H²` on `ℙ²`, where `H² = 1`;
* `Examples/Surface/Abelian.lean` — `td = 1 + 0 + 0` on an abelian surface.

The degree is parametrised by `h2 = ∫_X H²` rather than by a surface, so a new
Picard-rank-one model costs a Todd class and nothing else.

`Examples/RankOne.lean` performs this same construction in arbitrary dimension, and the
threefold and fourfold models are built on it. This file is not rebuilt on top of that one:
see the implementation notes there for why.
-/

open Polynomial Submodule Set

namespace AlgebraicGeometry.Numerical

namespace Examples

/-! ### The ring `ℚ[t]/(t³)` -/

/-- The defining relation: nothing survives in codimension three on a surface. -/
noncomputable def surfaceRel : ℚ[X] := X ^ 3

theorem surfaceRel_ne_zero : surfaceRel ≠ 0 :=
  pow_ne_zero 3 Polynomial.X_ne_zero

/-- The numerical intersection ring `A^•(X)_ℚ = ℚ[t]/(t³)`. -/
abbrev SurfaceRing : Type := AdjoinRoot surfaceRel

/-- The power basis `1, H, H²`. -/
noncomputable def surfacePB : PowerBasis ℚ SurfaceRing := AdjoinRoot.powerBasis surfaceRel_ne_zero

theorem surfacePB_dim : surfacePB.dim = 3 := by
  rw [surfacePB, AdjoinRoot.powerBasis_dim, surfaceRel, Polynomial.natDegree_X_pow]

/-- The ample generator of the Picard group. -/
noncomputable def H : SurfaceRing := AdjoinRoot.root surfaceRel

theorem surfacePB_gen : surfacePB.gen = H := AdjoinRoot.powerBasis_gen _

theorem surfacePB_basis_apply (i : Fin surfacePB.dim) : surfacePB.basis i = H ^ (i : ℕ) := by
  rw [surfacePB.basis_eq_pow, surfacePB_gen]

/-- `H³ = 0`: the relation, in the ring. -/
theorem H_pow_three : H ^ 3 = 0 := by
  change AdjoinRoot.root surfaceRel ^ 3 = 0
  rw [← AdjoinRoot.eval₂_root surfaceRel]
  simp [surfaceRel]
  rfl

theorem H_pow_four : H ^ 4 = 0 := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, H_pow_three, zero_mul]

/-- The codimension of `Hⁱ` is `i`. -/
def surfaceW : Fin surfacePB.dim → ℕ := fun i => (i : ℕ)

-- `surfacePB.dim` cannot be rewritten inside a hypothesis mentioning `i : Fin surfacePB.dim`
-- — the motive does not typecheck. Feed the equation to `omega` as a fact about naturals.
theorem surfaceW_le (i : Fin surfacePB.dim) : surfaceW i ≤ 2 := by
  have h := i.isLt
  have hd := surfacePB_dim
  show (i : ℕ) ≤ 2
  omega

theorem two_lt_dim : (2 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num

/-- The index of `H²`, the top graded piece. -/
def idx2 : Fin surfacePB.dim := ⟨2, two_lt_dim⟩

theorem surface_one_mem : (1 : SurfaceRing) ∈ gradedPiece (⇑surfacePB.basis) surfaceW 0 := by
  have h0 : (0 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num
  have hb : surfacePB.basis ⟨0, h0⟩ = 1 := by rw [surfacePB_basis_apply]; simp
  have hmem := mem_gradedPiece (b := ⇑surfacePB.basis) (w := surfaceW) ⟨0, h0⟩
  rwa [hb] at hmem

theorem surface_mul_mem (p q : Fin surfacePB.dim) :
    surfacePB.basis p * surfacePB.basis q
      ∈ gradedPiece (⇑surfacePB.basis) surfaceW (surfaceW p + surfaceW q) := by
  rw [surfacePB_basis_apply, surfacePB_basis_apply, ← pow_add]
  by_cases hpq : (p : ℕ) + (q : ℕ) < surfacePB.dim
  · have hmem := mem_gradedPiece (b := ⇑surfacePB.basis) (w := surfaceW) ⟨(p : ℕ) + (q : ℕ), hpq⟩
    rwa [surfacePB_basis_apply] at hmem
  · have hd := surfacePB_dim
    have h3 : 3 ≤ (p : ℕ) + (q : ℕ) := by omega
    have hzero : H ^ ((p : ℕ) + (q : ℕ)) = 0 := by
      obtain ⟨m, hm⟩ : ∃ m, (p : ℕ) + (q : ℕ) = 3 + m := ⟨(p : ℕ) + (q : ℕ) - 3, by omega⟩
      rw [hm, pow_add, H_pow_three, zero_mul]
    rw [hzero]
    exact Submodule.zero_mem _

theorem H_mem_piece_one : H ∈ gradedPiece (⇑surfacePB.basis) surfaceW 1 := by
  have h1 : (1 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num
  have hb : surfacePB.basis ⟨1, h1⟩ = H := by rw [surfacePB_basis_apply]; simp
  have hmem := mem_gradedPiece (b := ⇑surfacePB.basis) (w := surfaceW) ⟨1, h1⟩
  rwa [hb] at hmem

theorem Hsq_mem_piece_two : H ^ 2 ∈ gradedPiece (⇑surfacePB.basis) surfaceW 2 := by
  have hb : surfacePB.basis idx2 = H ^ 2 := by rw [surfacePB_basis_apply]; rfl
  have hmem := mem_gradedPiece (b := ⇑surfacePB.basis) (w := surfaceW) idx2
  rwa [hb] at hmem

theorem algebraMap_mul_mem {i : ℕ} {x : SurfaceRing} (q : ℚ)
    (hx : x ∈ gradedPiece (⇑surfacePB.basis) surfaceW i) :
    algebraMap ℚ SurfaceRing q * x ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hx

/-! ### The degree map, pinned by `∫_X H² = h2` -/

/-- `∫_X`, normalised so that `∫_X H² = h2`. -/
noncomputable def surfaceDegree (h2 : ℚ) : SurfaceRing →ₗ[ℚ] ℚ := h2 • surfacePB.basis.coord idx2

-- `simp` is the wrong tool here: `PowerBasis.coe_basis` fires first and turns `basis i` into
-- `gen ^ i`, after which `Basis.repr_self` no longer matches. Rewrite by hand.
theorem surfaceDegree_basis_of_ne (h2 : ℚ) (i : Fin surfacePB.dim) (hi : surfaceW i ≠ 2) :
    surfaceDegree h2 (surfacePB.basis i) = 0 := by
  have hne : i ≠ idx2 := fun h => hi (by rw [h]; rfl)
  show (h2 • surfacePB.basis.coord idx2) (surfacePB.basis i) = 0
  rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp [hne]

theorem surfaceDegree_basis_two (h2 : ℚ) : surfaceDegree h2 (surfacePB.basis idx2) = h2 := by
  show (h2 • surfacePB.basis.coord idx2) (surfacePB.basis idx2) = h2
  rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp

theorem surfaceDegree_one (h2 : ℚ) : surfaceDegree h2 1 = 0 := by
  have h0 : (0 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num
  have hb : surfacePB.basis ⟨0, h0⟩ = 1 := by rw [surfacePB_basis_apply]; simp
  rw [← hb]
  exact surfaceDegree_basis_of_ne h2 _ (by show (0 : ℕ) ≠ 2; decide)

theorem surfaceDegree_H (h2 : ℚ) : surfaceDegree h2 H = 0 := by
  have h1 : (1 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num
  have hb : surfacePB.basis ⟨1, h1⟩ = H := by rw [surfacePB_basis_apply]; simp
  rw [← hb]
  exact surfaceDegree_basis_of_ne h2 _ (by show (1 : ℕ) ≠ 2; decide)

/-- `∫_X H² = h2`: the degree of the surface. -/
theorem surfaceDegree_Hsq (h2 : ℚ) : surfaceDegree h2 (H ^ 2) = h2 := by
  have hb : surfacePB.basis idx2 = H ^ 2 := by rw [surfacePB_basis_apply]; rfl
  rw [← hb]
  exact surfaceDegree_basis_two h2

theorem surfaceDegree_algebraMap_mul (h2 q : ℚ) (x : SurfaceRing) :
    surfaceDegree h2 (algebraMap ℚ SurfaceRing q * x) = q * surfaceDegree h2 x := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- `∫_X` on the normal form `a + b·H + c·H²`. Only the top coefficient survives. -/
theorem surfaceDegree_normalForm (h2 a b c : ℚ) :
    surfaceDegree h2 (algebraMap ℚ SurfaceRing a + algebraMap ℚ SurfaceRing b * H
      + algebraMap ℚ SurfaceRing c * H ^ 2) = h2 * c := by
  rw [map_add, map_add, surfaceDegree_algebraMap_mul, surfaceDegree_algebraMap_mul,
    surfaceDegree_H, surfaceDegree_Hsq, mul_zero, add_zero]
  rw [show algebraMap ℚ SurfaceRing a = algebraMap ℚ SurfaceRing a * 1 by rw [mul_one],
    surfaceDegree_algebraMap_mul, surfaceDegree_one, mul_zero, zero_add]
  ring

/-- The numerical intersection ring of a Picard-rank-one surface with `∫_X H² = h2`. -/
@[reducible]
noncomputable def surfaceNumericalRing (h2 : ℚ) : NumericalRingData 2 SurfaceRing :=
  NumericalRingData.ofGradedBasis 2 surfacePB.basis surfaceW surfaceW_le surface_one_mem
    surface_mul_mem (surfaceDegree h2) (surfaceDegree_basis_of_ne h2)

/-! ### The Chern character

All three models use the same `N`. `K3.lean` and `Abelian.lean` share `k3ChCoeff`;
`ProjectivePlane.lean` reparametrises with its own `p2ChCoeff`, because `ch₂` is a
half-integer on `ℙ²` — see `Examples/Surface/ProjectivePlane.lean`. Coefficients are
therefore rational rather than integral. -/

/-- A class is recorded by the three rational coefficients of `ch = a + b·H + c·H²`. -/
abbrev SurfaceNum : Type := Fin 3 → ℤ

/-- The Chern character of `E`, given its coefficient functions. `chCoeff E i` is the
coefficient of `Hⁱ`; keeping it abstract lets `ℙ²` use half-integers. -/
noncomputable def surfaceCh (chCoeff : SurfaceNum → ℕ → ℚ) (E : SurfaceNum) : ℕ → SurfaceRing
  | 0 => algebraMap ℚ SurfaceRing (chCoeff E 0)
  | 1 => algebraMap ℚ SurfaceRing (chCoeff E 1) * H
  | 2 => algebraMap ℚ SurfaceRing (chCoeff E 2) * H ^ 2
  | _ + 3 => 0

theorem surfaceCh_mem (chCoeff : SurfaceNum → ℕ → ℚ) (E : SurfaceNum) (i : ℕ) :
    surfaceCh chCoeff E i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 =>
    show algebraMap ℚ SurfaceRing (chCoeff E 0) ∈ _
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ surface_one_mem
  | 1 => exact algebraMap_mul_mem _ H_mem_piece_one
  | 2 => exact algebraMap_mul_mem _ Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

theorem surfaceCh_add (chCoeff : SurfaceNum → ℕ → ℚ)
    (hadd : ∀ E F i, chCoeff (E + F) i = chCoeff E i + chCoeff F i)
    (E F : SurfaceNum) (i : ℕ) :
    surfaceCh chCoeff (E + F) i = surfaceCh chCoeff E i + surfaceCh chCoeff F i := by
  match i with
  | 0 =>
    show algebraMap ℚ SurfaceRing (chCoeff (E + F) 0) = _
    rw [hadd, map_add]
    rfl
  | 1 =>
    show algebraMap ℚ SurfaceRing (chCoeff (E + F) 1) * H = _
    rw [hadd, map_add, add_mul]
    rfl
  | 2 =>
    show algebraMap ℚ SurfaceRing (chCoeff (E + F) 2) * H ^ 2 = _
    rw [hadd, map_add, add_mul]
    rfl
  | _ + 3 => show (0 : SurfaceRing) = 0 + 0; rw [add_zero]

theorem surfaceCh_sum (chCoeff : SurfaceNum → ℕ → ℚ) (E : SurfaceNum) :
    (∑ i ∈ Finset.range (2 + 1), surfaceCh chCoeff E i)
      = algebraMap ℚ SurfaceRing (chCoeff E 0) + algebraMap ℚ SurfaceRing (chCoeff E 1) * H
        + algebraMap ℚ SurfaceRing (chCoeff E 2) * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  rfl

/-- **The product `ch(E)·td(X)`, reduced.** Everything of codimension above two is killed by
`H³ = H⁴ = 0`, leaving the codimension-two coefficient `a·t₂ + b·t₁ + c`.

This is the computational core shared by every Picard-rank-one model. -/
theorem surfaceDegree_ch_mul_todd (h2 a b c t₁ t₂ : ℚ) :
    surfaceDegree h2
        ((algebraMap ℚ SurfaceRing a + algebraMap ℚ SurfaceRing b * H
            + algebraMap ℚ SurfaceRing c * H ^ 2)
          * (1 + algebraMap ℚ SurfaceRing t₁ * H + algebraMap ℚ SurfaceRing t₂ * H ^ 2))
      = h2 * (a * t₂ + b * t₁ + c) := by
  have hprod :
      (algebraMap ℚ SurfaceRing a + algebraMap ℚ SurfaceRing b * H
          + algebraMap ℚ SurfaceRing c * H ^ 2)
        * (1 + algebraMap ℚ SurfaceRing t₁ * H + algebraMap ℚ SurfaceRing t₂ * H ^ 2)
      = algebraMap ℚ SurfaceRing a + algebraMap ℚ SurfaceRing (b + a * t₁) * H
        + algebraMap ℚ SurfaceRing (a * t₂ + b * t₁ + c) * H ^ 2 := by
    rw [map_add, map_add, map_add, map_mul, map_mul, map_mul]
    linear_combination
      (algebraMap ℚ SurfaceRing c * algebraMap ℚ SurfaceRing t₁
        + algebraMap ℚ SurfaceRing b * algebraMap ℚ SurfaceRing t₂) * H_pow_three
        + (algebraMap ℚ SurfaceRing c * algebraMap ℚ SurfaceRing t₂) * H_pow_four
  rw [hprod, surfaceDegree_normalForm]

end Examples

end AlgebraicGeometry.Numerical
