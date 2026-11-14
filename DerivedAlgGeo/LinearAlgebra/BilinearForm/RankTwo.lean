/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic

/-!
# Rank-two Gram determinants of a bilinear form

For a module `M` over a commutative ring `R` with a bilinear form `B`, the Gram
determinant of a pair is `B v v * B w w - (B v w)^2`, and the pair is
**hyperbolic** when that determinant is negative -- signature `(1, 1)` for a
rank-two lattice.

## Main definitions

* `BilinearForm.gram`: the Gram determinant of a pair.
* `BilinearForm.orthWitness`: `B v w • v - B v v • w`, the projection of `w`
  off `v` cleared of denominators.
* `BilinearForm.pairSpan`: the set of `R`-combinations of two vectors.
* `BilinearForm.IsHyperbolicPair`: negative Gram determinant.

## Main results

* `BilinearForm.gram_lincomb`: the Gram determinant transforms by the square
  of the change-of-basis determinant.
* `BilinearForm.apply_orthWitness` and `BilinearForm.self_orthWitness`: the
  witness is orthogonal to `v` and has self-pairing `B v v * gram B v w`.
* `BilinearForm.isHyperbolicPair_lincomb`: hyperbolicity is invariant under a
  change of basis whose determinant squares to `1`.
* `BilinearForm.exists_neg_self_of_isHyperbolicPair`: a hyperbolic pair with
  `B v v > 0` spans a nonzero vector of negative square.

## Implementation notes

### This is stated over an arbitrary ambient form, not over one extension

Every identity here is arithmetic of two vectors under a bilinear form, and none
of it depends on a particular carrier. So it is stated on `(R, M, B)`, and
`Lattice/Mukai/RankTwo.lean` specialises it on the carrier `ℤ × N × ℤ` at
`B := Mukai.pairingBilin b`.

The file splits at the point where order is needed, which is also where the
hypotheses stop being purely algebraic:

* `gram`, the change-of-basis identity and `orthWitness` need only a commutative
  ring, and `apply_orthWitness` needs no symmetry either;
* `IsHyperbolicPair` and everything reading a sign need a linear order and a
  strict ordered ring structure.

### What is deliberately not here

`HasSphericalClass` and `HasIsotropicClass` stay in `Lattice/Mukai/RankTwo.lean`.
They are phrased in terms of `IsSpherical` and `IsIsotropic`, which are
application vocabulary for `-2` and `0`, and that vocabulary stays with the
application.

No geometry is asserted. The correspondence between rank-two data and actual
walls in a space of stability conditions is Bayer--Macrì Theorem 5.7; it needs
moduli of stable objects and is **not** formalised anywhere below.

## References

* Bayer--Macrì, Theorem 5.7, cited only for the wall correspondence this file
  does not formalise.
* Mathlib's bilinear maps `M →ₗ[R] M →ₗ[R] R` in
  `Mathlib.LinearAlgebra.BilinearForm.Basic`.

## Tags

bilinear form, Gram determinant, hyperbolic pair, signature
-/

namespace BilinearForm

section Algebraic
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : M →ₗ[R] M →ₗ[R] R)

/-- The Gram determinant of the pair `(v, w)`: `B v v * B w w - (B v w)^2`. -/
def gram (v w : M) : R := B v v * B w w - B v w ^ 2

theorem gram_comm (hb : ∀ x y : M, B x y = B y x) (v w : M) :
    gram B v w = gram B w v := by
  simp only [gram, hb w v]; ring

@[simp] theorem gram_zero_left (w : M) : gram B 0 w = 0 := by simp [gram]
@[simp] theorem gram_zero_right (v : M) : gram B v 0 = 0 := by simp [gram]

theorem apply_lincomb (hb : ∀ x y : M, B x y = B y x) (a₁ a₂ a₃ a₄ : R) (v w : M) :
    B (a₁ • v + a₂ • w) (a₃ • v + a₄ • w)
      = a₁ * a₃ * B v v + (a₁ * a₄ + a₂ * a₃) * B v w + a₂ * a₄ * B w w := by
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hb w v]
  ring

theorem self_lincomb (hb : ∀ x y : M, B x y = B y x) (a₁ a₂ : R) (v w : M) :
    B (a₁ • v + a₂ • w) (a₁ • v + a₂ • w)
      = a₁ ^ 2 * B v v + 2 * (a₁ * a₂) * B v w + a₂ ^ 2 * B w w := by
  rw [apply_lincomb B hb a₁ a₂ a₁ a₂ v w]; ring

theorem gram_lincomb (hb : ∀ x y : M, B x y = B y x) (a₁ a₂ a₃ a₄ : R) (v w : M) :
    gram B (a₁ • v + a₂ • w) (a₃ • v + a₄ • w)
      = (a₁ * a₄ - a₂ * a₃) ^ 2 * gram B v w := by
  simp only [gram, self_lincomb B hb, apply_lincomb B hb]; ring

/-- `B v w • v - B v v • w`, the projection of `w` off `v` cleared of
denominators. Orthogonal to `v` with no symmetry hypothesis. -/
def orthWitness (v w : M) : M := B v w • v - B v v • w

theorem apply_orthWitness (v w : M) : B v (orthWitness B v w) = 0 := by
  simp only [orthWitness, map_sub, map_smul, smul_eq_mul]; ring

theorem self_orthWitness (hb : ∀ x y : M, B x y = B y x) (v w : M) :
    B (orthWitness B v w) (orthWitness B v w) = B v v * gram B v w := by
  simp only [orthWitness, gram, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hb w v]
  ring

/-- The set of `R`-combinations of `v` and `w`. -/
def pairSpan (v w : M) : Set M := {x | ∃ a₁ a₂ : R, x = a₁ • v + a₂ • w}

theorem mem_pairSpan_left (v w : M) : v ∈ pairSpan (R := R) v w := ⟨1, 0, by simp⟩
theorem mem_pairSpan_right (v w : M) : w ∈ pairSpan (R := R) v w := ⟨0, 1, by simp⟩

theorem orthWitness_mem_pairSpan (v w : M) :
    orthWitness B v w ∈ pairSpan (R := R) v w :=
  ⟨B v w, -B v v, by simp [orthWitness, sub_eq_add_neg]⟩

end Algebraic

section Ordered
variable {R M : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup M] [Module R M] (B : M →ₗ[R] M →ₗ[R] R)

/-- Negative Gram determinant: the rank-two form spanned by `v` and `w` is
indefinite. For a rank-two lattice this is signature `(1, 1)`.

A numerical condition on two vectors, and **not** a claim that a wall exists in
any space of stability conditions. -/
def IsHyperbolicPair (v w : M) : Prop := gram B v w < 0

theorem isHyperbolicPair_iff (v w : M) :
    IsHyperbolicPair B v w ↔ B v v * B w w < B v w ^ 2 := by
  rw [IsHyperbolicPair, gram]; constructor <;> intro h <;> linarith

theorem discr_pos_of_isHyperbolicPair {v w : M} (h : IsHyperbolicPair B v w) :
    0 < 4 * (B v w ^ 2 - B v v * B w w) := by
  rw [IsHyperbolicPair, gram] at h; linarith

omit [IsStrictOrderedRing R] in
theorem gram_ne_zero_of_isHyperbolicPair {v w : M} (h : IsHyperbolicPair B v w) :
    gram B v w ≠ 0 := ne_of_lt h

omit [IsStrictOrderedRing R] in
theorem ne_zero_left_of_isHyperbolicPair {v w : M} (h : IsHyperbolicPair B v w) :
    v ≠ 0 := by
  rintro rfl; rw [IsHyperbolicPair, gram_zero_left] at h; exact absurd h (lt_irrefl 0)

omit [IsStrictOrderedRing R] in
theorem ne_zero_right_of_isHyperbolicPair {v w : M} (h : IsHyperbolicPair B v w) :
    w ≠ 0 := by
  rintro rfl; rw [IsHyperbolicPair, gram_zero_right] at h; exact absurd h (lt_irrefl 0)

omit [IsStrictOrderedRing R] in
theorem isHyperbolicPair_comm (hb : ∀ x y : M, B x y = B y x) (v w : M) :
    IsHyperbolicPair B v w ↔ IsHyperbolicPair B w v := by
  rw [IsHyperbolicPair, IsHyperbolicPair, gram_comm B hb]

omit [IsStrictOrderedRing R] in
theorem isHyperbolicPair_lincomb (hb : ∀ x y : M, B x y = B y x) {a₁ a₂ a₃ a₄ : R}
    (hd : (a₁ * a₄ - a₂ * a₃) ^ 2 = 1) {v w : M} (h : IsHyperbolicPair B v w) :
    IsHyperbolicPair B (a₁ • v + a₂ • w) (a₃ • v + a₄ • w) := by
  rw [IsHyperbolicPair, gram_lincomb B hb, hd, one_mul]; exact h

theorem self_orthWitness_neg (hb : ∀ x y : M, B x y = B y x) {v w : M}
    (hv : 0 < B v v) (h : IsHyperbolicPair B v w) :
    B (orthWitness B v w) (orthWitness B v w) < 0 := by
  rw [self_orthWitness B hb]; exact mul_neg_of_pos_of_neg hv h

theorem orthWitness_ne_zero (hb : ∀ x y : M, B x y = B y x) {v w : M}
    (hv : 0 < B v v) (h : IsHyperbolicPair B v w) : orthWitness B v w ≠ 0 := by
  intro hzero
  have := self_orthWitness_neg B hb hv h
  rw [hzero, map_zero] at this
  simp at this

theorem exists_neg_self_of_isHyperbolicPair (hb : ∀ x y : M, B x y = B y x)
    {v w : M} (hv : 0 < B v v) (h : IsHyperbolicPair B v w) :
    ∃ x ∈ pairSpan (R := R) v w, x ≠ 0 ∧ B x x < 0 :=
  ⟨orthWitness B v w, orthWitness_mem_pairSpan B v w,
    orthWitness_ne_zero B hb hv h, self_orthWitness_neg B hb hv h⟩

end Ordered
end BilinearForm
