/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.BilinearForm.HodgeIndex
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The diagonal model `diag(1, -1, …, -1)`

The signature-`(1, k)` form on `ℝ × (Fin k → ℝ)`, and the proof that every
vector of positive square carries a `HodgeDefinite` certificate for it.

## The point of this file

`Examples/Surface/BlowUpPlane.lean` proves the same statement for `k = 2` by
destructuring three coordinates and calling `nlinarith`, and its own docstring
calls that the hard part of the model. **That proof does not scale**: the
number of coordinates is fixed in the syntax, and the polynomial arithmetic
grows with it. `hodgeDefinite_diagonal` below is proved for every `k` at once,
by the argument that actually generalises — Cauchy–Schwarz on the
negative-definite part:

> With `w = (a, u)` and `x = (b, v)`, positivity of `w²` reads `‖u‖² < a²` and
> orthogonality reads `a·b = ⟪u, v⟫`.  Cauchy–Schwarz gives
> `a²b² = ⟪u, v⟫² ≤ ‖u‖²‖v‖² < a²‖v‖²` once `‖v‖² > 0`, and dividing by
> `a² > 0` gives `b² < ‖v‖²`, which is `x² < 0`.  When `‖v‖² = 0` the
> orthogonality relation forces `b = 0` and `x` is zero, which the hypothesis
> excludes.

Nothing here is case-split on `k`, and no coordinate is named.

## Transport

`hodgeDefinite_of_equiv_diagonal` is what makes the proof reusable: a
`DivisorSpace` on any carrier that admits a form-preserving linear equivalence
onto this model inherits the certificate. That is the intended route for a
concrete surface model to stop proving its own Hodge index inequality.

## What is not here

There is no surface. `ℝ × (Fin k → ℝ)` is a real vector space with a symmetric
form; it is not `N¹(X) ⊗ ℝ` for any `X`, `(1, 0, …, 0)` is not claimed to be a
hyperplane class, and no anticanonical class, ample cone or `(-1)`-class
appears. The comparison with `Examples/Surface/BlowUpPlane.lean` cannot live in
this file and does not: a module under `LinearAlgebra/` may not import
`AlgebraicGeometry/`, so the agreement lemma belongs to the consumer, built on
the transport theorem below.
-/

universe w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

/-! ### The model -/

/-- The carrier of the signature-`(1, k)` model: one coordinate of positive
square and `k` of negative square. -/
abbrev DiagonalDivisor (k : ℕ) : Type := ℝ × (Fin k → ℝ)

/-- The form `diag(1, -1, …, -1)` in `k + 1` variables. -/
def diagonalForm (k : ℕ) : LinearMap.BilinForm ℝ (DiagonalDivisor k) :=
  LinearMap.mk₂ ℝ (fun x y => x.1 * y.1 - ∑ i, x.2 i * y.2 i)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
      Finset.sum_add_distrib]; ring)
    (fun _ _ _ => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_sub,
        Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun i _ => by ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]; ring)
    (fun _ _ _ => by
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_sub,
        Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun i _ => by ring)

@[simp]
theorem diagonalForm_apply (k : ℕ) (x y : DiagonalDivisor k) :
    diagonalForm k x y = x.1 * y.1 - ∑ i, x.2 i * y.2 i := rfl

/-- The signature-`(1, k)` divisor space. -/
def diagonalSpace (k : ℕ) : DivisorSpace (DiagonalDivisor k) where
  intersection := diagonalForm k
  intersection_symm := ⟨by
    intro x y
    simp only [diagonalForm_apply]
    rw [mul_comm x.1 y.1]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩

@[simp]
theorem diagonalSpace_pair (k : ℕ) (x y : DiagonalDivisor k) :
    (diagonalSpace k).pair x y = x.1 * y.1 - ∑ i, x.2 i * y.2 i := rfl

/-! ### The Hodge index inequality, at every rank -/

/-- **The reverse Cauchy–Schwarz inequality for `diag(1, -1, …, -1)`.**  Every
vector of positive square carries a Hodge certificate: the form is negative
definite on its orthogonal complement.

Proved for all `k` at once.  The one inequality doing the work is
`Finset.sum_mul_sq_le_sq_mul_sq`, Cauchy–Schwarz on the negative-definite
coordinates; no coordinate is named and there is no case split on `k`. -/
theorem hodgeDefinite_diagonal {k : ℕ} {w : DiagonalDivisor k}
    (hw : 0 < (diagonalSpace k).pair w w) :
    (diagonalSpace k).HodgeDefinite w where
  H_square_pos := hw
  neg_definite x hx hxne := by
    obtain ⟨a, u⟩ := w
    obtain ⟨b, v⟩ := x
    simp only [diagonalSpace_pair] at hw hx ⊢
    have hUnonneg : (0 : ℝ) ≤ ∑ i, u i * u i :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
    have hVnonneg : (0 : ℝ) ≤ ∑ i, v i * v i :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    have hcs : (∑ i, u i * v i) ^ 2 ≤ (∑ i, u i * u i) * ∑ i, v i * v i := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
      simpa [pow_two] using h
    have hab : a * b = ∑ i, u i * v i := by linarith
    have ha2 : (∑ i, u i * u i) < a * a := by linarith
    have ha2pos : 0 < a * a := lt_of_le_of_lt hUnonneg ha2
    by_cases hV : (∑ i, v i * v i) = 0
    · exfalso
      have hv0 : ∀ i, v i = 0 := by
        intro i
        have hi := (Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (v j))).mp hV i (Finset.mem_univ i)
        exact mul_self_eq_zero.mp hi
      have hsum0 : (∑ i, u i * v i) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hv0 i, mul_zero]
      have hane : a ≠ 0 := fun h => by rw [h] at ha2pos; simp at ha2pos
      have hb : b = 0 := by
        have hz : a * b = 0 := by rw [hab, hsum0]
        exact (mul_eq_zero.mp hz).resolve_left hane
      refine hxne ?_
      have hveq : v = 0 := funext hv0
      rw [hb, hveq]
      rfl
    · have hVpos : 0 < ∑ i, v i * v i := lt_of_le_of_ne hVnonneg (Ne.symm hV)
      have h1 : (∑ i, u i * u i) * (∑ i, v i * v i) < (a * a) * ∑ i, v i * v i :=
        mul_lt_mul_of_pos_right ha2 hVpos
      have h2 : (a * b) ^ 2 < (a * a) * ∑ i, v i * v i := by
        rw [hab]; exact lt_of_le_of_lt hcs h1
      have h3 : (a * a) * (b * b) < (a * a) * ∑ i, v i * v i := by nlinarith [h2]
      have h4 : b * b < ∑ i, v i * v i := lt_of_mul_lt_mul_left h3 ha2pos.le
      linarith

/-! ### Transport onto the model -/

variable {D : Type w} [AddCommGroup D] [Module ℝ D]

/-- A `DivisorSpace` that admits a form-preserving linear equivalence onto the
diagonal model inherits its Hodge certificates, so a concrete model need not
prove its own Hodge index inequality. -/
theorem hodgeDefinite_of_equiv_diagonal {S : DivisorSpace D} {k : ℕ}
    (f : D ≃ₗ[ℝ] DiagonalDivisor k)
    (hf : ∀ x y, (diagonalSpace k).pair (f x) (f y) = S.pair x y)
    {w : D} (hw : 0 < S.pair w w) : S.HodgeDefinite w where
  H_square_pos := hw
  neg_definite x hx hxne := by
    have hfw : 0 < (diagonalSpace k).pair (f w) (f w) := by rw [hf]; exact hw
    have hperp : (diagonalSpace k).pair (f w) (f x) = 0 := by rw [hf]; exact hx
    have hne : f x ≠ 0 := fun h => hxne (f.injective (by rw [h, map_zero]))
    have hneg := (hodgeDefinite_diagonal hfw).neg_definite (f x) hperp hne
    rwa [hf] at hneg

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
