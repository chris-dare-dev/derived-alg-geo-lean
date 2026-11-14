/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Polar decomposition for invertible matrices

`A = Q * P` with `Q` unitary and `P` positive definite, over `RCLike` scalars.

**Mathlib has no polar decomposition for matrices at the pinned revision**
(`8a178386`) — a search for `polarDecomposition` across the whole library
returns nothing. This file supplies the case this repo needs, in the
`ForMathlib` pattern this repository uses for Mathlib gaps, and is written to be
upstreamable rather than to be convenient here.

## Main definitions

* `Matrix.polarFactor`: the positive-definite factor `√(Aᴴ A)`.
* `Matrix.polarUnitary`: the unitary factor `A · √(Aᴴ A)⁻¹`.

## Main results

* `Matrix.polarFactor_posDef`: for invertible `A` the factor `√(Aᴴ A)` is
  positive definite.
* `Matrix.polarUnitary_mem_unitaryGroup`: the factor `A · √(Aᴴ A)⁻¹` is unitary.
* `Matrix.exists_polarDecomposition`: every invertible matrix is a unitary
  matrix times a positive-definite one.
* `Matrix.eq_polarFactor_of_mul`, `Matrix.eq_polarUnitary_of_mul` and
  `Matrix.existsUnique_polarDecomposition`: both factors are unique.

## Implementation notes

### Why it costs almost nothing

The classical proof needs a square root of the positive-definite matrix
`Aᴴ A`, which usually comes from the spectral theorem. Here it does not:
Mathlib's **continuous functional calculus** applies to real matrices once the
Loewner order is in scope (`open scoped MatrixOrder`), so `CFC.sqrt` is
available directly and `CFC.sqrt_mul_sqrt_self` is the only property needed.

That is the whole trick. `P := √(Aᴴ A)`, `Q := A P⁻¹`, and

```
Qᴴ Q = P⁻¹ Aᴴ A P⁻¹ = P⁻¹ (P P) P⁻¹ = 1.
```

### Uniqueness

Both factors are unique. If `A = Q P` with `Q` unitary and `P` positive
definite then `Pᴴ Qᴴ Q P = P P`, so `P` is *a* nonnegative square root of
`Aᴴ A` — and the nonnegative square root is unique (`CFC.sqrt_unique`), so it
is *the* one. `Q = A P⁻¹` then follows.

## References

Mathlib's `CFC.sqrt`, `CFC.sqrt_mul_sqrt_self`, `CFC.sqrt_unique` and
`Matrix.unitaryGroup`.

## Tags

polar decomposition, matrix square root, unitary matrix, positive definite
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open scoped MatrixOrder ComplexOrder

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ## The positive-definite factor -/

/-- The positive-definite factor of the polar decomposition, `√(Aᴴ A)`. -/
noncomputable def polarFactor (A : Matrix n n 𝕜) : Matrix n n 𝕜 := CFC.sqrt (Aᴴ * A)

theorem polarFactor_posSemidef (A : Matrix n n 𝕜) : (polarFactor A).PosSemidef :=
  nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

/-- `√(Aᴴ A)` squares to `Aᴴ A`. This is the only property of the square root
the construction uses. -/
theorem polarFactor_mul_self (A : Matrix n n 𝕜) :
    polarFactor A * polarFactor A = Aᴴ * A :=
  CFC.sqrt_mul_sqrt_self _ (posSemidef_conjTranspose_mul_self A).nonneg

theorem polarFactor_isHermitian (A : Matrix n n 𝕜) : (polarFactor A).IsHermitian :=
  (polarFactor_posSemidef A).isHermitian

section Invertible

variable {A : Matrix n n 𝕜} (hA : IsUnit A.det)
include hA

theorem det_polarFactor_ne_zero : (polarFactor A).det ≠ 0 := by
  intro h
  have hsq : (polarFactor A).det * (polarFactor A).det = (Aᴴ * A).det := by
    rw [← det_mul, polarFactor_mul_self]
  rw [h, mul_zero, det_mul, det_conjTranspose] at hsq
  exact hA.ne_zero (by simpa [star_eq_zero] using mul_eq_zero.mp hsq.symm)

theorem isUnit_det_polarFactor : IsUnit (polarFactor A).det :=
  (isUnit_iff_ne_zero).mpr (det_polarFactor_ne_zero hA)

/-- With `A` invertible the factor is positive **definite**, not merely
semidefinite. -/
theorem polarFactor_posDef : (polarFactor A).PosDef := by
  refine posDef_iff_dotProduct_mulVec.mpr ⟨polarFactor_isHermitian A, fun x hx => ?_⟩
  -- `RCLike` carries only a partial order, so this is `0 ≤ v` together with
  -- `0 ≠ v` rather than a case split. Semidefiniteness gives the first; the
  -- second is where invertibility enters, via the empty kernel.
  refine lt_of_le_of_ne ((polarFactor_posSemidef A).dotProduct_mulVec_nonneg x) ?_
  intro heq
  have hker : polarFactor A *ᵥ x = 0 :=
    ((polarFactor_posSemidef A).dotProduct_mulVec_zero_iff (x := x)).mp heq.symm
  refine hx ?_
  have hinv := isUnit_det_polarFactor hA
  have hx0 := congrArg (fun v => (polarFactor A)⁻¹ *ᵥ v) hker
  simpa [mulVec_mulVec, nonsing_inv_mul _ hinv] using hx0

/-! ## The orthogonal factor -/

/-- The unitary factor of the polar decomposition, `A · √(Aᴴ A)⁻¹`. -/
noncomputable def polarUnitary (A : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  A * (polarFactor A)⁻¹

theorem polarUnitary_mul_polarFactor : polarUnitary A * polarFactor A = A := by
  rw [polarUnitary, Matrix.mul_assoc, nonsing_inv_mul _ (isUnit_det_polarFactor hA),
    Matrix.mul_one]

theorem polarUnitary_mem_unitaryGroup :
    polarUnitary A ∈ Matrix.unitaryGroup n 𝕜 := by
  have hHerm : (polarFactor A)ᴴ = polarFactor A := polarFactor_isHermitian A
  have hinv : IsUnit (polarFactor A).det := isUnit_det_polarFactor hA
  have hinvHerm : ((polarFactor A)⁻¹)ᴴ = (polarFactor A)⁻¹ := by
    rw [conjTranspose_nonsing_inv, hHerm]
  rw [mem_unitaryGroup_iff']
  show (polarUnitary A)ᴴ * polarUnitary A = 1
  rw [polarUnitary, conjTranspose_mul, hinvHerm]
  calc (polarFactor A)⁻¹ * Aᴴ * (A * (polarFactor A)⁻¹)
      = (polarFactor A)⁻¹ * (Aᴴ * A) * (polarFactor A)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (polarFactor A)⁻¹ * (polarFactor A * polarFactor A) * (polarFactor A)⁻¹ := by
        rw [polarFactor_mul_self]
    _ = 1 := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hinv, Matrix.one_mul,
          mul_nonsing_inv _ hinv]

/-- **Polar decomposition.** Every invertible matrix factors as a unitary
matrix times a positive-definite one. -/
theorem exists_polarDecomposition :
    ∃ Q ∈ Matrix.unitaryGroup n 𝕜, ∃ P : Matrix n n 𝕜, P.PosDef ∧ A = Q * P :=
  ⟨polarUnitary A, polarUnitary_mem_unitaryGroup hA, polarFactor A,
    polarFactor_posDef hA, (polarUnitary_mul_polarFactor hA).symm⟩

/-! ## Uniqueness -/

omit hA in
/-- The positive-definite factor is unique. -/
theorem eq_polarFactor_of_mul {Q P : Matrix n n 𝕜} (hQ : Q ∈ Matrix.unitaryGroup n 𝕜)
    (hP : P.PosDef) (hQP : A = Q * P) : P = polarFactor A := by
  refine (CFC.sqrt_unique ?_ hP.posSemidef.nonneg).symm
  have hQ' : Qᴴ * Q = 1 := by
    have := (mem_unitaryGroup_iff' (A := Q)).mp hQ
    simpa only [Matrix.star_eq_conjTranspose] using this
  calc P * P = Pᴴ * (Qᴴ * Q) * P := by rw [hQ', hP.isHermitian]; simp
    _ = (Q * P)ᴴ * (Q * P) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * A := by rw [← hQP]

/-- The unitary factor is unique. -/
theorem eq_polarUnitary_of_mul {Q P : Matrix n n 𝕜} (hQ : Q ∈ Matrix.unitaryGroup n 𝕜)
    (hP : P.PosDef) (hQP : A = Q * P) : Q = polarUnitary A := by
  have hPeq : P = polarFactor A := eq_polarFactor_of_mul hQ hP hQP
  have hinv : IsUnit (polarFactor A).det := isUnit_det_polarFactor hA
  have key : Q * polarFactor A = A := by rw [← hPeq, ← hQP]
  -- Built forwards: rewriting with `hQP` would also hit the `A` inside
  -- `polarFactor A`.
  calc Q = Q * (polarFactor A * (polarFactor A)⁻¹) := by
        rw [mul_nonsing_inv _ hinv, Matrix.mul_one]
    _ = Q * polarFactor A * (polarFactor A)⁻¹ := by rw [Matrix.mul_assoc]
    _ = A * (polarFactor A)⁻¹ := by rw [key]
    _ = polarUnitary A := rfl

/-- **Polar decomposition, with uniqueness.** -/
theorem existsUnique_polarDecomposition :
    ∃! QP : Matrix n n 𝕜 × Matrix n n 𝕜,
      QP.1 ∈ Matrix.unitaryGroup n 𝕜 ∧ QP.2.PosDef ∧ A = QP.1 * QP.2 := by
  refine ⟨(polarUnitary A, polarFactor A),
    ⟨polarUnitary_mem_unitaryGroup hA, polarFactor_posDef hA,
      (polarUnitary_mul_polarFactor hA).symm⟩, ?_⟩
  rintro ⟨Q, P⟩ ⟨hQ, hP, hQP⟩
  exact Prod.ext (eq_polarUnitary_of_mul hA hQ hP hQP) (eq_polarFactor_of_mul hQ hP hQP)

end Invertible

end Matrix
