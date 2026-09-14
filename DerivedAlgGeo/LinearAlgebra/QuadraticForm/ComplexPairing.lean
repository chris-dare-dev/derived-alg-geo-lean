/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Tactic

/-!
# The complex functional of a pair in a quadratic space

An ordered pair `(x, y)` — later read as the real and imaginary parts of `Ω` — determines

```
Z (v) = ⟪x, v⟫ + i ⟪y, v⟫
```

This is `⟪Ω, -⟫` written without complexifying the space, since `⟪·,·⟫` is
the polar form.  The API below is ordinary linear algebra: it packages no
heart, semistable locus, support predicate, or wall arrangement.

The span, orthogonal complement, and exact kernel description are generic
quadratic algebra. Signature and positive-plane consequences live in
`ComplexPairingSignature.lean`; stability and wall interpretations live in
`StabilityCondition/CentralCharge/Quadratic.lean`.

## Main results

* `centralCharge_eq_zero_iff` — **the kernel of `Z` is the orthogonal complement
  of the plane.**
-/

open QuadraticMap Complex

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}

section Pair

variable (Q)

/-- The subspace spanned by an ordered pair. -/
def pairSpan (x y : M) : Submodule ℝ M := Submodule.span ℝ ({x, y} : Set M)

/-- The orthogonal complement with respect to the polar pairing. -/
abbrev orthogonal (W : Submodule ℝ M) : Submodule ℝ M :=
  LinearMap.BilinForm.orthogonal Q.polarBilin W

end Pair


/-- Membership in the orthogonal complement, written using the polar form. -/
theorem mem_orthogonal_iff {W : Submodule ℝ M} {u : M} :
    u ∈ orthogonal Q W ↔ ∀ w ∈ W, polar (⇑Q) w u = 0 := by
  simp [orthogonal, LinearMap.BilinForm.mem_orthogonal_iff]

/-- Orthogonality to a span of two vectors is orthogonality to both. -/
theorem mem_orthogonal_span_pair_iff {x y u : M} :
    u ∈ orthogonal Q (Submodule.span ℝ ({x, y} : Set M)) ↔
      polar (⇑Q) x u = 0 ∧ polar (⇑Q) y u = 0 := by
  rw [mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨h x (Submodule.subset_span (by simp)), h y (Submodule.subset_span (by simp))⟩
  · rintro ⟨hx, hy⟩ w hw
    have hle : Submodule.span ℝ ({x, y} : Set M) ≤ LinearMap.ker (Q.polarBilin.flip u) := by
      rw [Submodule.span_le]
      rintro z (rfl | rfl) <;> simp [LinearMap.mem_ker, hx, hy]
    simpa [LinearMap.mem_ker] using hle hw

section Defs

variable (Q)

/-- The **central charge** of an ordered pair: the pairing against `x` and `y`
read as the real and imaginary parts of a complex number. -/
def centralCharge (x y v : M) : ℂ :=
  Complex.ofReal (polar (⇑Q) x v) + Complex.ofReal (polar (⇑Q) y v) * Complex.I

end Defs

@[simp]
theorem centralCharge_re (x y v : M) : (centralCharge Q x y v).re = polar (⇑Q) x v := by
  simp [centralCharge]

@[simp]
theorem centralCharge_im (x y v : M) : (centralCharge Q x y v).im = polar (⇑Q) y v := by
  simp [centralCharge]

theorem centralCharge_add (x y v w : M) :
    centralCharge Q x y (v + w) = centralCharge Q x y v + centralCharge Q x y w := by
  apply Complex.ext <;> simp [polar_add_right]

theorem centralCharge_smul (x y v : M) (a : ℝ) :
    centralCharge Q x y (a • v) = (a : ℂ) * centralCharge Q x y v := by
  apply Complex.ext <;> simp [polar_smul_right]

@[simp]
theorem centralCharge_zero (x y : M) : centralCharge Q x y 0 = 0 := by
  apply Complex.ext <;> simp

/-- **The kernel of the charge is the orthogonal complement of the plane.** -/
theorem centralCharge_eq_zero_iff {x y v : M} :
    centralCharge Q x y v = 0 ↔ v ∈ orthogonal Q (pairSpan x y) := by
  rw [pairSpan, mem_orthogonal_span_pair_iff, Complex.ext_iff]
  simp

/-- The charge kernel as a submodule: the orthogonal complement, named for what
it is in stability language. -/
theorem ker_centralCharge_eq (x y : M) :
    {v : M | centralCharge Q x y v = 0} = (orthogonal Q (pairSpan x y) : Set M) := by
  ext v
  exact centralCharge_eq_zero_iff

end PeriodDomain
