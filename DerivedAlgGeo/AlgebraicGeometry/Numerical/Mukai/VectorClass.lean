/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.SqrtTodd

/-!
# The Mukai vector as a class in the intersection ring

`v(E) = ch(E)·√td(X)`, component by component, for a numerical variety of any dimension.

Until now the Mukai vector existed in this repository only as a *formula*: `IntegralMukaiData`
asserts a triple `(rank, c₁, s)` by fiat, and `RiemannRoch/K3.lean` explains in a docstring that
this triple is what `ch(E)·√td(X)` comes to on a K3. This file makes that a theorem. After it,
`mukaiS` is a statement *about* `ch(E)·√td(X)` rather than a definition that happens to look
right.

## Why it is defined in every dimension

`mukaiComp` takes an arbitrary `n`. The K3 facts are a section at `n = 2`, not the definition.
Fourier–Mukai and the higher-dimensional Bridgeland lanes want `v(E)` on a threefold, and defining
it only where it is currently used would force a rewrite later.

## What is deliberately not touched

`mukaiS` is **not** redefined as the degree of the top component. The existing definition stays and
`K3.degree_mukaiComp_two` is the comparison theorem. Redefining it would ripple through the Euler
pairing, the Mukai vector, the transfer and the realization files, which is a restructuring this
lane must not do. Nothing under `Numerical/Core/**` or `Numerical/GrothendieckGroup/**` is edited.

## The one place the convolution bites

`mukaiComp_mem` needs the summand `chᵢ(E)·√td_{i-j}` to land in codimension `i`, and the grading
gives it codimension `j + (i - j)`. Those agree only because `j ≤ i` inside the sum, so the index
arithmetic is `Nat.add_sub_cancel'` and not `rfl`.
-/

universe u v

open Finset

namespace AlgebraicGeometry.Numerical

variable {n : ℕ} {A : Type u} [CommRing A] [Algebra ℚ A]
variable {N : Type v} [AddCommGroup N]

namespace NumericalVarietyData

variable (V : NumericalVarietyData n A N)

/-- **The codimension-`i` component of the Mukai vector**, `(ch(E)·√td(X))ᵢ`. -/
noncomputable def mukaiComp (E : N) (i : ℕ) : A :=
  ∑ j ∈ range (i + 1), V.chComp E j * V.sqrtToddComp (i - j)

/-- **The Mukai vector** `v(E) = ch(E)·√td(X)`, as a single class. -/
noncomputable def mukaiClass (E : N) : A :=
  ∑ i ∈ range (n + 1), V.mukaiComp E i

/-- The `i`-th component lives in codimension `i`. -/
theorem mukaiComp_mem (E : N) (i : ℕ) : V.mukaiComp E i ∈ V.ring.piece i := by
  refine Submodule.sum_mem _ fun j hj ↦ ?_
  have hji : j ≤ i := by
    simpa using Nat.lt_succ_iff.mp (mem_range.mp hj)
  have h := V.ring.mul_mem_piece (V.chComp_mem E j) (V.sqrtToddComp_mem (i - j))
  rwa [Nat.add_sub_cancel' hji] at h

/-- The Mukai vector is additive, because the Chern character is and `√td(X)` is a constant. -/
theorem mukaiComp_add (E F : N) (i : ℕ) :
    V.mukaiComp (E + F) i = V.mukaiComp E i + V.mukaiComp F i := by
  simp only [mukaiComp, V.chComp_add, add_mul]
  exact Finset.sum_add_distrib

theorem mukaiClass_add (E F : N) :
    V.mukaiClass (E + F) = V.mukaiClass E + V.mukaiClass F := by
  simp only [mukaiClass, V.mukaiComp_add]
  exact Finset.sum_add_distrib

/-- `v₀(E) = rank E`, because `√td₀ = 1` and `ch₀ = rank`. -/
@[simp]
theorem mukaiComp_zero (E : N) :
    V.mukaiComp E 0 = algebraMap ℚ A (V.rank E : ℚ) := by
  simp [mukaiComp, V.chComp_zero]

/-- A product of Mukai components integrates to zero unless the codimensions add to the
dimension. This is the shape `degree_chComp_mul_chComp_mul_toddComp_eq_zero` already has for the
Chern character, and it is what makes the Euler pairing collapse to a single term. -/
theorem degree_mukaiComp_mul_mukaiComp_eq_zero (E F : N) {i j : ℕ} (hij : i + j ≠ n) :
    V.ring.degree (V.mukaiComp E i * V.mukaiComp F j) = 0 :=
  V.ring.degree_eq_zero_of_mem hij
    (V.ring.mul_mem_piece (V.mukaiComp_mem E i) (V.mukaiComp_mem F j))

end NumericalVarietyData

end AlgebraicGeometry.Numerical
