/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.SqrtTodd
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Discriminant
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector

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

namespace K3

open NumericalVarietyData

variable {V : NumericalVarietyData 2 A N}

/-- On a K3 the linear component of the Mukai vector is `c₁`: the cross term dies because
`√td₁ = 0`. -/
theorem mukaiComp_one (hK3 : IsK3 V) (E : N) : V.mukaiComp E 1 = V.chComp E 1 := by
  rw [mukaiComp, Finset.sum_range_succ, Finset.sum_range_one]
  simp [K3.sqrtToddComp_one hK3]

/-- On a K3 the top component is `ch₂(E) + rank(E)·√td₂`: the middle summand
`ch₁(E)·√td₁` vanishes. -/
theorem mukaiComp_two (hK3 : IsK3 V) (E : N) :
    V.mukaiComp E 2 =
      V.chComp E 2 + algebraMap ℚ A (V.rank E : ℚ) * V.sqrtToddComp 2 := by
  simp [mukaiComp, Finset.sum_range_succ, K3.sqrtToddComp_one hK3, V.chComp_zero]
  ring

/-- **The deliverable the lane hangs on.** `∫_X v₂(E) = mukaiS V E`.

`mukaiS` was defined as `rank E + ∫ ch₂(E)`, which is what `ch(E)·√td(X)` comes to in top
codimension on a K3 — but only because `∫√td₂ = 1`. That is now used rather than asserted. Note
the hypothesis: `IsK3` alone, with no Riemann–Roch input. -/
theorem degree_mukaiComp_two (hK3 : IsK3 V) (E : N) :
    V.ring.degree (V.mukaiComp E 2) = mukaiS V E := by
  rw [mukaiComp_two hK3, map_add, NumericalRingData.degree_algebraMap_mul,
    K3.degree_sqrtToddComp_two hK3, mukaiS]
  ring

/-! ### The asserted triple is the computed class

`IntegralMukaiData.mukaiVector` asserts the triple `(rank, c₁, s)` by formula. These three
statements say it is `ch(E)·√td(X)`.

The middle coordinate is compared **through the form** `b`, never by an equation in `Λ`. That is
deliberate and is the strongest available statement: in `IntegralMukaiData` the class `c₁` is a
bare function with no additivity and no relation to `A`, so there is no map to compare against.
`MukaiVector.lean`'s own `b_c₁_add` docstring explains why. -/

section Comparison

variable {Λ : Type*} [AddCommGroup Λ] (D : IntegralMukaiData V Λ)

/-- The rank coordinate needs no comparison; it holds by definition. -/
theorem mukaiVector_fst_eq (E : N) : (D.mukaiVector E).1 = V.rank E := rfl

/-- **The `c₁` coordinate is the linear component of `ch(E)·√td(X)`**, read through the form. -/
theorem b_mukaiVector_snd_eq_degree (hK3 : IsK3 V) (E F : N) :
    ((D.b (D.mukaiVector E).2.1 (D.c₁ F) : ℤ) : ℚ) =
      V.ring.degree (V.mukaiComp E 1 * V.chComp F 1) := by
  rw [mukaiComp_one hK3]
  exact D.b_spec E F

/-- **The `s` coordinate is the degree of the top component of `ch(E)·√td(X)`.**

This is the coordinate that was previously justified only in prose. -/
theorem mukaiVector_thd_eq_degree (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E : N) :
    (((D.mukaiVector E).2.2 : ℤ) : ℚ) = V.ring.degree (V.mukaiComp E 2) := by
  rw [degree_mukaiComp_two hK3]
  exact mukaiSInt_spec V hHRR hK3 E

end Comparison

end K3

end AlgebraicGeometry.Numerical
