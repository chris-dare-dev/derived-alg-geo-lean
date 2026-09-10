/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.VectorClass
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.EulerPairing

/-!
# The Euler pairing is the integral of Mukai classes, on a K3

`χ(E,F) = ∫_X v(E)^∨·v(F)`, with `v(E) = ch(E)·√td(X)` the actual class from
`Mukai/VectorClass.lean`. This is the identity that makes `√td(X)` earn its place, and it is the
form Mukai's paper uses and a Fourier–Mukai comparison needs.

`EulerPairing.lean` already proves `χ(E,F) = −⟨v(E),v(F)⟩` against the *explicit formula* for the
Mukai pairing. That is a different statement: it compares against a formula, this compares against
the class.

## The sign, stated out loud rather than left to the reader

**The headline identity carries no minus sign**, and this is the one thing here that is easy to
get wrong — a draft of this lane wrote one and propagated it into three further statements.

The two objects differ by a sign, and conflating them is where a spurious minus comes from:

* the **Mukai pairing** `⟨v,w⟩`, which `EulerPairing.lean` defines by the explicit formula
  `∫c₁(E)c₁(F) − r_E·s_F − r_F·s_E`;
* the **integral of the dual product** `∫ v^∨·w`, which is this file's `mukaiIntegral`.

They are related by `⟨v,w⟩ = −∫ v^∨·w`. So the literature identity `χ(E,F) = −⟨v(E),v(F)⟩` and
this file's `χ(E,F) = +∫ v(E)^∨·v(F)` are the same statement, and both are true.

The diagonal is the cross-check: `chi₂_self` gives `χ(E,E) = 2r² − ∫Δ` while `mukaiSelfPairing_eq`
gives `⟨v,v⟩ = ∫Δ − 2r²`, so `mukaiIntegral E E = −mukaiSelfPairing E`. If a statement here came
out with the opposite sign, the error would be in its proof and not in this note.

## The dual, and why it is the literature's involution on a K3

`mukaiDual` uses `chDual`'s convention, `chᵢ(E^∨) = (−1)ⁱchᵢ(E)`, applied to the Mukai components.
The literature's Mukai involution is `(r,c,s)^∨ = (r,−c,s)`. On a K3 the two agree, because the
odd component of `√td(X)` vanishes and so `√td(X)` is its own dual.

## Two dimensions only, and why

`mukaiDual` is defined for every `n`, but nothing relates it to `χ` outside `IsK3`. On a general
surface `χ(E,F) ≠ ∫ v(E)^∨·v(F)`, because `td₁ ≠ 0` makes `(√td)^∨ ≠ √td`;
`Surface.chi₂_sub_chi₂_swap` already measures the resulting asymmetry. That is the whole story and
this file stops there.
-/

universe u v

open Finset

namespace AlgebraicGeometry.Numerical

variable {n : ℕ} {A : Type u} [CommRing A] [Algebra ℚ A]
variable {N : Type v} [AddCommGroup N]

namespace NumericalVarietyData

variable (V : NumericalVarietyData n A N)

/-- **The dual Mukai class** `v(E)^∨`, alternating in codimension, exactly as `chDual` is. -/
noncomputable def mukaiDual (E : N) : A :=
  ∑ i ∈ range (n + 1), (-1 : ℚ) ^ i • V.mukaiComp E i

theorem mukaiDual_add (E F : N) :
    V.mukaiDual (E + F) = V.mukaiDual E + V.mukaiDual F := by
  simp only [mukaiDual, V.mukaiComp_add, smul_add]
  exact Finset.sum_add_distrib

end NumericalVarietyData

namespace K3

open NumericalVarietyData

variable (V : NumericalVarietyData 2 A N)

/-- **The integral of the dual product**, `∫_X v(E)^∨·v(F)`.

Note the name: this is *not* the Mukai pairing. The two differ by a sign; see the module
docstring. -/
noncomputable def mukaiIntegral (E F : N) : ℚ :=
  V.ring.degree (V.mukaiDual E * V.mukaiClass F)

variable {V}

/-- The dual class on a surface, written out. -/
theorem mukaiDual_eq (E : N) :
    V.mukaiDual E = V.mukaiComp E 0 - V.mukaiComp E 1 + V.mukaiComp E 2 := by
  simp [NumericalVarietyData.mukaiDual, Finset.sum_range_succ]
  ring

/-- The Mukai class on a surface, written out. -/
theorem mukaiClass_eq (E : N) :
    V.mukaiClass E = V.mukaiComp E 0 + V.mukaiComp E 1 + V.mukaiComp E 2 := by
  simp [NumericalVarietyData.mukaiClass, Finset.sum_range_succ]

/-- **The expansion.** Only the three pairs with `i + j = 2` survive the integral, and the middle
one carries the sign of the dual. -/
theorem mukaiIntegral_eq (hK3 : IsK3 V) (E F : N) :
    mukaiIntegral V E F =
      (V.rank E : ℚ) * mukaiS V F - V.ring.degree (V.chComp E 1 * V.chComp F 1)
        + (V.rank F : ℚ) * mukaiS V E := by
  have z : ∀ i j : ℕ, i + j ≠ 2 →
      V.ring.degree (V.mukaiComp E i * V.mukaiComp F j) = 0 :=
    fun i j h ↦ V.degree_mukaiComp_mul_mukaiComp_eq_zero E F h
  rw [mukaiIntegral, mukaiDual_eq, mukaiClass_eq]
  simp only [sub_mul, add_mul, mul_add, map_add, map_sub]
  rw [z 0 0 (by norm_num), z 0 1 (by norm_num), z 1 0 (by norm_num), z 1 2 (by norm_num),
    z 2 1 (by norm_num), z 2 2 (by norm_num)]
  rw [mukaiComp_zero, mukaiComp_zero, mukaiComp_one hK3, mukaiComp_one hK3,
    NumericalRingData.degree_algebraMap_mul, degree_mukaiComp_two hK3]
  have hlast : V.ring.degree (V.mukaiComp E 2 * algebraMap ℚ A (V.rank F : ℚ)) =
      (V.rank F : ℚ) * mukaiS V E := by
    rw [mul_comm, NumericalRingData.degree_algebraMap_mul, degree_mukaiComp_two hK3]
  rw [hlast]
  ring

/-- **The headline.** `χ(E,F) = ∫_X v(E)^∨·v(F)`, with **no** minus sign; see the module
docstring on why, and on why `chi₂_eq_neg_mukaiPairing` carries one. -/
theorem chi₂_eq_mukaiIntegral (hK3 : IsK3 V) (E F : N) :
    V.chi₂ E F = mukaiIntegral V E F := by
  rw [chi₂_eq_neg_mukaiPairing V hK3, mukaiIntegral_eq hK3, mukaiPairing]
  ring

/-- The integral is symmetric, because `√td(X)` is its own dual on a K3. -/
theorem mukaiIntegral_comm (hK3 : IsK3 V) (E F : N) :
    mukaiIntegral V E F = mukaiIntegral V F E := by
  rw [mukaiIntegral_eq hK3, mukaiIntegral_eq hK3, mul_comm (V.chComp E 1)]
  ring

/-- On the diagonal the integral is **minus** the Mukai self-pairing. This is the cross-check the
module docstring names. -/
theorem mukaiIntegral_self (hK3 : IsK3 V) (E : N) :
    mukaiIntegral V E E = -mukaiSelfPairing V E := by
  rw [mukaiIntegral_eq hK3, mukaiSelfPairing]
  ring

/-- Consequently the integral is `2·rank² − ∫Δ`, through the existing discriminant comparison. -/
theorem mukaiIntegral_self_eq (hK3 : IsK3 V) (E : N) :
    mukaiIntegral V E E = 2 * (V.rank E : ℚ) ^ 2 - V.ring.degree (V.discriminant E) := by
  rw [mukaiIntegral_self hK3, mukaiSelfPairing_eq V]
  ring

/-- **The sign, as a theorem.** The integral of the dual product is minus the Mukai pairing. -/
theorem mukaiIntegral_eq_neg_mukaiPairing (hK3 : IsK3 V) (E F : N) :
    mukaiIntegral V E F = -mukaiPairing V E F := by
  rw [mukaiIntegral_eq hK3, mukaiPairing]
  ring

/-! ### The three-way closure

The abstract lattice pairing, the explicit formula and the integral of classes are one number. -/

section Lattice

variable {Λ : Type*} [AddCommGroup Λ] (D : IntegralMukaiData V Λ)

/-- **The abstract Mukai pairing on the lattice is minus the integral of classes.**

Composing `pairing_mukaiVector`, which lands on the explicit formula, with
`mukaiIntegral_eq_neg_mukaiPairing`. This is the one place the sign is visible from both sides at
once. -/
theorem pairing_eq_neg_mukaiIntegral (hHRR : V.SatisfiesHRR) (hK3 : IsK3 V) (E F : N) :
    (Mukai.pairing D.b (D.mukaiVector E) (D.mukaiVector F) : ℚ) = -mukaiIntegral V E F := by
  rw [D.pairing_mukaiVector hHRR hK3, mukaiIntegral_eq_neg_mukaiPairing hK3, neg_neg]

end Lattice

end K3

end AlgebraicGeometry.Numerical
