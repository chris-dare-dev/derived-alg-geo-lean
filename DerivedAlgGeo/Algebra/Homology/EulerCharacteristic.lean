/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Homology.EulerCharacteristic

/-!
# The Euler characteristic is additive along a long exact sequence

Mathlib's `GradedObject.eulerChar c X = ∑ᶠ i, c.χ i * finrank R (X i)` is the Euler
characteristic of a graded object, with the signs supplied by `ComplexShape.EulerCharSigns`;
for `ComplexShape.up ℤ` the sign at `i` is `(-1)^i`. This file adds the arithmetic underneath
"`χ` is additive on distinguished triangles": for three `ℤ`-graded families of
finite-dimensional vector spaces assembled into a long exact sequence

`… → A i → B i → C i → A (i+1) → …`

the Euler characteristics satisfy `χ B = χ A + χ C` (`GradedObject.eulerChar_eq_add_of_exact`).
The families are unbundled, with linear maps between them, because that is how a homology
sequence of a linear functor presents them; the graded objects are `fun i => ModuleCat.of k (A i)`.

## Indices are `ℤ`, and there are no boundary hypotheses

This file deliberately does **not** reindex to `ℕ`, and the reason is worth stating.

Mathlib's `Module.sum_neg_one_pow_finrank_eq_zero_of_exact` handles a *single* exact sequence and is
finitely indexed. A transport objection is sometimes raised against `ℤ` — that over `ℤ` the
exactness hypothesis reads `ker (d i) = range (d (i-1))`, whose right-hand side lives in `V (i-1+1)`
rather than `V i`.  That objection does not apply here: spelled `ker (d (i+1)) = range (d i)` the
indices agree on the nose, and `(· + 1)` is surjective on `ℤ`, so no transport arises.  A finitely
indexed alternating sum is proved by *induction*, and an induction needs a base case.

The `ℤ`-indexed three-family statement below needs no induction. It telescopes by a translation of
the summation index — one `finsum_comp_equiv` along `Equiv.addRight 1` — and consequently carries
**no injectivity at the bottom, no surjectivity at the top, and no `Subsingleton` at either end**.
The bounded `ℕ`-indexed companion, which pays injectivity at the bottom and
`[Subsingleton (A (n+1))]` at the top, is `Module.sum_neg_one_pow_finrank_eq_zero_of_longExact` in
`Algebra/Exact/Sequence.lean`. Both statements are geometry-free linear algebra; geometric
Euler-characteristic additivity consumes the bounded one after constructing the relevant long exact
sequence.

Finiteness enters as finiteness of the *support* of each dimension function
rather than as a vanishing bound.  Given `Module.Finite`, over a division ring
the two are equivalent — `finrank = 0 ↔ Subsingleton`, and a finite subset of
`ℤ` is bounded — so this is a choice of spelling, not of strength.  It is the
form `finsum_add_distrib` consumes directly, which removes the `max`-of-three-
bounds bookkeeping a common window forces.

## `k` is a division ring

Not a field: commutativity is used nowhere.  `DivisionRing` is exactly what
`LinearMap.finrank_range_add_finrank_ker` asks for (it lives in a `section DivisionRing` in
`Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`), and it supplies the `StrongRankCondition`
that `LinearMap.finrank_range_le` needs for the support bounds.  Mathlib states
`Module.sum_neg_one_pow_finrank_eq_zero_of_exact` at the same level.

## What this file does not do

It says nothing about complexes, homology, `ModuleCat`, or triangulated
categories.  It is linear algebra; the categorical Euler form that motivated it
is assembled elsewhere.  It also proves no *vanishing* statement — the
three-family balance is what a distinguished triangle gives, and Mathlib already
has the vanishing form for a finite exact sequence.
-/

universe u v

open CategoryTheory Module

namespace GradedObject

variable {R : Type*} [Ring R] {ι : Type*}

/-- `finrankSupport` is also the support of the integer-valued rank function. -/
theorem finrankSupport_eq_support_intCast (X : GradedObject ι (ModuleCat R)) :
    finrankSupport X = Function.support fun i => (finrank R (X i) : ℤ) := by
  ext i
  simp [finrankSupport, Function.mem_support]

end GradedObject

namespace Module

variable {k : Type u} [DivisionRing k]

/-- A range's dimension is bounded by the source's, so its support sits inside the source's.
This is where `StrongRankCondition`, hence `DivisionRing`, is used, and it is the only place
the support side conditions come from. -/
theorem support_finrank_range_subset {ι : Type*} {V W : ι → Type v} [∀ i, AddCommGroup (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (V i)] [∀ i, Module k (W i)]
    [∀ i, Module.Finite k (V i)] (f : ∀ i, V i →ₗ[k] W i) :
    (Function.support fun i => (finrank k (LinearMap.range (f i)) : ℤ))
      ⊆ Function.support fun i => (finrank k (V i) : ℤ) := by
  intro i hi
  simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero] at hi ⊢
  exact fun h => hi (Nat.le_zero.mp (h ▸ LinearMap.finrank_range_le (f i)))

end Module

namespace GradedObject

variable {k : Type u} [DivisionRing k] {A B C : ℤ → Type v}
  [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
  [∀ i, Module k (A i)] [∀ i, Module k (B i)] [∀ i, Module k (C i)]
  [∀ i, Module.Finite k (A i)] [∀ i, Module.Finite k (B i)]
  [∀ i, Module.Finite k (C i)]

/-- The summand of `eulerChar (ComplexShape.up ℤ)` on an unbundled family: an implementation
helper for the telescoping proof below, not an API. -/
private noncomputable def altDim (V : ℤ → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (i : ℤ) : ℤ :=
  (i.negOnePow : ℤ) * finrank k (V i)

private theorem support_altDim (V : ℤ → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] :
    Function.support (altDim (k := k) V)
      = Function.support fun i => (finrank k (V i) : ℤ) := by
  ext i
  simp only [Function.mem_support, altDim, ne_eq, mul_eq_zero, not_or]
  exact ⟨fun h => h.2, fun h => ⟨Units.ne_zero _, h⟩⟩

/-- **The Euler characteristic is additive along a `ℤ`-indexed long exact sequence.**

`χ B = χ A + χ C` for `… → A i → B i → C i → A (i+1) → …` exact everywhere, with the signs
of `ComplexShape.up ℤ`. There is no injectivity hypothesis, no surjectivity hypothesis, and
no vanishing at either end: over `ℤ` the telescoping is a translation of the summation index
rather than an induction, so there are no boundary cases to state. Finiteness enters as
finiteness of the support of the integer-valued rank function, the form a homology sequence
of a linear functor supplies; `finrankSupport_eq_support_intCast` relates it to
`finrankSupport`. -/
theorem eulerChar_eq_add_of_exact
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i)
    (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i))
    (hδf : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (hA : (Function.support fun i => (finrank k (A i) : ℤ)).Finite)
    (hB : (Function.support fun i => (finrank k (B i) : ℤ)).Finite)
    (hC : (Function.support fun i => (finrank k (C i) : ℤ)).Finite) :
    eulerChar (ComplexShape.up ℤ) (fun i => ModuleCat.of k (B i))
      = eulerChar (ComplexShape.up ℤ) (fun i => ModuleCat.of k (A i))
        + eulerChar (ComplexShape.up ℤ) (fun i => ModuleCat.of k (C i)) := by
  change (∑ᶠ i : ℤ, altDim (k := k) B i)
    = (∑ᶠ i : ℤ, altDim (k := k) A i) + ∑ᶠ i : ℤ, altDim (k := k) C i
  -- The three rank families, and the alternating sums of each.
  set ρ : ℤ → ℤ := fun i => (i.negOnePow : ℤ) * finrank k (LinearMap.range (f i))
    with hρ
  set σ : ℤ → ℤ := fun i => (i.negOnePow : ℤ) * finrank k (LinearMap.range (g i))
    with hσ
  set d : ℤ → ℤ := fun i => (i.negOnePow : ℤ) * finrank k (LinearMap.range (δ i))
    with hd
  have hsupρ : (Function.support ρ).Finite := by
    refine hA.subset ?_
    rw [hρ, show (fun i : ℤ => (i.negOnePow : ℤ) * finrank k (LinearMap.range (f i)))
      = altDim (k := k) (fun i => LinearMap.range (f i)) from rfl, support_altDim]
    exact Module.support_finrank_range_subset f
  have hsupσ : (Function.support σ).Finite := by
    refine hB.subset ?_
    rw [hσ, show (fun i : ℤ => (i.negOnePow : ℤ) * finrank k (LinearMap.range (g i)))
      = altDim (k := k) (fun i => LinearMap.range (g i)) from rfl, support_altDim]
    exact Module.support_finrank_range_subset g
  have hsupd : (Function.support d).Finite := by
    refine hC.subset ?_
    rw [hd, show (fun i : ℤ => (i.negOnePow : ℤ) * finrank k (LinearMap.range (δ i)))
      = altDim (k := k) (fun i => LinearMap.range (δ i)) from rfl, support_altDim]
    exact Module.support_finrank_range_subset δ
  have hsupA : (Function.support (altDim (k := k) A)).Finite := by
    rw [support_altDim]; exact hA
  have hsupB : (Function.support (altDim (k := k) B)).Finite := by
    rw [support_altDim]; exact hB
  have hsupC : (Function.support (altDim (k := k) C)).Finite := by
    rw [support_altDim]; exact hC
  -- Pointwise rank--nullity at each of the three exact spots.
  have hb : ∀ i, altDim (k := k) B i = ρ i + σ i := by
    intro i
    simp only [altDim, hρ, hσ, (hfg i).finrank_eq_finrank_range_add_finrank_range]
    push_cast
    ring
  have hc : ∀ i, altDim (k := k) C i = σ i + d i := by
    intro i
    simp only [altDim, hσ, hd, (hgδ i).finrank_eq_finrank_range_add_finrank_range]
    push_cast
    ring
  have ha : ∀ i, altDim (k := k) A (i + 1) = -(d i) + ρ (i + 1) := by
    intro i
    simp only [altDim, hρ, hd,
      (hδf i).finrank_eq_finrank_range_add_finrank_range, Int.negOnePow_succ]
    push_cast
    ring
  -- Sum the three identities.
  have sB : ∑ᶠ i : ℤ, altDim (k := k) B i = (∑ᶠ i : ℤ, ρ i) + ∑ᶠ i : ℤ, σ i := by
    rw [← finsum_add_distrib hsupρ hsupσ]
    exact finsum_congr hb
  have sC : ∑ᶠ i : ℤ, altDim (k := k) C i = (∑ᶠ i : ℤ, σ i) + ∑ᶠ i : ℤ, d i := by
    rw [← finsum_add_distrib hsupσ hsupd]
    exact finsum_congr hc
  have sA : ∑ᶠ i : ℤ, altDim (k := k) A i = (∑ᶠ i : ℤ, ρ i) - ∑ᶠ i : ℤ, d i := by
    have shift : ∑ᶠ i : ℤ, altDim (k := k) A (i + 1) = ∑ᶠ i : ℤ, altDim (k := k) A i :=
      finsum_comp_equiv (Equiv.addRight (1 : ℤ))
    have shiftρ : ∑ᶠ i : ℤ, ρ (i + 1) = ∑ᶠ i : ℤ, ρ i :=
      finsum_comp_equiv (Equiv.addRight (1 : ℤ))
    have hneg : (Function.support fun i => -(d i)).Finite := by
      simpa [Function.support_neg] using hsupd
    have hsupρ' : (Function.support fun i => ρ (i + 1)).Finite := by
      have hpre : (Function.support fun i : ℤ => ρ (i + 1))
          = (fun x : ℤ => x + 1) ⁻¹' Function.support ρ := rfl
      rw [hpre]
      exact hsupρ.preimage ((Equiv.addRight (1 : ℤ)).injective.injOn)
    calc ∑ᶠ i : ℤ, altDim (k := k) A i
        = ∑ᶠ i : ℤ, altDim (k := k) A (i + 1) := shift.symm
      _ = ∑ᶠ i : ℤ, (-(d i) + ρ (i + 1)) := finsum_congr ha
      _ = (∑ᶠ i : ℤ, -(d i)) + ∑ᶠ i : ℤ, ρ (i + 1) := finsum_add_distrib hneg hsupρ'
      _ = -(∑ᶠ i : ℤ, d i) + ∑ᶠ i : ℤ, ρ i := by rw [finsum_neg_distrib, shiftρ]
      _ = (∑ᶠ i : ℤ, ρ i) - ∑ᶠ i : ℤ, d i := by ring
  rw [sA, sB, sC]
  ring

end GradedObject
