/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Alternating sums along long exact sequences

For three `ℤ`-indexed families of finite-dimensional vector spaces assembled
into a long exact sequence

`… → A i → B i → C i → A (i+1) → …`

the alternating sums of dimensions satisfy `Σ ε·dim B = Σ ε·dim A + Σ ε·dim C`,
where `ε i = (-1)^i`.  This is the arithmetic underneath "`χ` is additive on
distinguished triangles".

## Indices are `ℤ`, and there are no boundary hypotheses

This file deliberately does **not** reindex to `ℕ`, and the reason is worth
stating because a sibling file reaches the opposite conclusion.

`LinearAlgebra/AlternatingSum.lean` handles a *single* family and is `ℕ`-indexed.
Its docstring explains that choice by a transport objection — that over `ℤ` the
exactness hypothesis reads `ker (d i) = range (d (i-1))`, whose right-hand side
lives in `V (i-1+1)` rather than `V i`.  That objection does not apply here, and
on inspection it does not apply there either: spelled `ker (d (i+1)) = range (d i)`
the indices agree on the nose, and `(· + 1)` is surjective on `ℤ`, so no
transport arises.  The real reason that file is `ℕ`-indexed is that a
single-family alternating sum is proved by *induction*, and an induction needs a
base case.

The `ℤ`-indexed three-family statement below needs no induction.  It telescopes by a
translation of the summation index — one `finsum_comp_equiv` along
`Equiv.addRight 1` — and consequently carries **no injectivity at the bottom, no
surjectivity at the top, and no `Subsingleton` at either end**.  This file also
owns the bounded `ℕ`-indexed companion, which pays injectivity at the bottom and
`[Subsingleton (A (n+1))]` at the top.  Both statements are geometry-free
linear algebra; geometric Euler-characteristic additivity consumes the bounded
one after constructing the relevant long exact sequence.

Finiteness enters as finiteness of the *support* of each dimension function
rather than as a vanishing bound.  Given `Module.Finite`, over a division ring
the two are equivalent — `finrank = 0 ↔ Subsingleton`, and a finite subset of
`ℤ` is bounded — so this is a choice of spelling, not of strength.  It is the
form `finsum_add_distrib` consumes directly, which removes the `max`-of-three-
bounds bookkeeping a common window forces.

## `k` is a division ring

Not a field: commutativity is used nowhere.  `DivisionRing` is exactly what
`LinearMap.finrank_range_add_finrank_ker` asks for (it lives in a
`section DivisionRing` in `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean`),
and it supplies the `StrongRankCondition` that `LinearMap.finrank_range_le`
needs for the support bounds.  Mathlib states its own alternating-sum corollary
at the same level (`Module.sum_neg_one_pow_finrank_eq_zero_of_exact`).

## What this file does not do

It says nothing about complexes, homology, `ModuleCat`, or triangulated
categories.  It is linear algebra; the categorical Euler form that motivated it
is assembled elsewhere.  It also proves no *vanishing* statement — the
three-family balance is what a distinguished triangle gives, and Mathlib already
has the vanishing form for a finite exact sequence.
-/

universe u v w₁ w₂

namespace DerivedAlgGeo.LinearAlgebra

open Module Function

section RankNullity

variable {k : Type u} [DivisionRing k]

/-- Rank--nullity rewritten at an exact middle term: an exact `A → B → C`
splits `dim B` into the two ranks around it.

It is public because both the bounded `ℕ` and the unbounded `ℤ`
alternating-sum arguments consume it. -/
theorem finrank_eq_range_add_range {A : Type v} {B : Type w₁} {C : Type w₂} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module k A] [Module k B] [Module k C]
    [Module.Finite k B] (f : A →ₗ[k] B) (g : B →ₗ[k] C) (h : Function.Exact f g) :
    finrank k B = finrank k (LinearMap.range f) + finrank k (LinearMap.range g) := by
  have hr := g.finrank_range_add_finrank_ker
  rw [h.linearMap_ker_eq] at hr
  omega

end RankNullity

section LongExact

variable {k : Type u} [DivisionRing k] {A B C : ℤ → Type v}
  [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
  [∀ i, Module k (A i)] [∀ i, Module k (B i)] [∀ i, Module k (C i)]
  [∀ i, Module.Finite k (A i)] [∀ i, Module.Finite k (B i)]
  [∀ i, Module.Finite k (C i)]

/-- The alternating dimension function of a `ℤ`-indexed family. -/
noncomputable def altDim (V : ℤ → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (i : ℤ) : ℤ :=
  (i.negOnePow : ℤ) * finrank k (V i)

/-- The support of `altDim` is the support of the dimension function: the sign
is a unit, so multiplying by it changes no support. -/
theorem support_altDim (V : ℤ → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] :
    Function.support (altDim (k := k) V)
      = Function.support fun i => (finrank k (V i) : ℤ) := by
  ext i
  simp only [Function.mem_support, altDim, ne_eq, mul_eq_zero, not_or]
  exact ⟨fun h => h.2, fun h => ⟨Units.ne_zero _, h⟩⟩

/-- A range's dimension is bounded by the source's, so its support sits inside
the source's.  This is where `StrongRankCondition` — hence `DivisionRing` — is
used, and it is the only place the support side conditions come from. -/
theorem support_range_subset {V W : ℤ → Type v} [∀ i, AddCommGroup (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module k (V i)] [∀ i, Module k (W i)]
    [∀ i, Module.Finite k (V i)] (f : ∀ i, V i →ₗ[k] W i) :
    (Function.support fun i => (finrank k (LinearMap.range (f i)) : ℤ))
      ⊆ Function.support fun i => (finrank k (V i) : ℤ) := by
  intro i hi
  simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero] at hi ⊢
  exact fun h => hi (Nat.le_zero.mp (h ▸ LinearMap.finrank_range_le (f i)))

/-- **The alternating sum along a `ℤ`-indexed long exact sequence balances.**

`Σ ε·dim B = Σ ε·dim A + Σ ε·dim C` for

`… → A i → B i → C i → A (i+1) → …`

exact everywhere.  There is no injectivity hypothesis, no surjectivity
hypothesis, and no vanishing at either end: over `ℤ` the telescoping is a
translation of the summation index rather than an induction, so there are no
boundary cases to state.  See the module docstring for why that is the whole
point of indexing by `ℤ`. -/
theorem finsum_altDim_middle
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i)
    (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i))
    (hδf : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (hA : (Function.support fun i => (finrank k (A i) : ℤ)).Finite)
    (hB : (Function.support fun i => (finrank k (B i) : ℤ)).Finite)
    (hC : (Function.support fun i => (finrank k (C i) : ℤ)).Finite) :
    ∑ᶠ i : ℤ, altDim (k := k) B i
      = (∑ᶠ i : ℤ, altDim (k := k) A i) + ∑ᶠ i : ℤ, altDim (k := k) C i := by
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
    exact support_range_subset f
  have hsupσ : (Function.support σ).Finite := by
    refine hB.subset ?_
    rw [hσ, show (fun i : ℤ => (i.negOnePow : ℤ) * finrank k (LinearMap.range (g i)))
      = altDim (k := k) (fun i => LinearMap.range (g i)) from rfl, support_altDim]
    exact support_range_subset g
  have hsupd : (Function.support d).Finite := by
    refine hC.subset ?_
    rw [hd, show (fun i : ℤ => (i.negOnePow : ℤ) * finrank k (LinearMap.range (δ i)))
      = altDim (k := k) (fun i => LinearMap.range (δ i)) from rfl, support_altDim]
    exact support_range_subset δ
  have hsupA : (Function.support (altDim (k := k) A)).Finite := by
    rw [support_altDim]; exact hA
  have hsupB : (Function.support (altDim (k := k) B)).Finite := by
    rw [support_altDim]; exact hB
  have hsupC : (Function.support (altDim (k := k) C)).Finite := by
    rw [support_altDim]; exact hC
  -- Pointwise rank--nullity at each of the three exact spots.
  have hb : ∀ i, altDim (k := k) B i = ρ i + σ i := by
    intro i
    simp only [altDim, hρ, hσ, finrank_eq_range_add_range (f i) (g i) (hfg i)]
    push_cast
    ring
  have hc : ∀ i, altDim (k := k) C i = σ i + d i := by
    intro i
    simp only [altDim, hσ, hd, finrank_eq_range_add_range (g i) (δ i) (hgδ i)]
    push_cast
    ring
  have ha : ∀ i, altDim (k := k) A (i + 1) = -(d i) + ρ (i + 1) := by
    intro i
    simp only [altDim, hρ, hd,
      finrank_eq_range_add_range (δ i) (f (i + 1)) (hδf i), Int.negOnePow_succ]
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

end LongExact

section BoundedLongExact

variable {k : Type u} [Field k]
variable (A : ℕ → Type v) (B : ℕ → Type w₁) (C : ℕ → Type w₂)
  [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
  [∀ i, Module k (A i)] [∀ i, Module k (B i)] [∀ i, Module k (C i)]
  [∀ i, Module.Finite k (A i)] [∀ i, Module.Finite k (B i)] [∀ i, Module.Finite k (C i)]
  (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i)
  (δ : ∀ i, C i →ₗ[k] A (i + 1))

/-- Alternating finite-dimensional dimensions cancel along a bounded long exact sequence.
The endpoint hypothesis is stated as vanishing of the next `A` term, which makes the final
connecting map surjective onto zero. -/
theorem alternating_finrank_eq_zero_of_exact
    (hinj : Function.Injective (f 0))
    (hexact₂ : ∀ i, Function.Exact (f i) (g i))
    (hexact₃ : ∀ i, Function.Exact (g i) (δ i))
    (hexact₁ : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (n : ℕ) [Subsingleton (A (n + 1))] :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i *
      ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) = 0 := by
  have hA₀ : Module.finrank k (A 0) = Module.finrank k (LinearMap.range (f 0)) :=
    (LinearMap.finrank_range_of_inj hinj).symm
  have hB (i : ℕ) : Module.finrank k (B i) =
      Module.finrank k (LinearMap.range (f i)) +
        Module.finrank k (LinearMap.range (g i)) :=
    finrank_eq_range_add_range (f i) (g i) (hexact₂ i)
  have hC (i : ℕ) : Module.finrank k (C i) =
      Module.finrank k (LinearMap.range (g i)) +
        Module.finrank k (LinearMap.range (δ i)) :=
    finrank_eq_range_add_range (g i) (δ i) (hexact₃ i)
  have hA (i : ℕ) : Module.finrank k (A (i + 1)) =
      Module.finrank k (LinearMap.range (δ i)) +
        Module.finrank k (LinearMap.range (f (i + 1))) :=
    finrank_eq_range_add_range (δ i) (f (i + 1)) (hexact₁ i)
  have hδn : Module.finrank k (LinearMap.range (δ n)) = 0 := by
    letI : Subsingleton (LinearMap.range (δ n)) := inferInstance
    exact Module.finrank_zero_of_subsingleton
  have hpartial (m : ℕ) :
      ∑ i ∈ Finset.range (m + 1), (-1 : ℤ) ^ i *
        ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) +
          Module.finrank k (C i)) =
        (-1 : ℤ) ^ m * Module.finrank k (LinearMap.range (δ m)) := by
    induction m with
    | zero =>
        simp only [Nat.reduceAdd, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul]
        have hA₀' := hA₀
        have hB' := hB 0
        have hC' := hC 0
        push_cast at hA₀' hB' hC'
        omega
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have hA' := hA m
        have hB' := hB (m + 1)
        have hC' := hC (m + 1)
        have htriple :
            (Module.finrank k (A (m + 1)) : ℤ) - Module.finrank k (B (m + 1)) +
                Module.finrank k (C (m + 1)) =
              Module.finrank k (LinearMap.range (δ m)) +
                Module.finrank k (LinearMap.range (δ (m + 1))) := by
          omega
        rw [htriple, pow_succ]
        ring
  rw [hpartial n, hδn, Int.ofNat_zero, mul_zero]

end BoundedLongExact

end DerivedAlgGeo.LinearAlgebra
