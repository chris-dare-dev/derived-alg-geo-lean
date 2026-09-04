/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import DerivedAlgGeo.LinearAlgebra.Lattice.Arithmetic.TorsionFree

/-!
# Isotropic sequences in an integral bilinear lattice

A sequence `v : Fin n → Λ` in a `ℤ`-bilinear lattice is **isotropic** when
`⟨v i, v j⟩ = 1 - δᵢⱼ`: every member is isotropic and every distinct ordered
pair pairs to `1`. For `n = 10` this is the combinatorial skeleton of the
half-fiber configurations on an Enriques surface (Li–Nuer–Stellari–Zhao,
arXiv:1912.04332, §2.3), but nothing here mentions a surface: every statement
is lattice arithmetic, true whether or not any geometry exists — the same
discipline `Lattice/Mukai/Basic.lean` records for the Mukai extension.

Neither existing isotropy notion is reusable here, which is why a new
predicate appears at all: `Mukai.IsIsotropic` is bound to the Mukai
extension's own `pairing`, and `IntegralLattice.NumLattice` names the rank-two
numerical lattice `Fin 2 → ℤ`, not an ambient carrier.

## Main definitions

* `IsIsotropicSequence` — the predicate.
* `hyperbolicPairing` — the Gram matrix `!![0, 1; 1, 0]` of the hyperbolic
  plane `U`, as a bilinear map on `Fin 2 → ℤ`.

## Main results

* `IsIsotropicSequence.linearIndependent` — for `n ≥ 2` an isotropic sequence
  is linearly independent over `ℤ`, through the separation statement
  `coeffs_eq_zero_of_pairing_smul_sum_eq_zero` (the Gram argument in elementary
  form).
* `IsIsotropicSequence.pairing_sum_left`, `pairing_sum_right`,
  `pairing_sum_sum` — the sum-vector identities `⟨s, v j⟩ = ⟨v j, s⟩ = n - 1`
  and `⟨s, s⟩ = n(n - 1)`.
* two geometry-free inhabitants: the hyperbolic plane carries an isotropic
  2-sequence, and any lattice carries the degenerate singleton.

## Implementation notes

**Symmetry is not assumed.** The two defining clauses quantify over all
ordered pairs, so `⟨v i, v j⟩` and `⟨v j, v i⟩` are each `1` by hypothesis and
no symmetry of `b` enters any proof below. A symmetric lattice loses nothing;
an asymmetric pairing (an Euler form before symmetrization) can still carry an
isotropic sequence. The left and right sum identities are both provided for
exactly this reason.

**What is deferred.** For `s = ∑ i, v i` and `n = 10` the identities read
`⟨s, v j⟩ = 9` and `⟨s, s⟩ = 90`, which are the shadows of the Fano class
`Δ = s/3` with `Δ·F_j = 3` and `Δ² = 10` — but division by `3` is a statement
about divisibility *in the lattice*, not about the pairing, and is deferred
until the rank-ten Enriques lattice exists to state it in.

## References

* Li, Nuer, Stellari, Zhao, *A refined Derived Torelli Theorem for Enriques
  surfaces*, arXiv:1912.04332, §2.3.

## Tags

isotropic sequence, integral lattice, Enriques surface, hyperbolic plane
-/

namespace IntegralLattice

variable {Λ : Type*} [AddCommGroup Λ] (b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ)

/-- An **isotropic sequence**: `⟨v i, v j⟩ = 1 - δᵢⱼ`, stated as two clauses
so neither needs an `if`. Both clauses range over ordered pairs, which is why
no symmetry hypothesis on `b` appears here or in any consequence. -/
structure IsIsotropicSequence {n : ℕ} (v : Fin n → Λ) : Prop where
  /-- Every member of the sequence is isotropic. -/
  self_isotropic : ∀ i, b (v i) (v i) = 0
  /-- Every ordered pair of distinct members pairs to `1`. -/
  pairwise_one : ∀ i j, i ≠ j → b (v i) (v j) = 1

namespace IsIsotropicSequence

variable {b} {n : ℕ} {v : Fin n → Λ} (h : IsIsotropicSequence b v)

include h

/-- The two clauses in `if` normal form, for summing over an index. No
symmetry is needed to state either orientation: the `if` is on the index
pair, and `pairwise_one` covers both orders by hypothesis. -/
theorem pairing_ite (i j : Fin n) :
    b (v i) (v j) = if i = j then 0 else 1 := by
  by_cases hij : i = j
  · simp [hij, h.self_isotropic j]
  · simp [hij, h.pairwise_one i j hij]

/-- **The weighted sum identity**: pairing `∑ gᵢ vᵢ` against `v j` reads off
the coefficient sum minus the `j`-th coefficient. This is the single
computation behind every result below — the unweighted identity is `g = 1`
and linear independence is the statement that it separates coefficients. -/
theorem pairing_smul_sum_left (g : Fin n → ℤ) (j : Fin n) :
    b (∑ i, g i • v i) (v j) = (∑ i, g i) - g j := by
  rw [map_sum, LinearMap.sum_apply]
  calc (∑ i, b (g i • v i) (v j))
      = ∑ i, if i = j then 0 else g i := Finset.sum_congr rfl fun i _ => by
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, h.pairing_ite i j]
        by_cases hij : i = j <;> simp [hij]
    _ = (∑ i ∈ Finset.univ.erase j, if i = j then 0 else g i)
          + if j = j then 0 else g j :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
    _ = ∑ i ∈ Finset.univ.erase j, g i := by
        rw [if_pos rfl, add_zero]
        exact Finset.sum_congr rfl fun i hi =>
          if_neg (Finset.ne_of_mem_erase hi)
    _ = (∑ i, g i) - g j := by
        rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ j)]
        ring

/-- **The sum vector pairs to `n - 1` against every member.** For the
Enriques configuration `n = 10` this is the `⟨s, F_j⟩ = 9` identity behind
`Δ·F_j = 3`; see the module docstring for why the division by `3` is not
taken here. -/
theorem pairing_sum_left (j : Fin n) :
    b (∑ i, v i) (v j) = (n : ℤ) - 1 := by
  have := h.pairing_smul_sum_left (fun _ => 1) j
  simpa [Finset.sum_const, Finset.card_univ] using this

/-- The right-slot companion of `pairing_sum_left`, provided because no
symmetry of `b` is assumed anywhere in this file. -/
theorem pairing_sum_right (j : Fin n) :
    b (v j) (∑ i, v i) = (n : ℤ) - 1 := by
  rw [map_sum (b (v j))]
  calc (∑ i, b (v j) (v i))
      = ∑ i, if i = j then 0 else (1 : ℤ) := Finset.sum_congr rfl fun i _ => by
        by_cases hij : i = j
        · simp [hij, h.self_isotropic j]
        · simp [hij, h.pairwise_one j i (Ne.symm hij)]
    _ = (∑ i ∈ Finset.univ.erase j, if i = j then 0 else (1 : ℤ))
          + if j = j then 0 else 1 :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
    _ = ∑ _i ∈ Finset.univ.erase j, (1 : ℤ) := by
        rw [if_pos rfl, add_zero]
        exact Finset.sum_congr rfl fun i hi =>
          if_neg (Finset.ne_of_mem_erase hi)
    _ = (n : ℤ) - 1 := by
        rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
          Nat.cast_sub j.pos, Nat.cast_one]

/-- **The self-pairing of the sum vector is `n(n - 1)`.** For `n = 10` this
is the `⟨s, s⟩ = 90` identity behind `Δ² = 10`. -/
theorem pairing_sum_sum :
    b (∑ i, v i) (∑ i, v i) = (n : ℤ) * ((n : ℤ) - 1) := by
  rw [map_sum (b (∑ i, v i))]
  calc (∑ j, b (∑ i, v i) (v j))
      = ∑ _j : Fin n, ((n : ℤ) - 1) :=
        Finset.sum_congr rfl fun j _ => h.pairing_sum_left j
    _ = (n : ℤ) * ((n : ℤ) - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]

/-- **An isotropic sequence of length at least two separates coefficients**:
if `∑ gᵢ vᵢ` pairs to zero against every member, every coefficient vanishes.
This is non-degeneracy of the pairing on the span of the sequence, stated
without mentioning the span; `linearIndependent` is its immediate consumer,
and the Torelli-lane numerical steps consume it directly when the vanishing
comes from geometry rather than from a linear relation.

By `pairing_smul_sum_left`, the hypothesis says every coefficient equals the
common sum `S`; summing again gives `S = nS`, and `n ≥ 2` forces `S = 0` in
`ℤ`. -/
theorem coeffs_eq_zero_of_pairing_smul_sum_eq_zero (hn : 2 ≤ n) (g : Fin n → ℤ)
    (hg : ∀ j, b (∑ i, g i • v i) (v j) = 0) : ∀ i, g i = 0 := by
  have key : ∀ j, (∑ i, g i) - g j = 0 := fun j => by
    have := hg j
    rwa [h.pairing_smul_sum_left g j] at this
  have hS : (∑ i, g i) = 0 := by
    have hsum : (∑ j, g j) = ∑ _j : Fin n, (∑ i, g i) :=
      Finset.sum_congr rfl fun j _ => by
        have := key j; omega
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      at hsum
    have hfactor : ((n : ℤ) - 1) * (∑ i, g i) = 0 := by
      rw [sub_mul, one_mul, ← hsum, sub_self]
    have hne : ((n : ℤ) - 1) ≠ 0 := by omega
    exact (mul_eq_zero.1 hfactor).resolve_left hne
  intro i
  have := key i
  omega

/-- **An isotropic sequence of length at least two is linearly independent
over `ℤ`.** The hypothesis `2 ≤ n` is necessary at `n = 1`: the single vector
may be `0`, as the degenerate inhabitant below shows (at `n = 0` the
statement is vacuous). -/
theorem linearIndependent (hn : 2 ≤ n) : LinearIndependent ℤ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  exact h.coeffs_eq_zero_of_pairing_smul_sum_eq_zero hn g fun j => by rw [hg]; simp

end IsIsotropicSequence

/-! ### Two geometry-free inhabitants

The hyperbolic witness is the honest one: `U`'s standard basis is a genuine
isotropic 2-sequence, and it is the seed from which the Enriques lattice
`U ⊕ E₈(−1)` will grow its length-ten sequences. The singleton `0` is the
degenerate boundary case, and it is why `linearIndependent` needs `2 ≤ n`. -/

/-- The hyperbolic pairing on `ℤ²`: `⟨x, y⟩ = x₀y₁ + x₁y₀`, the Gram matrix
`!![0, 1; 1, 0]` of the hyperbolic plane `U`. -/
def hyperbolicPairing : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => x 0 * y 1 + x 1 * y 0)
    (fun x x' y => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp only [Pi.add_apply]; ring)
    (fun c x y => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp]
theorem hyperbolicPairing_apply (x y : Fin 2 → ℤ) :
    hyperbolicPairing x y = x 0 * y 1 + x 1 * y 0 :=
  rfl

/-- The standard basis of the hyperbolic plane is an isotropic 2-sequence:
`⟨e, e⟩ = ⟨f, f⟩ = 0` and `⟨e, f⟩ = ⟨f, e⟩ = 1`. -/
theorem isIsotropicSequence_hyperbolic :
    IsIsotropicSequence hyperbolicPairing ![![1, 0], ![0, 1]] := by
  constructor
  · intro i
    fin_cases i <;> simp
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- Any lattice carries the degenerate singleton sequence `![0]`: the
self-pairing clause is `b 0 0 = 0` and the pairwise clause is vacuous. This
is the boundary case excluded by `linearIndependent`'s `2 ≤ n`. -/
theorem isIsotropicSequence_zero_singleton :
    IsIsotropicSequence b ![(0 : Λ)] := by
  constructor
  · intro i
    fin_cases i
    simp
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij

end IntegralLattice
