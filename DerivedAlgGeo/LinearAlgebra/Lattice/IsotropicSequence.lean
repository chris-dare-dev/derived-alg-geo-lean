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

A sequence `v : Fin n → N` in a `ℤ`-bilinear lattice is **isotropic** when
`⟨v i, v j⟩ = 1 - δᵢⱼ`: every member is isotropic and every distinct pair
pairs to `1`. For `n = 10` this is the combinatorial skeleton of the
half-fiber configurations on an Enriques surface (Li–Nuer–Stellari–Zhao,
arXiv:1912.04332, §2.3), but nothing here mentions a surface: every statement
is lattice arithmetic, true whether or not any geometry exists — the same
discipline `Lattice/Mukai/Basic.lean` records for the Mukai extension.

## Symmetry is not assumed

The two defining clauses quantify over all ordered pairs, so `⟨v i, v j⟩` and
`⟨v j, v i⟩` are each `1` by hypothesis and no symmetry of `b` enters any
proof below. A symmetric lattice loses nothing; an asymmetric pairing (an
Euler form before symmetrization) can still carry an isotropic sequence.

## The sum vector, and what is deferred

For `s = ∑ i, v i` the pairing identities `⟨s, v j⟩ = n - 1` and
`⟨s, s⟩ = n(n - 1)` are proved here. In the Enriques lattice with `n = 10`
these read `⟨s, v j⟩ = 9` and `⟨s, s⟩ = 90`, which are the shadows of the Fano
class `Δ = s/3` with `Δ·F_j = 3` and `Δ² = 10` — but division by `3` is a
statement about divisibility *in the lattice*, not about the pairing, and is
deferred until the rank-ten Enriques lattice exists to state it in.

## Main definitions

* `IsIsotropicSequence` — the predicate.

## Main results

* `IsIsotropicSequence.linearIndependent` — for `n ≥ 2` an isotropic sequence
  is linearly independent over `ℤ`; the Gram matrix argument in elementary
  form.
* `IsIsotropicSequence.pairing_sum_left`, `pairing_sum_sum` — the sum-vector
  identities.
* two geometry-free inhabitants: the hyperbolic plane carries an isotropic
  2-sequence, and any lattice carries the degenerate singleton.

## References

* Li, Nuer, Stellari, Zhao, *A refined Derived Torelli Theorem for Enriques
  surfaces*, arXiv:1912.04332, §2.3.

## Tags

isotropic sequence, integral lattice, Enriques surface, hyperbolic plane
-/

namespace IntegralLattice

variable {N : Type*} [AddCommGroup N] (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)

/-- An **isotropic sequence**: `⟨v i, v j⟩ = 1 - δᵢⱼ`, stated as two clauses
so neither needs an `if`. Both clauses range over ordered pairs, which is why
no symmetry hypothesis on `b` appears here or in any consequence. -/
structure IsIsotropicSequence {n : ℕ} (v : Fin n → N) : Prop where
  /-- Every member of the sequence is isotropic. -/
  self_isotropic : ∀ i, b (v i) (v i) = 0
  /-- Every ordered pair of distinct members pairs to `1`. -/
  pairing_one : ∀ i j, i ≠ j → b (v i) (v j) = 1

namespace IsIsotropicSequence

variable {b} {n : ℕ} {v : Fin n → N} (h : IsIsotropicSequence b v)

include h

/-- The two clauses in `if` normal form, for summing over an index. -/
theorem pairing_ite (i j : Fin n) :
    b (v i) (v j) = if i = j then 0 else 1 := by
  by_cases hij : i = j
  · simp [hij, h.self_isotropic j]
  · simp [hij, h.pairing_one i j hij]

/-- **The sum vector pairs to `n - 1` against every member.** For the
Enriques configuration `n = 10` this is the `⟨s, F_j⟩ = 9` identity behind
`Δ·F_j = 3`; see the module docstring for why the division by `3` is not
taken here. -/
theorem pairing_sum_left (j : Fin n) :
    b (∑ i, v i) (v j) = (n : ℤ) - 1 := by
  have hterm : ∀ i : Fin n, b (v i) (v j) = if i = j then 0 else 1 :=
    fun i => h.pairing_ite i j
  calc b (∑ i, v i) (v j)
      = ∑ i, b (v i) (v j) := by rw [map_sum, LinearMap.sum_apply]
    _ = ∑ i, if i = j then 0 else (1 : ℤ) := Finset.sum_congr rfl fun i _ => hterm i
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

/-- **An isotropic sequence of length at least two is linearly independent
over `ℤ`.**

The Gram-matrix argument in elementary form: pairing a vanishing combination
`∑ gᵢ vᵢ = 0` against `v j` gives `(∑ gᵢ) - g j = 0`, so every coefficient
equals the common sum `S`; summing again gives `S = nS`, and `n ≥ 2` forces
`S = 0` in `ℤ`. The hypothesis `2 ≤ n` is necessary: for `n = 1` the single
vector may be `0`, as the degenerate inhabitant below shows. -/
theorem linearIndependent (hn : 2 ≤ n) : LinearIndependent ℤ v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ j, (∑ i, g i) - g j = 0 := by
    intro j
    have h0 : b (∑ i, g i • v i) (v j) = 0 := by rw [hg]; simp
    rw [map_sum, LinearMap.sum_apply] at h0
    have h1 : (∑ i, g i * b (v i) (v j)) = 0 := by
      calc (∑ i, g i * b (v i) (v j))
          = ∑ i, b (g i • v i) (v j) := Finset.sum_congr rfl fun i _ => by
            rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
        _ = 0 := h0
    have h2 : (∑ i, g i * b (v i) (v j)) = (∑ i, g i) - g j := by
      calc (∑ i, g i * b (v i) (v j))
          = ∑ i, if i = j then 0 else g i := Finset.sum_congr rfl fun i _ => by
            rw [h.pairing_ite i j]
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
    rw [← h2, h1]
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
    (fun x x' y => by simp [Pi.add_apply]; ring)
    (fun c x y => by simp [Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y y' => by simp [Pi.add_apply]; ring)
    (fun c x y => by simp [Pi.smul_apply, smul_eq_mul]; ring)

/-- The standard basis of the hyperbolic plane is an isotropic 2-sequence:
`⟨e, e⟩ = ⟨f, f⟩ = 0` and `⟨e, f⟩ = ⟨f, e⟩ = 1`. -/
theorem isIsotropicSequence_hyperbolic :
    IsIsotropicSequence hyperbolicPairing ![![1, 0], ![0, 1]] := by
  constructor
  · intro i
    fin_cases i <;> simp [hyperbolicPairing]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hyperbolicPairing]

/-- Any lattice carries the degenerate singleton sequence `![0]`: the
self-pairing clause is `b 0 0 = 0` and the pairwise clause is vacuous. This
is the boundary case excluded by `linearIndependent`'s `2 ≤ n`. -/
theorem isIsotropicSequence_zero_singleton :
    IsIsotropicSequence b ![(0 : N)] := by
  constructor
  · intro i
    fin_cases i
    simp
  · intro i j hij
    exact absurd (Subsingleton.elim i j) hij

end IntegralLattice
