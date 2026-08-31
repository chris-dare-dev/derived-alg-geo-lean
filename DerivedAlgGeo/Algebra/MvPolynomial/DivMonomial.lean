/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Division by monomials

This file extends Mathlib's `MvPolynomial.divMonomial` API with homogeneous
degree bookkeeping and identities for moving monomial factors through a
division. The statements depend only on finitely supported exponent vectors
and multivariate polynomials; projective localization and Čech constructions
consume them from algebraic geometry.
-/

universe u

namespace Finsupp

/-- `Finsupp.degree` is `Finsupp.weight 1`, pointwise. -/
theorem degree_eq_weight_one_apply {ι : Type u} (e : ι →₀ ℕ) :
    degree e = weight 1 e := by
  rw [degree_eq_weight_one]
  rfl

end Finsupp

namespace MvPolynomial

variable {ι R : Type u} [CommRing R]

/-- Dividing by a monomial drops homogeneous degree by the degree of that
monomial. -/
theorem isHomogeneous_divMonomial {p : MvPolynomial ι R} {s : ι →₀ ℕ}
    {k : ℕ} (hp : p.IsHomogeneous (s.degree + k)) :
    (divMonomial p s).IsHomogeneous k := by
  intro e he
  rw [coeff_divMonomial] at he
  have h := hp he
  rw [map_add, ← Finsupp.degree_eq_weight_one_apply,
    ← Finsupp.degree_eq_weight_one_apply] at h
  rw [← Finsupp.degree_eq_weight_one_apply]
  exact Nat.add_left_cancel h

/-- Dividing off a factor already present leaves the rest of the division to
do. -/
theorem divMonomial_monomial_mul_add (a b : ι →₀ ℕ)
    (x : MvPolynomial ι R) :
    divMonomial (monomial a 1 * x) (a + b) = divMonomial x b := by
  rw [divMonomial_add, divMonomial_monomial_mul]

/-- A monomial factor passes through a division when the factor and divisor
have disjoint support. -/
theorem divMonomial_monomial_mul_comm {a s : ι →₀ ℕ}
    (hd : ∀ j, a j = 0 ∨ s j = 0) (p : MvPolynomial ι R) :
    divMonomial (monomial a 1 * p) s =
      monomial a 1 * divMonomial p s := by
  have hiff : ∀ β : ι →₀ ℕ, a ≤ s + β ↔ a ≤ β := by
    intro β
    constructor
    · intro h j
      rcases hd j with hj | hj
      · simp [hj]
      · have := h j
        simpa [hj] using this
    · intro h j
      exact le_trans (h j) (by simp)
  ext β
  rw [coeff_divMonomial, coeff_monomial_mul', coeff_monomial_mul']
  by_cases h : a ≤ β
  · rw [if_pos ((hiff β).mpr h), if_pos h, coeff_divMonomial]
    congr 2
    ext j
    have := h j
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.coe_add, Pi.add_apply]
    omega
  · rw [if_neg (fun hc => h ((hiff β).mp hc)), if_neg h]

set_option maxHeartbeats 800000 in
/-- Raising a numerator by a power of one monomial and then dividing off one
of its factors agrees with first dividing and then multiplying by the
disjoint remaining factor. -/
theorem divMonomial_pow_mul {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0)
    (m t : ℕ) (p : MvPolynomial ι R) :
    divMonomial ((monomial γ (1 : R)) ^ t * p)
        (Finsupp.single i₀ ((m + t) * c)) =
      (monomial γ' (1 : R)) ^ t *
        divMonomial p (Finsupp.single i₀ (m * c)) := by
  have hpow : (monomial γ (1 : R)) ^ t =
      monomial (Finsupp.single i₀ (t * c)) 1 *
        monomial (t • γ') 1 := by
    rw [monomial_pow, one_pow, monomial_mul, one_mul, hγ, smul_add,
      Finsupp.smul_single, smul_eq_mul]
  have hsplit : Finsupp.single i₀ ((m + t) * c) =
      Finsupp.single i₀ (t * c) + Finsupp.single i₀ (m * c) := by
    rw [← Finsupp.single_add]
    congr 1
    ring
  have hdisj : ∀ j : ι,
      (t • γ') j = 0 ∨ (Finsupp.single i₀ (m * c)) j = 0 := by
    intro j
    by_cases hj : j = i₀
    · exact Or.inl (by simp [hj, hγ'])
    · exact Or.inr (by simp [Ne.symm hj])
  rw [hpow, hsplit, mul_assoc, divMonomial_monomial_mul_add,
    divMonomial_monomial_mul_comm hdisj, monomial_pow, one_pow]

end MvPolynomial
