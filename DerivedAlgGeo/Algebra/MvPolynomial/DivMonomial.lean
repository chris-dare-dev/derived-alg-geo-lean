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
and multivariate polynomials. They include exact division by a power of one
variable and cross-variable cancellation; projective localization and Čech
constructions import these facts as consumers.
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

/-! ## Exact division by a power of one variable -/

/-- Dividing a homogeneous polynomial of degree `n + d` by `Xᵢⁿ`, when the division is exact,
produces a homogeneous polynomial of degree `d`. -/
theorem divMonomial_single_mem_homogeneousSubmodule
    (ι k : Type u) [Field k] (i : ι) (n d : ℕ) (p : MvPolynomial ι k)
    (hp : p ∈ homogeneousSubmodule ι k (n + d)) :
    p.divMonomial (Finsupp.single i n) ∈ homogeneousSubmodule ι k d := by
  intro s hs
  have hcoeff : coeff (Finsupp.single i n + s) p ≠ 0 := by
    simpa only [coeff_divMonomial] using hs
  have hdeg := hp hcoeff
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, nsmul_eq_mul, mul_one] at hdeg
  exact Nat.add_left_cancel hdeg

/-- Exact division by `Xᵢⁿ` reconstructs the original polynomial. -/
theorem X_pow_mul_divMonomial_single
    (ι k : Type u) [Field k] (i : ι) (n : ℕ) (p : MvPolynomial ι k)
    (hdiv : (X i : MvPolynomial ι k) ^ n ∣ p) :
    X i ^ n * p.divMonomial (Finsupp.single i n) = p := by
  rw [X_pow_eq_monomial]
  have hmod : p.modMonomial (Finsupp.single i n) = 0 :=
    monomial_one_dvd_iff_modMonomial_eq_zero.mp
      (by simpa only [X_pow_eq_monomial] using hdiv)
  simpa only [hmod, add_zero] using
    divMonomial_add_modMonomial p (Finsupp.single i n)

/-- If a fraction with denominator a power of `Xᵢ` also admits a denominator involving only a
different variable, then its numerator is divisible by the entire power of `Xᵢ`. -/
theorem X_pow_dvd_of_cross_mul
    (ι k : Type u) [Field k] {i j : ι} (hij : i ≠ j) (n m : ℕ)
    (p q : MvPolynomial ι k) (hcross : X j ^ m * p = X i ^ n * q) :
    (X i : MvPolynomial ι k) ^ n ∣ p := by
  have hnot : ¬(X i : MvPolynomial ι k) ∣ X j ^ m := by
    intro h
    have hX : (X i : MvPolynomial ι k) ∣ X j :=
      (X_prime (R := k) (i := i)).dvd_of_dvd_pow h
    exact hij (X_dvd_X.mp hX)
  apply (X_prime (R := k) (i := i)).pow_dvd_of_dvd_mul_left n hnot
  exact ⟨q, hcross⟩

end MvPolynomial
