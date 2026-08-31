/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Data.Finsupp.Weight
import Mathlib.Tactic

/-!
# Laurent exponents of finitely supported natural vectors

This file embeds finitely supported natural exponent vectors into integer
exponent vectors and records the subtraction and degree identities used by
Laurent monomials.  It depends only on `Finsupp`; multivariate polynomials and
graded localizations consume this API from their own algebraic layers.
-/

universe u

namespace Finsupp

variable {ι : Type u}

/-- An exponent vector read in `ℤ`, so that an inverted variable can carry a
negative exponent. -/
noncomputable def natToIntExponent : (ι →₀ ℕ) →+ (ι →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

theorem natToIntExponent_injective :
    Function.Injective (natToIntExponent (ι := ι)) := fun _ _ h =>
  Finsupp.mapRange_injective (Nat.cast) Nat.cast_zero Nat.cast_injective h

/-- Reading an exponent vector in `ℤ` does not change its total degree. -/
theorem degree_natToIntExponent (β : ι →₀ ℕ) :
    (natToIntExponent β).degree = (β.degree : ℤ) := by
  classical
  induction β using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [map_add, hf, hg]
  | single a b => simp [natToIntExponent, Finsupp.degree_single]

/-- The Laurent exponent of the formal fraction `Xᵝ / (Xᵞ)ᵐ`. -/
noncomputable def laurentExponent (γ : ι →₀ ℕ) (m : ℕ) (β : ι →₀ ℕ) : ι →₀ ℤ :=
  natToIntExponent β - m • natToIntExponent γ

@[simp]
theorem laurentExponent_apply (γ : ι →₀ ℕ) (m : ℕ) (β : ι →₀ ℕ) (j : ι) :
    laurentExponent γ m β j = (β j : ℤ) - m * (γ j : ℤ) := by
  simp [laurentExponent, natToIntExponent]

/-- Laurent exponents agree exactly when the natural exponent vectors agree
after clearing the formal denominators. -/
theorem laurentExponent_eq_iff (γ : ι →₀ ℕ) (m m' : ℕ) (β β' : ι →₀ ℕ) :
    laurentExponent γ m β = laurentExponent γ m' β' ↔ m' • γ + β = m • γ + β' := by
  rw [laurentExponent, laurentExponent, sub_eq_sub_iff_add_eq_add,
    ← map_nsmul, ← map_nsmul, ← map_add, ← map_add,
    Function.Injective.eq_iff natToIntExponent_injective]
  constructor
  · intro h; rw [add_comm (m' • γ), add_comm (m • γ)]; exact h
  · intro h; rw [add_comm β, add_comm β']; exact h

/-- The total degree of a Laurent exponent after subtracting a natural
denominator degree. -/
theorem degree_laurentExponent (γ β : ι →₀ ℕ) (m d : ℕ)
    (hβ : β.degree = m • γ.degree + d) :
    (laurentExponent γ m β).degree = d := by
  rw [laurentExponent, map_sub, map_nsmul, degree_natToIntExponent,
    degree_natToIntExponent, hβ, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- Off the support of `γ`, its Laurent exponent contribution is
nonnegative. -/
theorem laurentExponent_nonneg_of_apply_eq_zero (γ : ι →₀ ℕ) (m : ℕ) (β : ι →₀ ℕ) {j : ι}
    (hj : γ j = 0) : 0 ≤ laurentExponent γ m β j := by
  simp [hj]

/-- The total-degree identity for an integer-valued twist. -/
theorem degree_laurentExponent_int (γ β : ι →₀ ℕ) (m : ℕ) (d : ℤ)
    (hβ : (β.degree : ℤ) = m • (γ.degree : ℤ) + d) :
    (laurentExponent γ m β).degree = d := by
  rw [laurentExponent, map_sub, map_nsmul, degree_natToIntExponent,
    degree_natToIntExponent, hβ]
  ring

end Finsupp
