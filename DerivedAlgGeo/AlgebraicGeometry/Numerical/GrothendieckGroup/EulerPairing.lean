/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Dual
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.K3

/-!
# The Euler pairing

`χ(E,F) = ∫_X ch(E)^∨ · ch(F) · td(X)`, the bilinear form Bridgeland stability conditions
are defined against: the central charge factors through `N(X)` modulo the radical of this
pairing.

## Main definitions

* `NumericalVarietyData.chi₂` — the Euler pairing `∫_X ch(E)^∨ · ch(F) · td(X)`.
* `K3.mukaiPairing` — the Mukai pairing `⟨v(E), v(F)⟩`, whose diagonal is
  `K3.mukaiSelfPairing`.

## Main results

* `chi₂_eq_sum` — the expansion in any dimension, one term per `(i, j)` with `i + j ≤ n`.
* `Surface.chi₂_eq` — the `n = 2` specialisation.
* `Surface.chi₂_sub_chi₂_swap` — the **failure** of symmetry, measured exactly.
* `K3.chi₂_eq_neg_mukaiPairing` — `χ(E,F) = −⟨v(E), v(F)⟩` on a K3.

## Implementation notes

### What `chi₂` is and is not

`chi₂` is a **definition**, not a theorem. At this layer there is no `Ext`, so there is
nothing to prove `chi₂ E F = Σᵢ (-1)ⁱ dim Extⁱ(E,F)` against; that identity is the bilinear
Hirzebruch–Riemann–Roch and it is Layer B's job, exactly as `hirzebruch_riemannRoch` is for
the one-variable `chi`. What *is* proved here is that `chi₂` is consistent with the `chi`
already in `NumericalVarietyData`: `chi₂_eq_chi_of_isStructureSheafLike` says that pairing
against a rank-one class with vanishing higher Chern components returns `chi`.

### The Euler pairing is not symmetric in even dimension

`chi₂ E F = chi₂ F E` does not hold in even dimension, and it is not a convention problem.
`chi₂_sub_chi₂_swap` computes the obstruction on a surface:

`χ(E,F) − χ(F,E) = 2·(r_E·∫c₁(F)·td₁ − r_F·∫c₁(E)·td₁)`,

which is nonzero as soon as `td₁ ≠ 0` — on `ℙ²`, for instance, where `td₁ = (3/2)H`. What is
true formally is `chi₂_symm_of_toddComp_one_eq_zero`: symmetry holds once `td₁ = 0`, hence on
every K3 and every Calabi–Yau. What Serre duality gives in general is
`χ(E,F) = (-1)ⁿ χ(F, E ⊗ ω_X)` — a Layer B theorem about `Ext`, not an identity between
these integrals — so it is not asserted here. The `ω_X` is not decoration: dropping it would
read, at `n = 2`, as exactly the symmetry disproved above, and it disappears only when
`ω_X ≅ O_X`, which is the same Calabi–Yau hypothesis as `td₁ = 0`.

### Continued in the lattice module

This file proves that `chi₂` is additive in each argument (`chi₂_add_left`,
`chi₂_add_right`). `DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Lattice` packages
that biadditivity,
constructs the radical quotient and descends the pairing.  Keeping the construction there
separates the `ℚ`-valued Euler form from the explicit finite-generation and torsion-freeness
hypotheses needed for its underlying `ℤ`-lattice.

## References

This file builds on `NumericalVarietyData`, the dual involution `NumericalRingDualHypotheses`, and
the K3 self-pairing `K3.mukaiSelfPairing` with its formula `K3.mukaiSelfPairing_eq`.

## Tags

Euler pairing, Euler characteristic, Mukai pairing, Riemann–Roch, Todd class, K3 surface
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace NumericalVarietyData

open NumericalRingData NumericalRingDualHypotheses Finset

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData n A N)

/-- The **Euler pairing** `χ(E,F) = ∫_X ch(E)^∨ · ch(F) · td(X)`.

Note what this does *not* require: no `NumericalRingDualHypotheses` value. `chDual` is the
explicit alternating sum `Σᵢ (-1)ⁱ chᵢ(E)`, which the grading alone supplies. The involution
is what *justifies* calling it a dual — `chi₂_eq_degree_dual_ch` below — but the pairing and
every consequence of it are available on any `NumericalVarietyData`. -/
noncomputable def chi₂ (E F : N) : ℚ :=
  V.ring.degree (V.chDual E * V.ch F * V.todd)

/-- A mixed term `q·chᵢ(E)·chⱼ(F)·td_k(X)` integrates to zero unless `i + j + k = n`. This is
the only computational input to the expansion, exactly as
`degree_chComp_mul_toddComp_eq_zero` is for the one-variable case. -/
theorem degree_smul_chComp_mul_chComp_mul_toddComp_eq_zero (q : ℚ) (E F : N) {i j k : ℕ}
    (h : i + j + k ≠ n) :
    V.ring.degree (q • V.chComp E i * V.chComp F j * V.toddComp k) = 0 :=
  V.ring.degree_eq_zero_of_mem h
    (V.ring.mul_mem_piece
      (V.ring.mul_mem_piece (Submodule.smul_mem _ q (V.chComp_mem E i)) (V.chComp_mem F j))
      (V.toddComp_mem k))

/-- A mixed term `chᵢ(E)·chⱼ(F)·td_k(X)` integrates to zero unless `i + j + k = n`. -/
theorem degree_chComp_mul_chComp_mul_toddComp_eq_zero (E F : N) {i j k : ℕ}
    (h : i + j + k ≠ n) :
    V.ring.degree (V.chComp E i * V.chComp F j * V.toddComp k) = 0 :=
  V.ring.degree_eq_zero_of_mem h
    (V.ring.mul_mem_piece (V.ring.mul_mem_piece (V.chComp_mem E i) (V.chComp_mem F j))
      (V.toddComp_mem k))

/-- **The bilinear Riemann–Roch expansion.** Integrating `ch(E)^∨ · ch(F) · td(X)` leaves one
term per pair `(i, j)` with `i + j ≤ n`, the Todd index being forced to `n - i - j`:

`χ(E,F) = Σᵢ Σ_{j ≤ n-i} (-1)ⁱ ∫_X chᵢ(E)·chⱼ(F)·td_{n-i-j}(X)`.

The inner range is `n + 1 - i` rather than `n + 1` with a side condition. Both say the same
thing, but the truncated range leaves no `if` in the term, and every dimension-specific
specialisation below is then a matter of `Finset.sum_range_succ` and nothing else. -/
theorem chi₂_eq_sum (E F : N) :
    V.chi₂ E F
      = ∑ i ∈ range (n + 1), ∑ j ∈ range (n + 1 - i),
          (-1 : ℚ) ^ i * V.ring.degree
            (V.chComp E i * V.chComp F j * V.toddComp (n - i - j)) := by
  rw [chi₂]
  simp only [chDual, ch, todd]
  rw [Finset.sum_mul_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n + 1 := Finset.mem_range.mp hi
  rw [Finset.sum_mul, map_sum]
  -- Widen the truncated inner range: the terms it omits are the ones that integrate to zero.
  have hwiden :
      ∑ j ∈ range (n + 1 - i), (-1 : ℚ) ^ i * V.ring.degree
            (V.chComp E i * V.chComp F j * V.toddComp (n - i - j))
        = ∑ j ∈ range (n + 1), (-1 : ℚ) ^ i * V.ring.degree
            (V.chComp E i * V.chComp F j * V.toddComp (n - i - j)) := by
    have hsub : range (n + 1 - i) ⊆ range (n + 1) := fun x hx =>
      Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) (Nat.sub_le _ _))
    refine Finset.sum_subset hsub fun j _ hj => ?_
    have hj' : n + 1 - i ≤ j := by simpa using hj
    rw [V.degree_chComp_mul_chComp_mul_toddComp_eq_zero E F (by omega), mul_zero]
  rw [hwiden]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, map_sum]
  rw [Finset.sum_eq_single (n - i - j)]
  · rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul]
  · intro k _ hk
    exact V.degree_smul_chComp_mul_chComp_mul_toddComp_eq_zero _ E F (by omega)
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega)) hmem

/-- Pulling a scalar out of the left of a triple product. -/
theorem degree_algebraMap_mul_mul (q : ℚ) (x y : A) :
    V.ring.degree (algebraMap ℚ A q * x * y) = q * V.ring.degree (x * y) := by
  rw [mul_assoc, V.ring.degree_algebraMap_mul]

/-- Pulling a scalar out of the middle of a triple product. -/
theorem degree_mul_algebraMap_mul (q : ℚ) (x y : A) :
    V.ring.degree (x * algebraMap ℚ A q * y) = q * V.ring.degree (x * y) := by
  rw [mul_comm x (algebraMap ℚ A q), mul_assoc, V.ring.degree_algebraMap_mul]

/-- Pulling a scalar out of the right of a product. -/
theorem degree_mul_algebraMap (q : ℚ) (x : A) :
    V.ring.degree (x * algebraMap ℚ A q) = q * V.ring.degree x := by
  rw [mul_comm x (algebraMap ℚ A q), V.ring.degree_algebraMap_mul]

/-- `chi₂` is additive in its second argument. -/
theorem chi₂_add_right (E F G : N) :
    V.chi₂ E (F + G) = V.chi₂ E F + V.chi₂ E G := by
  simp only [chi₂, ch_add, mul_add, add_mul, map_add]

/-- `chi₂` is additive in its first argument. -/
theorem chi₂_add_left (E F G : N) :
    V.chi₂ (E + F) G = V.chi₂ E G + V.chi₂ F G := by
  simp only [chi₂, chDual_add, add_mul, map_add]

/-- `chi₂` written with the involution rather than with `chDual`, which is how
Hirzebruch–Riemann–Roch states it. This is the only place the involution is needed, and it
is what earns `chDual` its name. -/
theorem chi₂_eq_degree_dual_ch (D : NumericalRingDualHypotheses V.ring) (E F : N) :
    V.chi₂ E F = V.ring.degree (D.dual (V.ch E) * V.ch F * V.todd) := by
  rw [chi₂, V.dual_ch D]

end NumericalVarietyData

namespace Surface

open NumericalRingData NumericalRingDualHypotheses NumericalVarietyData Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 2 A N)

/-- **The Euler pairing on a surface.**

`χ(E,F) = r_E·r_F·∫td₂ + r_E·∫c₁(F)·td₁ − r_F·∫c₁(E)·td₁ + r_E·∫ch₂(F) + r_F·∫ch₂(E)
− ∫c₁(E)·c₁(F)`.

The two `td₁` terms carry opposite signs; that asymmetry is the whole content of the dual
involution, and it is what `chi₂_sub_chi₂_swap` measures. -/
theorem chi₂_eq (E F : N) :
    V.chi₂ E F
      = (V.rank E : ℚ) * (V.rank F : ℚ) * V.ring.degree (V.toddComp 2)
        + (V.rank E : ℚ) * V.ring.degree (V.chComp F 1 * V.toddComp 1)
        - (V.rank F : ℚ) * V.ring.degree (V.chComp E 1 * V.toddComp 1)
        + (V.rank E : ℚ) * V.ring.degree (V.chComp F 2)
        + (V.rank F : ℚ) * V.ring.degree (V.chComp E 2)
        - V.ring.degree (V.chComp E 1 * V.chComp F 1) := by
  rw [V.chi₂_eq_sum]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  -- Reduce the Todd indices by hand: `simp` leaves `2 - i - j` unevaluated at this point, and
  -- `toddComp_zero` then has nothing to match against. Same idiom as `Surface.chi_eq`.
  simp only [show (2 : ℕ) - 0 - 0 = 2 from rfl, show (2 : ℕ) - 0 - 1 = 1 from rfl,
    show (2 : ℕ) - 0 - 2 = 0 from rfl]
  simp only [pow_zero, pow_one, neg_one_sq, one_mul, V.chComp_zero, V.toddComp_zero, mul_one]
  simp only [V.degree_algebraMap_mul_mul, V.degree_mul_algebraMap_mul,
    V.ring.degree_algebraMap_mul, V.degree_mul_algebraMap]
  ring

/-- Pairing against a rank-one class with vanishing higher Chern components returns the
one-variable `chi`. This is the consistency check between `chi₂` and the `chi` that
`NumericalVarietyData` already carries: `chi₂` is a new definition, and this is the statement
that it is the *right* one. -/
theorem chi₂_eq_chi_of_isStructureSheafLike (hV : V.SatisfiesHRR) (E F : N)
    (hr : V.rank E = 1) (h₁ : V.chComp E 1 = 0) (h₂ : V.chComp E 2 = 0) :
    V.chi₂ E F = (V.chi F : ℚ) := by
  have hchi := V.chi_eq_sum hV F
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at hchi
  simp only [show (2 : ℕ) - 0 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
    show (2 : ℕ) - 2 = 0 from rfl] at hchi
  rw [chi₂_eq V, hchi, V.chComp_zero, V.ring.degree_algebraMap_mul, V.toddComp_zero,
    mul_one, hr, h₁, h₂]
  simp only [Int.cast_one, one_mul, zero_mul, map_zero, mul_zero]
  ring

/-- **The Euler pairing is not symmetric**, and this is by how much:

`χ(E,F) − χ(F,E) = 2·(r_E·∫c₁(F)·td₁ − r_F·∫c₁(E)·td₁)`.

Symmetry fails in even dimension: on `ℙ²`, `td₁ = (3/2)H ≠ 0`, so the right-hand side is
nonzero for suitable `E`, `F`. Symmetry needs `td₁ = 0`. -/
theorem chi₂_sub_chi₂_swap (E F : N) :
    V.chi₂ E F - V.chi₂ F E
      = 2 * ((V.rank E : ℚ) * V.ring.degree (V.chComp F 1 * V.toddComp 1)
          - (V.rank F : ℚ) * V.ring.degree (V.chComp E 1 * V.toddComp 1)) := by
  rw [chi₂_eq V, chi₂_eq V, mul_comm (V.chComp F 1) (V.chComp E 1)]
  ring

/-- The Euler pairing is symmetric once `td₁(X) = 0` — in particular on every K3 and every
Calabi–Yau surface. Without that hypothesis symmetry fails, already on `ℙ²`; see
`chi₂_sub_chi₂_swap`. -/
theorem chi₂_symm_of_toddComp_one_eq_zero (htd : V.toddComp 1 = 0) (E F : N) :
    V.chi₂ E F = V.chi₂ F E := by
  rw [chi₂_eq V, chi₂_eq V, htd, mul_comm (V.chComp F 1) (V.chComp E 1)]
  simp only [mul_zero, map_zero, mul_zero]
  ring

end Surface

namespace K3

open NumericalRingData NumericalRingDualHypotheses NumericalVarietyData Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 2 A N)

/-- The **Mukai pairing** `⟨v(E), v(F)⟩ = ∫c₁(E)·c₁(F) − r_E·s_F − r_F·s_E`, the bilinear
form whose diagonal is `mukaiSelfPairing`. -/
noncomputable def mukaiPairing (E F : N) : ℚ :=
  V.ring.degree (V.chComp E 1 * V.chComp F 1)
    - (V.rank E : ℚ) * mukaiS V F - (V.rank F : ℚ) * mukaiS V E

/-- The Mukai pairing restricts to `mukaiSelfPairing` on the diagonal, so nothing in
`Numerical/RiemannRoch/K3.lean` is being redefined. -/
theorem mukaiPairing_self (E : N) :
    mukaiPairing V E E = mukaiSelfPairing V E := by
  rw [mukaiPairing, mukaiSelfPairing]
  ring

/-- The Mukai pairing is symmetric. -/
theorem mukaiPairing_comm (E F : N) :
    mukaiPairing V E F = mukaiPairing V F E := by
  rw [mukaiPairing, mukaiPairing, mul_comm (V.chComp E 1) (V.chComp F 1)]
  ring

/-- **The Euler pairing is minus the Mukai pairing on a K3**: `χ(E,F) = −⟨v(E), v(F)⟩`.

This is the identity that fixes the sign convention of the dual involution: with
`chᵢ(E^∨) = (-1)ⁱchᵢ(E)` the sign comes out, and with the opposite convention it does not.
The self-pairing case recovers `K3.mukaiSelfPairing_eq`. -/
theorem chi₂_eq_neg_mukaiPairing (hK3 : IsK3 V) (E F : N) :
    V.chi₂ E F = -mukaiPairing V E F := by
  rw [Surface.chi₂_eq V, mukaiPairing, mukaiS, mukaiS, hK3.toddComp_one,
    hK3.degree_toddComp_two]
  simp only [mul_zero, map_zero, mul_zero]
  ring

/-- Consequently the Euler pairing is symmetric on a K3. -/
theorem chi₂_comm (hK3 : IsK3 V) (E F : N) : V.chi₂ E F = V.chi₂ F E := by
  rw [chi₂_eq_neg_mukaiPairing V hK3, chi₂_eq_neg_mukaiPairing V hK3,
    mukaiPairing_comm V]

/-- `χ(E,E) = −⟨v(E), v(E)⟩ = 2r² − ∫Δ(E)`, tying the Euler pairing to the
Bogomolov–Gieseker discriminant through `K3.mukaiSelfPairing_eq`. -/
theorem chi₂_self (hK3 : IsK3 V) (E : N) :
    V.chi₂ E E = 2 * (V.rank E : ℚ) ^ 2 - V.ring.degree (V.discriminant E) := by
  rw [chi₂_eq_neg_mukaiPairing V hK3, mukaiPairing_self V, mukaiSelfPairing_eq V]
  ring

end K3

end AlgebraicGeometry.Numerical
