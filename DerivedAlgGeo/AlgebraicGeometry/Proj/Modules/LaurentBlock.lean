/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.LaurentProjection
import Mathlib.Data.Int.Interval

/-!
# The block decomposition of an away localization

Step 2 of #340's proof plan decomposes the Čech complex of `O(d)` by the **negative support**
`N α = {j | α j < 0}` of the Laurent exponent: the differential preserves `N α`, each block with
a cone point contracts, and for `d ≥ 0` every block has a cone point. This file supplies the
decomposition at the level of one away localization `(A(d)_{Xᵞ})₀`, in the form the vanishing
argument consumes.

The decomposition is deliberately **not** packaged as a direct-sum isomorphism or a
`∏_F`-indexed complex. The consumer — "every positive-degree cocycle is a coboundary" — needs
exactly a family of additive projections `blockProj γ F d` with

* `sum_blockProj` — they sum to the identity over the *finite* index `γ.support.powerset`,
  which is the step that keeps an infinite variable set harmless: each single localization only
  ever meets finitely many blocks, and no infinite product is exchanged with an infinite sum;
* `blockProj_blockProj_self` / `blockProj_blockProj_of_ne` — they are orthogonal idempotents;
* `laurentFace_blockProj` — **the faces of the Čech complex commute with them**, because a face
  moves the numerator and the denominator together and the Laurent exponent never changes.

## Main definitions

* `intNegSupport` — the negative support of an integer exponent vector;
* `laurentFilter` — keep the monomials of a numerator whose Laurent exponent has a given
  negative support;
* `AwayRep.blockFilter` — the same operation on a representative;
* `blockProj` — the block projection on the localization, pinned by `blockProj_awayMk`.

## Implementation notes

`laurentFilter` is characterised coefficientwise by `coeff_laurentFilter_of_eq` and
`coeff_laurentFilter_of_ne`, and every identity about it is proved by `ext` plus a case split on
the block of the exponent. This keeps the `Finset.filter` in its definition — and the classical
decidability instance it needs — out of every statement.

`laurentFilter_monomial_mul` is the single shift identity behind both well-definedness and the
face square. Multiplying the numerator by `Xᵟ` and moving the denominator data from `(γ, m)` to
`(γ', m')` fixes every Laurent exponent as soon as `σ + m • γ = m' • γ'`; raising a
representative (`σ = t • γ`) and applying a Čech face (`σ = m • single e c`) are the two
instances, so one lemma serves where #526 needed `divMonomial_pow_mul` and #539 needed
`divMonomial_monomial_mul_comm` separately.

`blockProj` descends to the localization through `Exists.choose` exactly as `signProjection`
does, and everything must go through `blockProj_awayMk`; the definition itself has no useful
`rfl` behaviour.

## Tags

Laurent monomial, negative support, block decomposition, projective space
-/

open Finsupp GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

variable {ι R : Type u} [CommRing R]

/-! ## The negative support of a Laurent exponent -/

/-- The negative support of an integer exponent vector: the variables that occur with a negative
exponent. This is the `N α` of #340's proof plan; the block of a Laurent monomial is its
negative support, and the Čech differential preserves it. -/
noncomputable def intNegSupport (α : ι →₀ ℤ) : Finset ι :=
  α.support.filter fun j => α j < 0

theorem mem_intNegSupport {α : ι →₀ ℤ} {j : ι} : j ∈ intNegSupport α ↔ α j < 0 := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr (by omega), h⟩

/-- The negative support of a Laurent exponent lies inside the support of the denominator: a
variable the localization does not invert cannot go negative. This is
`laurentExponent_nonneg_of_apply_eq_zero` read as a `Finset` inclusion, and it is what makes
`γ.support.powerset` a complete block index for `(A(d)_{Xᵞ})₀`. -/
theorem intNegSupport_laurentExponent_subset (γ : ι →₀ ℕ) (m : ℕ) (β : ι →₀ ℕ) :
    intNegSupport (laurentExponent γ m β) ⊆ γ.support := by
  intro j hj
  rw [mem_intNegSupport] at hj
  rw [Finsupp.mem_support_iff]
  intro h0
  exact absurd hj (not_lt.mpr (laurentExponent_nonneg_of_apply_eq_zero γ m β h0))

/-- **The full block is indexed by finitely many Laurent exponents.**

An exponent in the block of *every* variable is negative in every coordinate, and its coordinates
sum to the twist. Each coordinate is therefore trapped between `-1` above and
`d + (card ι) - 1` below — the latter because the other `card ι - 1` coordinates contribute at most
`-1` each — so the exponents form a subset of a finite box.

This is the finiteness the top cohomology of `Pⁿ` rests on. Below the top degree the full block is
empty for a counting reason (`cechBlockProj_eq_zero_of_card_lt`); in the top degree it is not, and
this says it is at least small. Note the set is empty unless `d ≤ -(card ι)`, which is Serre's
`Hⁿ(Pⁿ, O(d)) = 0` for `d > -(n+1)` in exponent form — but that is a consequence, not what is
proved here. -/
theorem finite_setOf_degree_eq_of_neg [Fintype ι] (d : ℤ) :
    {α : ι →₀ ℤ | α.degree = d ∧ ∀ j : ι, α j < 0}.Finite := by
  classical
  refine Set.Finite.of_finite_image
    (f := (Finsupp.equivFunOnFinite : (ι →₀ ℤ) ≃ (ι → ℤ))) ?_
    (Finsupp.equivFunOnFinite.injective.injOn)
  refine Set.Finite.subset
    (Set.Finite.pi fun _ : ι =>
      Set.finite_Icc (d + (Fintype.card ι : ℤ) - 1) (-1)) ?_
  rintro f ⟨α, ⟨hdeg, hneg⟩, rfl⟩ j -
  simp only [Finsupp.equivFunOnFinite_apply]
  -- Over a fintype the total degree is the sum over all coordinates.
  have hsum : ∑ i : ι, α i = d := by
    rw [← hdeg, Finsupp.degree_apply]
    exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      simpa using Finsupp.notMem_support_iff.mp hi).symm
  have hle : ∀ i : ι, α i ≤ -1 := fun i => by have := hneg i; omega
  have hsplit : α j + ∑ i ∈ Finset.univ.erase j, α i = d :=
    (Finset.add_sum_erase Finset.univ α (Finset.mem_univ j)).trans hsum
  have hcard : (Finset.univ.erase j).card = Fintype.card ι - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
  have hpos : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
  have hupper : ∑ i ∈ Finset.univ.erase j, α i ≤ -((Fintype.card ι : ℤ) - 1) := by
    calc ∑ i ∈ Finset.univ.erase j, α i
        ≤ ∑ _i ∈ Finset.univ.erase j, (-1 : ℤ) := Finset.sum_le_sum fun i _ => hle i
      _ = -((Fintype.card ι : ℤ) - 1) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          have : ((Fintype.card ι - 1 : ℕ) : ℤ) = (Fintype.card ι : ℤ) - 1 := by
            omega
          rw [this]
          ring
  exact ⟨by omega, hle j⟩

/-- **The shift identity for Laurent exponents.** Multiplying a numerator exponent by `Xᵟ` while
the denominator data moves from `(γ, m)` to `(γ', m')` fixes the Laurent exponent as soon as
`σ + m • γ = m' • γ'`. Raising a representative and applying a Čech face are both instances. -/
theorem laurentExponent_sub_of_add_eq {γ γ' σ β : ι →₀ ℕ} {m m' : ℕ}
    (hσ : σ + m • γ = m' • γ') (hle : σ ≤ β) :
    laurentExponent γ m (β - σ) = laurentExponent γ' m' β := by
  ext j
  have hj : σ j + m * γ j = m' * γ' j := by
    have h := congrArg (fun v : ι →₀ ℕ => v j) hσ
    simpa using h
  have hlej : σ j ≤ β j := Finsupp.le_def.mp hle j
  rw [laurentExponent_apply, laurentExponent_apply, Finsupp.tsub_apply]
  have hz : ((β j - σ j : ℕ) : ℤ) = (β j : ℤ) - σ j := Nat.cast_sub hlej
  have hjz : (σ j : ℤ) + (m : ℤ) * γ j = (m' : ℤ) * γ' j := by exact_mod_cast hj
  rw [hz]
  linarith

/-! ## Filtering a numerator by block -/

open Classical in
/-- Keep the monomials of a numerator whose Laurent exponent over `(Xᵞ)ᵐ` has negative support
exactly `F`. Characterised coefficientwise by `coeff_laurentFilter_of_eq` and
`coeff_laurentFilter_of_ne`; the classical decidability this definition needs never reaches a
statement. -/
noncomputable def laurentFilter (γ : ι →₀ ℕ) (m : ℕ) (F : Finset ι) (p : MvPolynomial ι R) :
    MvPolynomial ι R :=
  ∑ β ∈ p.support.filter fun β => intNegSupport (laurentExponent γ m β) = F,
    MvPolynomial.monomial β (p.coeff β)

theorem coeff_laurentFilter_of_eq {γ : ι →₀ ℕ} {m : ℕ} {F : Finset ι} {β : ι →₀ ℕ}
    (h : intNegSupport (laurentExponent γ m β) = F) (p : MvPolynomial ι R) :
    (laurentFilter γ m F p).coeff β = p.coeff β := by
  classical
  rw [laurentFilter, MvPolynomial.coeff_sum,
    Finset.sum_congr rfl fun b _ => MvPolynomial.coeff_monomial β b (p.coeff b),
    Finset.sum_ite_eq' _ β fun b => p.coeff b]
  by_cases hs : β ∈ p.support
  · rw [if_pos (Finset.mem_filter.mpr ⟨hs, h⟩)]
  · rw [MvPolynomial.notMem_support_iff.mp hs, ite_self]

theorem coeff_laurentFilter_of_ne {γ : ι →₀ ℕ} {m : ℕ} {F : Finset ι} {β : ι →₀ ℕ}
    (h : intNegSupport (laurentExponent γ m β) ≠ F) (p : MvPolynomial ι R) :
    (laurentFilter γ m F p).coeff β = 0 := by
  classical
  rw [laurentFilter, MvPolynomial.coeff_sum,
    Finset.sum_congr rfl fun b _ => MvPolynomial.coeff_monomial β b (p.coeff b),
    Finset.sum_ite_eq' _ β fun b => p.coeff b]
  split_ifs with hmem
  · exact absurd (Finset.mem_filter.mp hmem).2 h
  · rfl

/-- Filtering is additive in the numerator, which is what the block projection's additivity
descends from. -/
theorem laurentFilter_add (γ : ι →₀ ℕ) (m : ℕ) (F : Finset ι) (p q : MvPolynomial ι R) :
    laurentFilter γ m F (p + q) = laurentFilter γ m F p + laurentFilter γ m F q := by
  ext β
  rw [MvPolynomial.coeff_add]
  by_cases h : intNegSupport (laurentExponent γ m β) = F
  · rw [coeff_laurentFilter_of_eq h, coeff_laurentFilter_of_eq h, coeff_laurentFilter_of_eq h,
      MvPolynomial.coeff_add]
  · rw [coeff_laurentFilter_of_ne h, coeff_laurentFilter_of_ne h, coeff_laurentFilter_of_ne h,
      add_zero]

/-- Filtering preserves the graded piece: it only discards monomials. -/
theorem IsPolynomialTwist.laurentFilter_mem {σM : Type u} [SetLike σM (MvPolynomial ι R)]
    {𝓜 : ℕ → σM} {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d) {γ : ι →₀ ℕ} {F : Finset ι} {m : ℕ}
    {p : MvPolynomial ι R} (hp : p ∈ 𝓜 (m • γ.degree)) :
    laurentFilter γ m F p ∈ 𝓜 (m • γ.degree) := by
  rcases (h𝓜 _ p).mp hp with rfl | ⟨e, he, hhom⟩
  · refine (h𝓜 _ _).mpr (Or.inl ?_)
    ext β
    by_cases h : intNegSupport (laurentExponent γ m β) = F
    · rw [coeff_laurentFilter_of_eq h]
    · rw [coeff_laurentFilter_of_ne h, MvPolynomial.coeff_zero]
  refine (h𝓜 _ _).mpr (Or.inr ⟨e, he, ?_⟩)
  intro β hβ
  by_cases h : intNegSupport (laurentExponent γ m β) = F
  · rw [coeff_laurentFilter_of_eq h] at hβ
    exact hhom hβ
  · rw [coeff_laurentFilter_of_ne h] at hβ
    exact absurd rfl hβ

theorem laurentFilter_mem_natShift {γ : ι →₀ ℕ} {F : Finset ι} {d m : ℕ}
    {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree)) :
    laurentFilter γ m F p ∈ natShift (polynomialGrading ι R) d (m • γ.degree) := by
  intro β hβ
  by_cases h : intNegSupport (laurentExponent γ m β) = F
  · rw [coeff_laurentFilter_of_eq h] at hβ
    exact hp hβ
  · rw [coeff_laurentFilter_of_ne h] at hβ
    exact absurd rfl hβ

/-- **The blocks exhaust the numerator.** Summing the filters over all subsets of the
denominator's support recovers the numerator: every monomial lands in the single block named by
its negative support, and that block is admissible by `intNegSupport_laurentExponent_subset`.
The index `γ.support.powerset` is finite for every `γ`, whatever the variable set. -/
theorem sum_laurentFilter_powerset (γ : ι →₀ ℕ) (m : ℕ) (p : MvPolynomial ι R) :
    ∑ F ∈ γ.support.powerset, laurentFilter γ m F p = p := by
  classical
  ext β
  rw [MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single_of_mem (intNegSupport (laurentExponent γ m β))
    (Finset.mem_powerset.mpr (intNegSupport_laurentExponent_subset γ m β))
    fun F _ hF => coeff_laurentFilter_of_ne (fun h => hF h.symm) p]
  rw [coeff_laurentFilter_of_eq rfl]

/-- Filtering twice by the same block changes nothing. -/
theorem laurentFilter_laurentFilter_self (γ : ι →₀ ℕ) (m : ℕ) (F : Finset ι)
    (p : MvPolynomial ι R) :
    laurentFilter γ m F (laurentFilter γ m F p) = laurentFilter γ m F p := by
  ext β
  by_cases h : intNegSupport (laurentExponent γ m β) = F
  · rw [coeff_laurentFilter_of_eq h, coeff_laurentFilter_of_eq h]
  · rw [coeff_laurentFilter_of_ne h, coeff_laurentFilter_of_ne h]

/-- Distinct blocks are disjoint: filtering by one then the other kills everything. -/
theorem laurentFilter_laurentFilter_of_ne {F F' : Finset ι} (h : F ≠ F') (γ : ι →₀ ℕ) (m : ℕ)
    (p : MvPolynomial ι R) :
    laurentFilter γ m F (laurentFilter γ m F' p) = 0 := by
  ext β
  rw [MvPolynomial.coeff_zero]
  by_cases hN : intNegSupport (laurentExponent γ m β) = F
  · rw [coeff_laurentFilter_of_eq hN, coeff_laurentFilter_of_ne fun h' => h (hN ▸ h')]
  · rw [coeff_laurentFilter_of_ne hN]

/-- A block outside the denominator's support is empty. -/
theorem laurentFilter_eq_zero_of_not_subset {γ : ι →₀ ℕ} {F : Finset ι}
    (h : ¬ F ⊆ γ.support) (m : ℕ) (p : MvPolynomial ι R) :
    laurentFilter γ m F p = 0 := by
  ext β
  rw [MvPolynomial.coeff_zero]
  exact coeff_laurentFilter_of_ne
    (fun hN => h (by rw [← hN]; exact intNegSupport_laurentExponent_subset γ m β)) p

/-- **The shift identity for filters.** Multiplying the numerator by `Xᵟ` while the denominator
data moves from `(γ, m)` to `(γ', m')` commutes with filtering, as soon as
`σ + m • γ = m' • γ'` — the hypothesis under which `laurentExponent_sub_of_add_eq` says no
Laurent exponent moves. Raising a representative (`σ = t • γ`) and applying a Čech face
(`σ = m • single e c`) are the two instances; this one identity is the whole content of both
the well-definedness of `blockProj` and its commutation with the faces. -/
theorem laurentFilter_monomial_mul {γ γ' σ : ι →₀ ℕ} {m m' : ℕ}
    (hσ : σ + m • γ = m' • γ') (F : Finset ι) (p : MvPolynomial ι R) :
    laurentFilter γ' m' F (MvPolynomial.monomial σ 1 * p) =
      MvPolynomial.monomial σ 1 * laurentFilter γ m F p := by
  ext β
  by_cases hle : σ ≤ β
  · have hα : laurentExponent γ m (β - σ) = laurentExponent γ' m' β :=
      laurentExponent_sub_of_add_eq hσ hle
    by_cases hN : intNegSupport (laurentExponent γ' m' β) = F
    · rw [coeff_laurentFilter_of_eq hN, MvPolynomial.coeff_monomial_mul',
        MvPolynomial.coeff_monomial_mul', if_pos hle, if_pos hle, one_mul, one_mul,
        coeff_laurentFilter_of_eq (by rw [hα]; exact hN)]
    · rw [coeff_laurentFilter_of_ne hN, MvPolynomial.coeff_monomial_mul', if_pos hle, one_mul,
        coeff_laurentFilter_of_ne (by rw [hα]; exact hN)]
  · rw [MvPolynomial.coeff_monomial_mul', if_neg hle]
    by_cases hN : intNegSupport (laurentExponent γ' m' β) = F
    · rw [coeff_laurentFilter_of_eq hN, MvPolynomial.coeff_monomial_mul', if_neg hle]
    · rw [coeff_laurentFilter_of_ne hN]

/-! ## The block projection on the localization

The filter descends to the away localization exactly as the sign projection did in #526: a
representative is filtered, well-definedness is the shift identity plus cross-multiplication,
and the resulting map is pinned by its `awayMk` equation. -/

attribute [local instance] MvPolynomial.gradedAlgebra

variable {σM : Type u} [SetLike σM (MvPolynomial ι R)]
  [AddSubgroupClass σM (MvPolynomial ι R)] {𝓜 : ℕ → σM}
  [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] {d : ℤ}

/-- The block-filtered representative: keep the numerator's monomials in block `F`. -/
noncomputable def AwayRep.blockFilter (h𝓜 : IsPolynomialTwist 𝓜 d) {γ : ι →₀ ℕ}
    (F : Finset ι)
    (r : AwayRep ι R 𝓜 γ) : AwayRep ι R 𝓜 γ where
  pow := r.pow
  num := laurentFilter γ r.pow F r.num
  num_mem := IsPolynomialTwist.laurentFilter_mem h𝓜 r.num_mem

set_option maxHeartbeats 800000 in
/-- Filtering a representative is the same as raising it first and then filtering. This is
`laurentFilter_monomial_mul` at `σ = t • γ` on the numerator and `awayMk_shift` on the
fraction; well-definedness follows exactly as it did for the sign projection. -/
theorem AwayRep.frac_blockFilter_raise (h𝓜 : IsPolynomialTwist 𝓜 d) {γ : ι →₀ ℕ}
    (F : Finset ι)
    (r : AwayRep ι R 𝓜 γ) (t : ℕ) :
    (r.blockFilter h𝓜 F).frac =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) (r.pow + t)
        (laurentFilter γ (r.pow + t) F ((MvPolynomial.monomial γ (1 : R)) ^ t * r.num))
        (IsPolynomialTwist.laurentFilter_mem h𝓜 (r.pow_mul_num_mem h𝓜 t)) := by
  have hσ : t • γ + r.pow • γ = (r.pow + t) • γ := by
    rw [← add_nsmul, Nat.add_comm t r.pow]
  have hnum : laurentFilter γ (r.pow + t) F ((MvPolynomial.monomial γ (1 : R)) ^ t * r.num) =
      (MvPolynomial.monomial γ (1 : R)) ^ t * laurentFilter γ r.pow F r.num := by
    rw [monomial_one_pow]
    exact laurentFilter_monomial_mul hσ F r.num
  have hmem2 : (MvPolynomial.monomial γ (1 : R)) ^ t • laurentFilter γ r.pow F r.num ∈
      𝓜 ((r.pow + t) • γ.degree) := by
    simp only [smul_eq_mul, ← hnum]
    exact IsPolynomialTwist.laurentFilter_mem h𝓜 (r.pow_mul_num_mem h𝓜 t)
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 ((r.pow + t) • γ.degree))
      (hb : b ∈ 𝓜 ((r.pow + t) • γ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) (r.pow + t) a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) (r.pow + t) b hb := by
    rintro a b ha hb rfl; rfl
  refine Eq.symm (Eq.trans (hcongr _ _ _ hmem2 hnum) ?_)
  exact DegreeZeroLocalization.awayMk_shift
    (monomial_one_mem_polynomialGrading (R := R) γ) r.pow t
    (laurentFilter γ r.pow F r.num) (IsPolynomialTwist.laurentFilter_mem h𝓜 r.num_mem) hmem2

set_option maxHeartbeats 800000 in
/-- **Well-definedness.** Two representatives of one fraction filter to the same fraction. -/
theorem AwayRep.frac_blockFilter_congr [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ : ι →₀ ℕ} (F : Finset ι)
    {r₁ r₂ : AwayRep ι R 𝓜 γ} (h : r₁.frac = r₂.frac) :
    (r₁.blockFilter h𝓜 F).frac = (r₂.blockFilter h𝓜 F).frac := by
  have hcross : (MvPolynomial.monomial γ (1 : R)) ^ r₂.pow * r₁.num =
      (MvPolynomial.monomial γ (1 : R)) ^ r₁.pow * r₂.num := by
    have hx := (DegreeZeroLocalization.awayMk_eq_awayMk_iff
      (monomial_one_mem_polynomialGrading (R := R) γ)
      (monomial_one_ne_zero (R := R) γ) r₁.num_mem r₂.num_mem).mp h
    simpa [smul_eq_mul] using hx
  have hgen : ∀ (n₁ n₂ : ℕ) (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (n₁ • γ.degree))
      (hb : b ∈ 𝓜 (n₂ • γ.degree)),
      n₁ = n₂ → a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) n₁ a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) n₂ b hb := by
    rintro n₁ n₂ a b ha hb rfl rfl; rfl
  refine (r₁.frac_blockFilter_raise h𝓜 F r₂.pow).trans
    (Eq.trans (hgen _ _ _ _ _ _ (Nat.add_comm _ _) ?_)
      (r₂.frac_blockFilter_raise h𝓜 F r₁.pow).symm)
  rw [Nat.add_comm r₁.pow r₂.pow, hcross]

/-- **The block projection**, as a map on the localization. Defined by choosing a
representative; `blockProj_awayMk` is the equation that pins it down and is what every caller
should use. -/
noncomputable def blockProj [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (γ : ι →₀ ℕ)
    (F : Finset ι)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R))) :=
  ((AwayRep.frac_surjective 𝓜 γ z).choose.blockFilter h𝓜 F).frac

theorem blockProj_frac [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (γ : ι →₀ ℕ)
    (F : Finset ι) (r : AwayRep ι R 𝓜 γ) :
    blockProj h𝓜 γ F r.frac = (r.blockFilter h𝓜 F).frac :=
  AwayRep.frac_blockFilter_congr h𝓜 F (AwayRep.frac_surjective 𝓜 γ r.frac).choose_spec

/-- **The defining equation of the block projection**: on a representative it filters the
numerator and keeps the exponent. -/
theorem blockProj_awayMk [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (γ : ι →₀ ℕ)
    (F : Finset ι) {m : ℕ}
    {p : MvPolynomial ι R}
    (hp : p ∈ 𝓜 (m • γ.degree)) :
    blockProj h𝓜 γ F
        (DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m p hp) =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m (laurentFilter γ m F p)
        (IsPolynomialTwist.laurentFilter_mem h𝓜 hp) :=
  blockProj_frac h𝓜 γ F ⟨m, p, hp⟩

set_option maxHeartbeats 800000 in
/-- The block projection is additive: align the fractions at a common denominator, where it is
`laurentFilter_add`. -/
theorem blockProj_add [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (γ : ι →₀ ℕ)
    (F : Finset ι)
    (z₁ z₂ : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    blockProj h𝓜 γ F (z₁ + z₂) = blockProj h𝓜 γ F z₁ + blockProj h𝓜 γ F z₂ := by
  obtain ⟨m, p₁, p₂, hp₁, hp₂, rfl, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk_pair
      (monomial_one_mem_polynomialGrading (R := R) γ) (monomial_one_pow_ne_zero γ) z₁ z₂
  rw [← DegreeZeroLocalization.awayMk_add
      (monomial_one_mem_polynomialGrading (R := R) γ) m p₁ p₂ hp₁ hp₂,
    blockProj_awayMk h𝓜 γ F, blockProj_awayMk h𝓜 γ F, blockProj_awayMk h𝓜 γ F,
    ← DegreeZeroLocalization.awayMk_add (monomial_one_mem_polynomialGrading (R := R) γ) m _ _
      (IsPolynomialTwist.laurentFilter_mem h𝓜 hp₁) (IsPolynomialTwist.laurentFilter_mem h𝓜 hp₂)]
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • γ.degree))
      (hb : b ∈ 𝓜 (m • γ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m b hb := by
    rintro a b ha hb rfl; rfl
  exact hcongr _ _ _ _ (laurentFilter_add γ m F p₁ p₂)

/-- The block projection bundled as an additive map. -/
noncomputable def blockProjHom [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (γ : ι →₀ ℕ)
    (F : Finset ι) :
    DegreeZeroLocalization (polynomialGrading ι R)
        (𝓜)
        (.powers (MvPolynomial.monomial γ (1 : R))) →+
      DegreeZeroLocalization (polynomialGrading ι R)
        (𝓜)
        (.powers (MvPolynomial.monomial γ (1 : R))) :=
  AddMonoidHom.mk' (blockProj h𝓜 γ F) (blockProj_add h𝓜 γ F)

@[simp]
theorem blockProjHom_apply [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (γ : ι →₀ ℕ)
    (F : Finset ι)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    blockProjHom h𝓜 γ F z = blockProj h𝓜 γ F z :=
  rfl

set_option maxHeartbeats 800000 in
/-- **The blocks exhaust the localization.** The projections over the finite index
`γ.support.powerset` sum to the identity. This is the whole decomposition step in the form the
vanishing argument consumes: no direct sum, no reindexed complex — each element *is* the finite
sum of its blocks, one localization at a time. -/
theorem sum_blockProj [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (γ : ι →₀ ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    ∑ F ∈ γ.support.powerset, blockProj h𝓜 γ F z = z := by
  obtain ⟨m, p, hp, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := R) γ) (monomial_one_pow_ne_zero γ) z
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • γ.degree))
      (hb : b ∈ 𝓜 (m • γ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m b hb := by
    rintro a b ha hb rfl; rfl
  calc ∑ F ∈ γ.support.powerset, blockProj h𝓜 γ F
        (DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m p hp)
      = ∑ F ∈ γ.support.powerset,
          DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
            (monomial_one_mem_polynomialGrading (R := R) γ) m (laurentFilter γ m F p)
            (IsPolynomialTwist.laurentFilter_mem h𝓜 hp) :=
        Finset.sum_congr rfl fun F _ => blockProj_awayMk h𝓜 γ F hp
    _ = DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m
          (∑ F ∈ γ.support.powerset, laurentFilter γ m F p)
          (sum_mem fun F _ => IsPolynomialTwist.laurentFilter_mem h𝓜 hp) :=
        (DegreeZeroLocalization.awayMk_sum
          (monomial_one_mem_polynomialGrading (R := R) γ) m γ.support.powerset
          (fun F => laurentFilter γ m F p) fun F => IsPolynomialTwist.laurentFilter_mem h𝓜 hp).symm
    _ = DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m p hp :=
        hcongr _ _ _ _ (sum_laurentFilter_powerset γ m p)

/-- The block projections are idempotent. -/
theorem blockProj_blockProj_self [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (γ : ι →₀ ℕ)
    (F : Finset ι)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    blockProj h𝓜 γ F (blockProj h𝓜 γ F z) = blockProj h𝓜 γ F z := by
  obtain ⟨m, p, hp, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := R) γ) (monomial_one_pow_ne_zero γ) z
  rw [blockProj_awayMk h𝓜 γ F, blockProj_awayMk h𝓜 γ F]
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • γ.degree))
      (hb : b ∈ 𝓜 (m • γ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m b hb := by
    rintro a b ha hb rfl; rfl
  exact hcongr _ _ _ _ (laurentFilter_laurentFilter_self γ m F p)

/-- Distinct block projections are orthogonal. -/
theorem blockProj_blockProj_of_ne [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {F F' : Finset ι} (h : F ≠ F') (γ : ι →₀ ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    blockProj h𝓜 γ F (blockProj h𝓜 γ F' z) = 0 := by
  obtain ⟨m, p, hp, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := R) γ) (monomial_one_pow_ne_zero γ) z
  rw [blockProj_awayMk h𝓜 γ F', blockProj_awayMk h𝓜 γ F]
  have hcongr : ∀ (a : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • γ.degree)), a = 0 →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha = 0 := by
    rintro a ha rfl
    exact DegreeZeroLocalization.awayMk_zero (monomial_one_mem_polynomialGrading (R := R) γ) m
  exact hcongr _ _ (laurentFilter_laurentFilter_of_ne h γ m p)

/-- A block outside the denominator's support projects to zero. -/
theorem blockProj_eq_zero_of_not_subset [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ : ι →₀ ℕ} {F : Finset ι} (h : ¬ F ⊆ γ.support)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    blockProj h𝓜 γ F z = 0 := by
  obtain ⟨m, p, hp, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := R) γ) (monomial_one_pow_ne_zero γ) z
  rw [blockProj_awayMk h𝓜 γ F]
  have hcongr : ∀ (a : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • γ.degree)), a = 0 →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha = 0 := by
    rintro a ha rfl
    exact DegreeZeroLocalization.awayMk_zero (monomial_one_mem_polynomialGrading (R := R) γ) m
  exact hcongr _ _ (laurentFilter_eq_zero_of_not_subset h m p)

/-! ## The faces commute with the block projections

A Čech face multiplies numerator and denominator together, so the Laurent exponent of every
monomial — and with it the block — never moves. This is the statement "the differential
preserves `N α`" of #340's proof plan, one face and one localization at a time. -/

set_option maxHeartbeats 1200000 in
/-- **The faces commute with the block projections.** Restricting along `X_e` and then taking
the block-`F` component is taking the block-`F` component and restricting after. This is
`laurentFilter_monomial_mul` at `σ = m • single e c`; no restriction on `F` is needed, in
contrast to the sign projection's square. -/
theorem laurentFace_blockProj [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {e : ι} {c : ℕ}
    (hγ : γ = Finsupp.single e c + γ') (F : Finset ι)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ' (1 : R)))) :
    laurentFace 𝓜 hγ (blockProj h𝓜 γ' F z) = blockProj h𝓜 γ F (laurentFace 𝓜 hγ z) := by
  obtain ⟨m, q, hq, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := R) γ') (monomial_one_pow_ne_zero γ') z
  have hdeg : γ.degree = c + γ'.degree := by rw [hγ, map_add, Finsupp.degree_single]
  have hres : (MvPolynomial.monomial (Finsupp.single e c) (1 : R)) ^ m •
      laurentFilter γ' m F q ∈
      𝓜 (m • (c + γ'.degree)) :=
    monomial_single_pow_smul_mem h𝓜 (IsPolynomialTwist.laurentFilter_mem h𝓜 hq)
  have hres' : (MvPolynomial.monomial (Finsupp.single e c) (1 : R)) ^ m • q ∈
      𝓜 (m • (c + γ'.degree)) :=
    monomial_single_pow_smul_mem h𝓜 hq
  rw [blockProj_awayMk h𝓜 γ' F,
    laurentFace_awayMk hγ (IsPolynomialTwist.laurentFilter_mem h𝓜 hq) hres,
    DegreeZeroLocalization.awayMk_deg_congr hdeg.symm (monomial_mem_add_degree hγ)
      (monomial_one_mem_polynomialGrading (R := R) γ) m _ hres (by rw [hdeg]; exact hres),
    laurentFace_awayMk hγ hq hres',
    DegreeZeroLocalization.awayMk_deg_congr hdeg.symm (monomial_mem_add_degree hγ)
      (monomial_one_mem_polynomialGrading (R := R) γ) m _ hres' (by rw [hdeg]; exact hres'),
    blockProj_awayMk h𝓜 γ F]
  have hσ : Finsupp.single e (m * c) + m • γ' = m • γ := by
    rw [hγ, smul_add, Finsupp.smul_single, smul_eq_mul]
  have hmono : (MvPolynomial.monomial (Finsupp.single e c) (1 : R)) ^ m =
      MvPolynomial.monomial (Finsupp.single e (m * c)) 1 := by
    rw [monomial_one_pow, Finsupp.smul_single, smul_eq_mul]
  have hnum : (MvPolynomial.monomial (Finsupp.single e c) (1 : R)) ^ m •
      laurentFilter γ' m F q =
      laurentFilter γ m F
        ((MvPolynomial.monomial (Finsupp.single e c) (1 : R)) ^ m • q) := by
    rw [hmono, smul_eq_mul, smul_eq_mul, laurentFilter_monomial_mul hσ F q]
  have hgen : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • γ.degree))
      (hb : b ∈ 𝓜 (m • γ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m b hb := by
    rintro a b ha hb rfl; rfl
  exact hgen _ _ _ _ hnum

end AlgebraicGeometry.Proj
