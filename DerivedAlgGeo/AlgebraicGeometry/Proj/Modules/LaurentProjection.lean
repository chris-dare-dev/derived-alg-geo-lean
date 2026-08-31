/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.MvPolynomial.LaurentBasis
import DerivedAlgGeo.Algebra.MvPolynomial.DivMonomial

/-!
# The numerator side of the sign projection

The contracting homotopy of #340 needs a **sign projection**: given a monomial denominator
`Xᵞ = X_{i₀}^c · Xᵞ'` with `γ' i₀ = 0`, a map

```
π : (A(d)_{Xᵞ})₀ → (A(d)_{Xᵞ'})₀
```

that keeps exactly the Laurent monomials whose `i₀`-exponent has not gone negative — the ones
still admissible once `X_{i₀}` is no longer inverted.

On a representative `p / (Xᵞ)ᵐ` that operation is *division by a monomial*: keep the terms of `p`
divisible by `X_{i₀}^{m·c}` and shift them down. The geometry-free division identities live in
`DerivedAlgGeo.Algebra.MvPolynomial.DivMonomial`; this file begins where those facts are applied to
projective graded localizations.

## Main statements

* `divMonomial_mem_natShift` — the degree bookkeeping: dividing off `X_{i₀}^{m·c}` moves a
  numerator for `Xᵞ` at twist `d` to a numerator for `Xᵞ'` at the same twist. The twist is
  untouched, which is what keeps `π` a map of `O(d)`-sections.
* `signProjection` — **the projection itself**, with `signProjection_awayMk` the equation that
  pins it down and `signProjection_laurentFace` the retraction `π ∘ ι = id`.
* `MvPolynomial.divMonomial_pow_mul` — **the well-definedness identity.** Raising a representative
  to a higher power of `Xᵞ` and then projecting is the same as projecting and then raising to a
  higher power of `Xᵞ'`:
  ```
  ((Xᵞ)ᵗ · p) /ᵐᵒⁿᵒᵐⁱᵃˡ X_{i₀}^{(m+t)c}  =  (Xᵞ')ᵗ · (p /ᵐᵒⁿᵒᵐⁱᵃˡ X_{i₀}^{m·c})
  ```
  Paired with `DegreeZeroLocalization.awayMk_shift`, this is exactly what makes the projection
  independent of the chosen representative: any two representatives of one element become equal
  numerators after raising both to a common denominator, and this identity says the projection
  survives that move.

## Implementation notes

`MvPolynomial.divMonomial_monomial_mul_comm` is the key generic polynomial fact. A monomial
factor may be pulled out through a division only when the two monomials have **disjoint support**
— the hypothesis `∀ j, a j = 0 ∨ s j = 0`. Without it the statement is false: dividing `X_{i₀}`
out of `X_{i₀} · p` is not `X_{i₀} ·` anything. The disjointness is available here for a
structural reason, not a lucky one: the factor being pulled out is a power of `Xᵞ'`, which by
hypothesis does not involve `i₀`, while the divisor is a pure power of `X_{i₀}`.

The `γ = X_{i₀}^c · γ'` splitting is taken as a hypothesis rather than built with `Finsupp.erase`.
The caller that matters is a Čech face, which produces the two pieces separately (`c = 1` and
`γ'` the denominator of the smaller intersection) and never has to take them apart again.

## Tags

monomial division, homogeneous localization, projective space
-/

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

universe u

variable {ι R : Type u} [CommRing R]

/-! ## The projection on numerators -/

attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 800000 in
/-- **The degree bookkeeping.** Dividing off `X_{i₀}^{m·c}` carries a numerator for `Xᵞ` at twist
`d` to a numerator for `Xᵞ'` at the *same* twist `d`.

Only the denominator's contribution `m • γ.degree` moves; the twist is untouched. That is what
makes the projection a map of `O(d)`-sections rather than a comparison between different
twists. -/
theorem divMonomial_mem_natShift {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') {d m : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ natShift (polynomialGrading ι R) d (m • γ.degree)) :
    MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) ∈
      natShift (polynomialGrading ι R) d (m • γ'.degree) := by
  have hdeg : γ.degree = c + γ'.degree := by
    rw [hγ, map_add, Finsupp.degree_single]
  refine isHomogeneous_divMonomial (s := Finsupp.single i₀ (m * c)) ?_
  rw [Finsupp.degree_single]
  have hsplit : m • γ.degree + d = m * c + (m • γ'.degree + d) := by
    rw [hdeg, smul_eq_mul, smul_eq_mul]; ring
  rw [← hsplit]
  exact hp

set_option maxHeartbeats 800000 in
/-- **The degree bookkeeping, for a twist of either sign.**

`divMonomial_mem_natShift` with `natShift` replaced by any `IsPolynomialTwist`. The twist is again
untouched: only the denominator's contribution `m • γ.degree` moves.

The nonnegative proof reads the membership as homogeneity and cancels `m * c` off the degree
directly. That cancellation is not available here, because a negative twist can put the numerator's
degree below `m * c` — and then there is nothing to divide, so the quotient is zero and the `p = 0`
disjunct of `IsPolynomialTwist` carries it. The `by_cases` on the quotient is therefore not
defensive bookkeeping; it is the only place the two signs behave differently in this whole
argument. -/
theorem IsPolynomialTwist.divMonomial_mem {σM : Type u} [SetLike σM (MvPolynomial ι R)]
    {𝓜 : ℕ → σM} {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ} (hγ : γ = Finsupp.single i₀ c + γ') {m : ℕ}
    {p : MvPolynomial ι R} (hp : p ∈ 𝓜 (m • γ.degree)) :
    MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) ∈ 𝓜 (m • γ'.degree) := by
  classical
  by_cases hq : MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) = 0
  · exact (h𝓜 _ _).mpr (Or.inl hq)
  -- The quotient is nonzero, so some exponent of `p` is divisible by `X_{i₀}^{m * c}`; its degree
  -- is what pins the quotient's homogeneous degree.
  obtain ⟨β, hβ⟩ := MvPolynomial.support_nonempty.mpr hq
  have hcoeff : MvPolynomial.coeff (Finsupp.single i₀ (m * c) + β) p ≠ 0 := by
    have := MvPolynomial.mem_support_iff.mp hβ
    rwa [MvPolynomial.coeff_divMonomial] at this
  have hmem : Finsupp.single i₀ (m * c) + β ∈ p.support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hdeg := h𝓜.degree_eq_of_mem_support hp hmem
  rw [map_add, Finsupp.degree_single] at hdeg
  have hγdeg : γ.degree = c + γ'.degree := by
    rw [hγ, map_add, Finsupp.degree_single]
  -- The target degree, in `ℕ`, and the identity that places it.
  have hβdeg : (β.degree : ℤ) = ((m • γ'.degree : ℕ) : ℤ) + d := by
    rw [hγdeg] at hdeg
    push_cast [Nat.cast_mul] at hdeg ⊢
    push_cast [nsmul_eq_mul] at hdeg ⊢
    linarith
  refine (h𝓜 _ _).mpr (Or.inr ⟨β.degree, hβdeg, ?_⟩)
  -- `p` is homogeneous in degree `m * c + β.degree`, so the quotient is homogeneous in `β.degree`.
  rcases (h𝓜 _ p).mp hp with rfl | ⟨e, he, hhom⟩
  · exact absurd (by simp) hcoeff
  have hesplit : e = m * c + β.degree := by
    have : (e : ℤ) = ((m * c + β.degree : ℕ) : ℤ) := by
      rw [he, hγdeg]
      push_cast [Nat.cast_mul] at hβdeg ⊢
      push_cast [nsmul_eq_mul] at hβdeg ⊢
      linarith
    exact_mod_cast this
  refine isHomogeneous_divMonomial (s := Finsupp.single i₀ (m * c)) ?_
  rw [Finsupp.degree_single]
  exact hesplit ▸ hhom

/-- **Multiplying a numerator by a homogeneous factor** raises its graded piece by that factor's
degree and leaves the twist alone.

Three places need this — raising a representative to a higher power of the denominator, and the
two columns of the projection square — and each of them read `natShift`'s membership as
homogeneity directly. Through `IsPolynomialTwist` the reading is a case split, because the
numerator may be zero in a degree the twist names no graded piece for. -/
theorem IsPolynomialTwist.mul_mem_of_isHomogeneous {σM : Type u} [SetLike σM (MvPolynomial ι R)]
    {𝓜 : ℕ → σM} {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d) {a : MvPolynomial ι R} {k n n' : ℕ}
    (ha : a.IsHomogeneous k) (hn : n' = k + n) {p : MvPolynomial ι R} (hp : p ∈ 𝓜 n) :
    a * p ∈ 𝓜 n' := by
  rcases (h𝓜 n p).mp hp with rfl | ⟨e, he, hhom⟩
  · exact (h𝓜 _ _).mpr (Or.inl (by rw [mul_zero]))
  refine (h𝓜 _ _).mpr (Or.inr ⟨k + e, ?_, ha.mul hhom⟩)
  rw [hn]
  push_cast at he ⊢
  linarith

/-! ## The projection itself

The numerator operation descends to a map on the localization. A representative is packaged as
`AwayRep`; `AwayRep.frac_project_congr` says two representatives of one element project to the
same fraction, and `signProjection` is the resulting map, chosen through `Exists.choose` and
pinned by `signProjection_awayMk`. -/

variable {σM : Type u} [SetLike σM (MvPolynomial ι R)]
  [AddSubgroupClass σM (MvPolynomial ι R)]

/-- A representative `p / (Xᵞ)ᵐ` of a degree-zero fraction of the twist `𝓜`.

The twist is carried by the graded family rather than by a natural number, so that the whole
projection layer is available at either sign; `IsPolynomialTwist 𝓜 d` is the hypothesis the
degree bookkeeping consumes, and it is required only where a degree actually moves. -/
structure AwayRep (ι R : Type u) [CommRing R] {σM : Type u} [SetLike σM (MvPolynomial ι R)]
    (𝓜 : ℕ → σM) (γ : ι →₀ ℕ) where
  /-- The exponent of the denominator. -/
  pow : ℕ
  /-- The numerator. -/
  num : MvPolynomial ι R
  /-- The numerator sits in the graded piece the denominator forces. -/
  num_mem : num ∈ 𝓜 (pow • γ.degree)

variable {𝓜 : ℕ → σM} [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] {d : ℤ}

/-- The fraction a representative names. -/
noncomputable def AwayRep.frac {γ : ι →₀ ℕ} (r : AwayRep ι R 𝓜 γ) :
    DegreeZeroLocalization (polynomialGrading ι R) 𝓜
      (.powers (MvPolynomial.monomial γ (1 : R))) :=
  DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
    (monomial_one_mem_polynomialGrading (R := R) γ) r.pow r.num r.num_mem

/-- Every fraction has a representative — this is `exists_awayMk`, repackaged. -/
theorem AwayRep.frac_surjective [Nontrivial R] (𝓜 : ℕ → σM)
    [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] (γ : ι →₀ ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R) 𝓜
      (.powers (MvPolynomial.monomial γ (1 : R)))) :
    ∃ r : AwayRep ι R 𝓜 γ, r.frac = z := by
  obtain ⟨m, p, hp, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk (monomial_one_mem_polynomialGrading (R := R) γ)
      (monomial_one_pow_ne_zero γ) z
  exact ⟨⟨m, p, hp⟩, rfl⟩

/-- The projected representative: divide the numerator by `X_{i₀}^{m·c}`, keep the exponent. -/
noncomputable def AwayRep.project (h𝓜 : IsPolynomialTwist 𝓜 d) {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (r : AwayRep ι R 𝓜 γ) : AwayRep ι R 𝓜 γ' where
  pow := r.pow
  num := MvPolynomial.divMonomial r.num (Finsupp.single i₀ (r.pow * c))
  num_mem := IsPolynomialTwist.divMonomial_mem h𝓜 hγ r.num_mem

omit [AddSubgroupClass σM (MvPolynomial ι R)]
  [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] in
/-- Raising a representative by `(Xᵞ)ᵗ` keeps it a legitimate numerator.

The nonnegative proof read `num_mem` as homogeneity directly. Here the reading goes through
`IsPolynomialTwist`, which also supplies the zero case — a numerator may be zero in a degree
where the twist names no graded piece at all. -/
theorem AwayRep.pow_mul_num_mem (h𝓜 : IsPolynomialTwist 𝓜 d) {γ : ι →₀ ℕ}
    (r : AwayRep ι R 𝓜 γ) (t : ℕ) :
    ((MvPolynomial.monomial γ (1 : R)) ^ t * r.num) ∈ 𝓜 ((r.pow + t) • γ.degree) := by
  have h1 : ((MvPolynomial.monomial γ (1 : R)) ^ t).IsHomogeneous (t * γ.degree) := by
    rw [monomial_one_pow]
    exact MvPolynomial.isHomogeneous_monomial 1 (by rw [map_nsmul, smul_eq_mul])
  exact IsPolynomialTwist.mul_mem_of_isHomogeneous h𝓜 h1 (by simp only [smul_eq_mul]; ring) r.num_mem

set_option maxHeartbeats 1200000 in
/-- Projecting a representative is the same as raising it first and then projecting.

This is `divMonomial_pow_mul` on the numerator and `awayMk_shift` on the fraction, and it is the
only place either is used. Well-definedness follows immediately: it lets both representatives of
one element be moved to the *same* exponent before they are compared. -/
theorem AwayRep.frac_project_raise (h𝓜 : IsPolynomialTwist 𝓜 d) {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0)
    (r : AwayRep ι R 𝓜 γ) (t : ℕ) :
    (r.project h𝓜 hγ).frac =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ') (r.pow + t)
        (MvPolynomial.divMonomial ((MvPolynomial.monomial γ (1 : R)) ^ t * r.num)
          (Finsupp.single i₀ ((r.pow + t) * c)))
        (IsPolynomialTwist.divMonomial_mem h𝓜 hγ (r.pow_mul_num_mem h𝓜 t)) := by
  have hnum := divMonomial_pow_mul hγ hγ' r.pow t r.num
  have hmem2 : (MvPolynomial.monomial γ' (1 : R)) ^ t •
      MvPolynomial.divMonomial r.num (Finsupp.single i₀ (r.pow * c)) ∈
      𝓜 ((r.pow + t) • γ'.degree) := by
    simp only [smul_eq_mul, ← hnum]
    exact IsPolynomialTwist.divMonomial_mem h𝓜 hγ (r.pow_mul_num_mem h𝓜 t)
  have hcongr : ∀ (n : ℕ) (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (n • γ'.degree)) (hb : b ∈ 𝓜 (n • γ'.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ') n a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ') n b hb := by
    rintro n a b ha hb rfl; rfl
  refine Eq.symm (Eq.trans (hcongr (r.pow + t) _ _ _ hmem2 hnum) ?_)
  exact DegreeZeroLocalization.awayMk_shift
    (monomial_one_mem_polynomialGrading (R := R) γ') r.pow t
    (MvPolynomial.divMonomial r.num (Finsupp.single i₀ (r.pow * c)))
    (IsPolynomialTwist.divMonomial_mem h𝓜 hγ r.num_mem) hmem2

set_option maxHeartbeats 1200000 in
/-- **Well-definedness.** Two representatives of one fraction project to the same fraction.

`awayMk_eq_awayMk_iff` turns the hypothesis into a cross-multiplication of numerators, and
`frac_project_raise` moves both projections to the common exponent `r₁.pow + r₂.pow` where that
cross-multiplication is literally the equality of numerators. -/
theorem AwayRep.frac_project_congr [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0)
    {r₁ r₂ : AwayRep ι R 𝓜 γ} (h : r₁.frac = r₂.frac) :
    (r₁.project h𝓜 hγ).frac = (r₂.project h𝓜 hγ).frac := by
  have hcross : (MvPolynomial.monomial γ (1 : R)) ^ r₂.pow * r₁.num =
      (MvPolynomial.monomial γ (1 : R)) ^ r₁.pow * r₂.num := by
    have hx := (DegreeZeroLocalization.awayMk_eq_awayMk_iff
      (monomial_one_mem_polynomialGrading (R := R) γ)
      (monomial_one_ne_zero (R := R) γ) r₁.num_mem r₂.num_mem).mp h
    simpa [smul_eq_mul] using hx
  have hgen : ∀ (n₁ n₂ : ℕ) (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (n₁ • γ'.degree)) (hb : b ∈ 𝓜 (n₂ • γ'.degree)),
      n₁ = n₂ → a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ') n₁ a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ') n₂ b hb := by
    rintro n₁ n₂ a b ha hb rfl rfl; rfl
  refine (r₁.frac_project_raise h𝓜 hγ hγ' r₂.pow).trans
    (Eq.trans (hgen _ _ _ _ _ _ (Nat.add_comm _ _) ?_)
      (r₂.frac_project_raise h𝓜 hγ hγ' r₁.pow).symm)
  rw [Nat.add_comm r₁.pow r₂.pow, hcross]

/-- **The sign projection**, as a map on the localization.

Defined by choosing a representative; `signProjection_awayMk` is the equation that pins it down
and is what every caller should use. The hypothesis `γ' i₀ = 0` is not needed to *make* the
definition — only to make it independent of the choice — so it is required by the equations rather
than by the definition. -/
noncomputable def signProjection [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ} (hγ : γ = Finsupp.single i₀ c + γ')
    (z : DegreeZeroLocalization (polynomialGrading ι R) 𝓜
      (.powers (MvPolynomial.monomial γ (1 : R)))) :
    DegreeZeroLocalization (polynomialGrading ι R) 𝓜
      (.powers (MvPolynomial.monomial γ' (1 : R))) :=
  ((AwayRep.frac_surjective 𝓜 γ z).choose.project h𝓜 hγ).frac

theorem signProjection_frac [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) (r : AwayRep ι R 𝓜 γ) :
    signProjection h𝓜 hγ r.frac = (r.project h𝓜 hγ).frac :=
  AwayRep.frac_project_congr h𝓜 hγ hγ' (AwayRep.frac_surjective 𝓜 γ r.frac).choose_spec

/-- **The defining equation of the sign projection**: on a representative it divides the numerator
by `X_{i₀}^{m·c}` and keeps the exponent. -/
theorem signProjection_awayMk [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) {m : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ 𝓜 (m • γ.degree)) :
    signProjection h𝓜 hγ
        (DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m p hp) =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ') m
        (MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)))
        (IsPolynomialTwist.divMonomial_mem h𝓜 hγ hp) :=
  signProjection_frac h𝓜 hγ hγ' ⟨m, p, hp⟩

/-! ## The projection retracts the face inclusion -/

theorem monomial_single_mem (i₀ : ι) (c : ℕ) :
    (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ∈ polynomialGrading ι R c := by
  have h := monomial_one_mem_polynomialGrading (R := R) (Finsupp.single i₀ c)
  rwa [Finsupp.degree_single] at h

theorem laurentFace_mul {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') :
    (MvPolynomial.monomial γ' (1 : R)) * MvPolynomial.monomial (Finsupp.single i₀ c) 1 =
      MvPolynomial.monomial γ 1 := by
  rw [MvPolynomial.monomial_mul, one_mul, hγ, add_comm]

theorem monomial_mem_add_degree {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') :
    (MvPolynomial.monomial γ (1 : R)) ∈ polynomialGrading ι R (c + γ'.degree) := by
  have h := monomial_one_mem_polynomialGrading (R := R) γ
  have hd : γ.degree = c + γ'.degree := by rw [hγ, map_add, Finsupp.degree_single]
  rwa [hd] at h

/-- The face inclusion `(A(d)_{Xᵞ'})₀ → (A(d)_{Xᵞ})₀`, in the shape the sign projection
retracts. This is `DegreeZeroLocalization.faceMap` at `g₁ * h = g₂` with `h = X_{i₀}^c`, which is
exactly the Čech face of #340's complex. -/
noncomputable def laurentFace (𝓜 : ℕ → σM) [SetLike.GradedSMul (polynomialGrading ι R) 𝓜]
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ} (hγ : γ = Finsupp.single i₀ c + γ') :
    DegreeZeroLocalization (polynomialGrading ι R)
        (𝓜) (.powers (MvPolynomial.monomial γ' (1 : R))) →+
      DegreeZeroLocalization (polynomialGrading ι R)
        (𝓜) (.powers (MvPolynomial.monomial γ (1 : R))) :=
  DegreeZeroLocalization.faceMap (𝓜 := 𝓜)
    (monomial_single_mem i₀ c)
    ⟨1, by show (MvPolynomial.monomial γ (1 : R)) ^ 1 = _; rw [pow_one, laurentFace_mul hγ]⟩
    (laurentFace_mul hγ)

set_option maxHeartbeats 1200000 in
/-- The face inclusion in `awayMk` normal form: it multiplies the numerator by
`X_{i₀}^{m·c}`. -/
theorem laurentFace_awayMk {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') {m : ℕ} {q : MvPolynomial ι R}
    (hq : q ∈ 𝓜 (m • γ'.degree))
    (hres : (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m • q ∈
      𝓜 (m • (c + γ'.degree))) :
    laurentFace 𝓜 hγ (DegreeZeroLocalization.awayMk
        (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ') m q hq) =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_mem_add_degree hγ) m
        ((MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m • q) hres :=
  DegreeZeroLocalization.faceMap_awayMk _ (monomial_one_mem_polynomialGrading (R := R) γ') _ _
    (monomial_mem_add_degree hγ) m q hq hres

set_option maxHeartbeats 1200000 in
/-- **The sign projection retracts the face inclusion**: `π ∘ ι = id`.

This is the first of the two properties #340's homotopy consumes. On a representative the face
multiplies the numerator by `X_{i₀}^{m·c}` and the projection divides it straight back out
(`divMonomial_monomial_mul`), so nothing survives to check — the content is all in the degree
bookkeeping, and in `awayMk_deg_congr` reconciling the two names `γ.degree` and `c + γ'.degree`
for the same natural number. -/
theorem signProjection_laurentFace [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ' (1 : R)))) :
    signProjection h𝓜 hγ (laurentFace 𝓜 hγ z) = z := by
  obtain ⟨m, q, hq, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk (monomial_one_mem_polynomialGrading (R := R) γ')
      (monomial_one_pow_ne_zero γ') z
  have hdeg : γ.degree = c + γ'.degree := by rw [hγ, map_add, Finsupp.degree_single]
  have hmono : (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m =
      MvPolynomial.monomial (Finsupp.single i₀ (m * c)) 1 := by
    rw [monomial_one_pow, Finsupp.smul_single, smul_eq_mul]
  have hres : (MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m • q ∈
      𝓜 (m • (c + γ'.degree)) := by
    have h1 : ((MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m).IsHomogeneous
        (m * c) := by
      rw [hmono]
      exact MvPolynomial.isHomogeneous_monomial 1 (by rw [Finsupp.degree_single])
    rw [smul_eq_mul]
    exact IsPolynomialTwist.mul_mem_of_isHomogeneous h𝓜 h1 (by simp only [smul_eq_mul]; ring) hq
  rw [laurentFace_awayMk hγ hq hres,
    DegreeZeroLocalization.awayMk_deg_congr hdeg.symm (monomial_mem_add_degree hγ)
      (monomial_one_mem_polynomialGrading (R := R) γ) m _ hres
      (by rw [hdeg]; exact hres),
    signProjection_awayMk h𝓜 hγ hγ']
  have hnum : MvPolynomial.divMonomial
      ((MvPolynomial.monomial (Finsupp.single i₀ c) (1 : R)) ^ m • q)
      (Finsupp.single i₀ (m * c)) = q := by
    rw [hmono, smul_eq_mul, MvPolynomial.divMonomial_monomial_mul]
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • γ'.degree))
      (hb : b ∈ 𝓜 (m • γ'.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ') m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ') m b hb := by
    rintro a b ha hb rfl; rfl
  exact hcongr _ _ _ hq hnum

/-! ## Additivity of the projection

The contracting homotopy applies the projection to an alternating sum of faces, so it consumes
the projection as an additive map. Additivity is not free from the definition — `signProjection`
is choice-based — but it reduces to the defining equation once the two summands are put over a
common denominator, which is exactly what `DegreeZeroLocalization.exists_awayMk_pair` supplies.
This is the first use of that lemma outside `frac_project_raise`'s single-element version. -/

set_option maxHeartbeats 800000 in
/-- **The sign projection is additive.** Align the two fractions at a common denominator
(`exists_awayMk_pair`), where the projection is division of the numerator by a fixed monomial
(`signProjection_awayMk`), and division by a monomial is additive (`add_divMonomial`). -/
theorem signProjection_add [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0)
    (z₁ z₂ : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    signProjection h𝓜 hγ (z₁ + z₂) = signProjection h𝓜 hγ z₁ + signProjection h𝓜 hγ z₂ := by
  obtain ⟨m, p₁, p₂, hp₁, hp₂, rfl, rfl⟩ :=
    DegreeZeroLocalization.exists_awayMk_pair
      (monomial_one_mem_polynomialGrading (R := R) γ) (monomial_one_pow_ne_zero γ) z₁ z₂
  rw [← DegreeZeroLocalization.awayMk_add
      (monomial_one_mem_polynomialGrading (R := R) γ) m p₁ p₂ hp₁ hp₂,
    signProjection_awayMk h𝓜 hγ hγ', signProjection_awayMk h𝓜 hγ hγ',
    signProjection_awayMk h𝓜 hγ hγ',
    ← DegreeZeroLocalization.awayMk_add (monomial_one_mem_polynomialGrading (R := R) γ') m _ _
      (IsPolynomialTwist.divMonomial_mem h𝓜 hγ hp₁) (IsPolynomialTwist.divMonomial_mem h𝓜 hγ hp₂)]
  have hcongr : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • γ'.degree))
      (hb : b ∈ 𝓜 (m • γ'.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ') m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ') m b hb := by
    rintro a b ha hb rfl; rfl
  exact hcongr _ _ _ _ (MvPolynomial.add_divMonomial p₁ p₂ _)

/-- **The sign projection as an additive map.** The hypothesis `γ' i₀ = 0` is what additivity
costs — see `signProjection` — so the bundled form carries it. `map_zero` comes with the
bundling; callers should reach equations through `signProjectionHom_apply` and then
`signProjection_awayMk`. -/
noncomputable def signProjectionHom [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0) :
    DegreeZeroLocalization (polynomialGrading ι R)
        (𝓜)
        (.powers (MvPolynomial.monomial γ (1 : R))) →+
      DegreeZeroLocalization (polynomialGrading ι R)
        (𝓜)
        (.powers (MvPolynomial.monomial γ' (1 : R))) :=
  AddMonoidHom.mk' (signProjection h𝓜 hγ) (signProjection_add h𝓜 hγ hγ')

@[simp]
theorem signProjectionHom_apply [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' : ι →₀ ℕ} {i₀ : ι} {c : ℕ}
    (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    signProjectionHom h𝓜 hγ hγ' z = signProjection h𝓜 hγ z :=
  rfl

/-! ## The projection commutes with the remaining faces

`signProjection_laurentFace` handles the face that reinserts `X_{i₀}` itself — the `j = 0` face
of the homotopy, which the projection retracts. Every other face of the Čech complex multiplies
the denominator by a variable `X_e` that is **not** `X_{i₀}`, and for those the projection and
the face commute. That square is the second and last property #340's contracting homotopy
consumes.

The restriction of §1 of the proof plan — the square only holds on the summands with
`i₀ ∉ N α` — enters here as the hypothesis `δ' i₀ = 0`: the target denominator of the
projection on the face side must not invert `X_{i₀}`, which encodes both `e ≠ i₀` (or the face
is the retracted one) and the well-definedness hypothesis of each projection. The unrestricted
square with `e = i₀` is false, and no statement of it appears. -/

omit [AddSubgroupClass σM (MvPolynomial ι R)]
  [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] in
/-- Multiplying a numerator by `(X_e^{c'})ᵐ` raises its graded piece by `m·c'` and keeps the
twist. This is the membership fact the face side of the projection square feeds
`laurentFace_awayMk`, stated once because both columns of the square need it. -/
theorem monomial_single_pow_smul_mem (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ : ι →₀ ℕ} {e : ι} {c' : ℕ} {m : ℕ} {p : MvPolynomial ι R}
    (hp : p ∈ 𝓜 (m • γ.degree)) :
    (MvPolynomial.monomial (Finsupp.single e c') (1 : R)) ^ m • p ∈
      𝓜 (m • (c' + γ.degree)) := by
  have h1 : ((MvPolynomial.monomial (Finsupp.single e c') (1 : R)) ^ m).IsHomogeneous
      (m * c') := by
    rw [monomial_one_pow, Finsupp.smul_single, smul_eq_mul]
    exact MvPolynomial.isHomogeneous_monomial 1 (by rw [Finsupp.degree_single])
  rw [smul_eq_mul]
  exact IsPolynomialTwist.mul_mem_of_isHomogeneous h𝓜 h1 (by simp only [smul_eq_mul]; ring) hp

set_option maxHeartbeats 1200000 in
/-- **The projection square.** Away from the retracted face, the sign projection commutes with
the Čech face: restricting along `X_e` and then projecting out `X_{i₀}` is projecting first and
restricting after.

The four denominators are supplied as separate splittings because the caller — a Čech
differential — produces each of them separately and never has to take one apart. `hδ'₀`
(`δ' i₀ = 0`) is the restriction of §1 of #340's proof plan in hypothesis form: with `hγ'` it
forces `X_e ≠ X_{i₀}` unless `c' = 0`, which is exactly the disjointness
`divMonomial_monomial_mul_comm` needs to pull the face's monomial through the projection's
division. The unrestricted square at `e = i₀` is false — that face is the retraction
`signProjection_laurentFace`, not this square. -/
theorem signProjection_laurentFace_comm [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {γ γ' δ δ' : ι →₀ ℕ} {i₀ e : ι}
    {c c' : ℕ} (hγ : γ = Finsupp.single i₀ c + γ') (hγ' : γ' i₀ = 0)
    (hδγ : δ = Finsupp.single e c' + γ) (hδγ' : δ' = Finsupp.single e c' + γ')
    (hδsplit : δ = Finsupp.single i₀ c + δ') (hδ'₀ : δ' i₀ = 0)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    signProjection h𝓜 hδsplit (laurentFace 𝓜 hδγ z) =
      laurentFace 𝓜 hδγ' (signProjection h𝓜 hγ z) := by
  obtain ⟨m, p, hp, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := R) γ) (monomial_one_pow_ne_zero γ) z
  have hdegδ : δ.degree = c' + γ.degree := by rw [hδγ, map_add, Finsupp.degree_single]
  have hdegδ' : δ'.degree = c' + γ'.degree := by rw [hδγ', map_add, Finsupp.degree_single]
  have hres : (MvPolynomial.monomial (Finsupp.single e c') (1 : R)) ^ m • p ∈
      𝓜 (m • (c' + γ.degree)) :=
    monomial_single_pow_smul_mem h𝓜 hp
  have hresδ : (MvPolynomial.monomial (Finsupp.single e c') (1 : R)) ^ m • p ∈
      𝓜 (m • δ.degree) := by rw [hdegδ]; exact hres
  have hres' : (MvPolynomial.monomial (Finsupp.single e c') (1 : R)) ^ m •
      MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) ∈
      𝓜 (m • (c' + γ'.degree)) :=
    monomial_single_pow_smul_mem h𝓜 (IsPolynomialTwist.divMonomial_mem h𝓜 hγ hp)
  rw [laurentFace_awayMk hδγ hp hres,
    DegreeZeroLocalization.awayMk_deg_congr hdegδ.symm (monomial_mem_add_degree hδγ)
      (monomial_one_mem_polynomialGrading (R := R) δ) m _ hres hresδ,
    signProjection_awayMk h𝓜 hδsplit hδ'₀,
    signProjection_awayMk h𝓜 hγ hγ',
    laurentFace_awayMk hδγ' (IsPolynomialTwist.divMonomial_mem h𝓜 hγ hp) hres',
    DegreeZeroLocalization.awayMk_deg_congr hdegδ'.symm (monomial_mem_add_degree hδγ')
      (monomial_one_mem_polynomialGrading (R := R) δ') m _ hres'
      (by rw [hdegδ']; exact hres')]
  -- The face's monomial does not involve `i₀`: `δ' i₀ = 0` splits into `X_e`'s contribution
  -- and `γ'`'s, both zero.
  have hs : Finsupp.single e c' i₀ = 0 := by
    have happ := congrArg (fun v : ι →₀ ℕ => v i₀) hδγ'
    simp only [Finsupp.add_apply, hγ', add_zero] at happ
    rw [← happ]; exact hδ'₀
  have hdisj : ∀ j : ι,
      (Finsupp.single e (m * c')) j = 0 ∨ (Finsupp.single i₀ (m * c)) j = 0 := by
    classical
    intro j
    rcases eq_or_ne j i₀ with rfl | hj
    · left
      rw [Finsupp.single_apply] at hs ⊢
      split_ifs at hs ⊢ with he
      · rw [hs, Nat.mul_zero]
      · rfl
    · exact Or.inr (Finsupp.single_eq_of_ne hj)
  have hmono : (MvPolynomial.monomial (Finsupp.single e c') (1 : R)) ^ m =
      MvPolynomial.monomial (Finsupp.single e (m * c')) 1 := by
    rw [monomial_one_pow, Finsupp.smul_single, smul_eq_mul]
  have hnum : MvPolynomial.divMonomial
      ((MvPolynomial.monomial (Finsupp.single e c') (1 : R)) ^ m • p)
      (Finsupp.single i₀ (m * c)) =
      (MvPolynomial.monomial (Finsupp.single e c') (1 : R)) ^ m •
        MvPolynomial.divMonomial p (Finsupp.single i₀ (m * c)) := by
    rw [hmono, smul_eq_mul, smul_eq_mul, divMonomial_monomial_mul_comm hdisj]
  have hgen : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • δ'.degree))
      (hb : b ∈ 𝓜 (m • δ'.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) δ') m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) δ') m b hb := by
    rintro a b ha hb rfl; rfl
  exact hgen _ _ _ _ hnum

end AlgebraicGeometry.Proj
