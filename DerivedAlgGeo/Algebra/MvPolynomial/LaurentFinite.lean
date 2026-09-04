/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.MvPolynomial.LaurentBlock

/-!
# The base field acting on a homogeneous localization, and the finiteness of a full block

`LaurentBlock.lean` decomposes an away localization by the negative support of the Laurent
exponent and proves the combinatorial fact the top cohomology of `Pⁿ` rests on:
`finite_setOf_degree_eq_of_neg`, that only finitely many exponents are negative in *every*
variable at a fixed total degree. This file turns that count into a statement about the
localization itself.

## Why the base field has to appear

Everything in the Čech lane is valued in abelian groups, and "finitely many exponents" is not by
itself a finiteness statement about a group: the block is a `k`-vector space, and it is spanned —
not generated as an abelian group — by the corresponding monomial fractions. So the `k`-action
has to be named before the count can be used.

It is not extra data. A constant is a degree-zero homogeneous element, so `k` maps into every
homogeneous localization through `HomogeneousLocalization.fromZeroRingHom`, and
`degreeZeroLocalizationModule` is the restriction of scalars along that map. `awayMk_smul` is the
computation that makes it usable: scaling a fraction scales its numerator.

## The spanning argument

`blockProj_univ_mem_span` decomposes an arbitrary element into monomial fractions, filters to the
full block, strips each coefficient with `awayMk_smul`, and replaces each monomial fraction by
`blockRep` of its Laurent exponent. The replacement is what makes the spanning family *fixed*
rather than dependent on the element, and it is sound because the Laurent exponent is a complete
invariant (`awayMk_monomial_eq_iff_laurentExponent`).

## Scope

One localization. Assembling the blocks of a Čech cochain, and matching this action against the
`cechScalarAction` that `module_finite_linearCoherentH_of_cech` consumes, are separate and are not
done here.
-/

universe u

open Finsupp GradedModule

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k]

/-- The base field acts on every homogeneous localization of the polynomial ring, through the
constants — which are exactly the degree-zero part of the grading. -/
noncomputable def polynomialToHomogeneousLocalization (S : Submonoid (MvPolynomial ι k)) :
    k →+* HomogeneousLocalization (polynomialGrading ι k) S :=
  (HomogeneousLocalization.fromZeroRingHom (polynomialGrading ι k) S).comp
    (algebraMap k ↥(polynomialGrading ι k 0))

variable {σM : Type u} [SetLike σM (MvPolynomial ι k)]
  [AddSubgroupClass σM (MvPolynomial ι k)] (𝓜 : ℕ → σM)
  [SetLike.GradedSMul (polynomialGrading ι k) 𝓜]

/-- The base field acting on a degree-zero homogeneous localization, by restriction of scalars
along `polynomialToHomogeneousLocalization`. -/
noncomputable instance degreeZeroLocalizationModule (S : Submonoid (MvPolynomial ι k)) :
    Module k (DegreeZeroLocalization (polynomialGrading ι k) 𝓜 S) :=
  Module.compHom _ (polynomialToHomogeneousLocalization ι k S)

/-- **The base field acts on the numerator.** Scalar multiplication on a fraction `p / fⁿ` is
scalar multiplication on `p`, because a constant is a degree-zero homogeneous element with
denominator `1`. This is what lets a spanning argument strip coefficients off monomials. -/
theorem awayMk_smul {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d) {f : MvPolynomial ι k} {e : ℕ}
    (hf : f ∈ polynomialGrading ι k e) (n : ℕ) (c : k) (p : MvPolynomial ι k)
    (hp : p ∈ 𝓜 (n • e)) :
    c • DegreeZeroLocalization.awayMk (𝓜 := 𝓜) hf n p hp =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜) hf n (c • p) (h𝓜.smul_mem c hp) := by
  apply DegreeZeroLocalization.ext
  show ((polynomialToHomogeneousLocalization ι k (.powers f) c •
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜) hf n p hp :
        DegreeZeroLocalization (polynomialGrading ι k) 𝓜 (.powers f)) :
      LocalizedModule (Submonoid.powers f) (MvPolynomial ι k)) = _
  rw [DegreeZeroLocalization.coe_smul, DegreeZeroLocalization.coe_awayMk,
    DegreeZeroLocalization.coe_awayMk]
  have hval : (polynomialToHomogeneousLocalization ι k (Submonoid.powers f) c).val =
      Localization.mk (MvPolynomial.C c) 1 := by
    show (HomogeneousLocalization.mk _).val = _
    rw [HomogeneousLocalization.val_mk]
    rfl
  show (polynomialToHomogeneousLocalization ι k (Submonoid.powers f) c).val •
      LocalizedModule.mk p (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) = _
  rw [hval, LocalizedModule.mk_smul_mk, one_mul]
  congr 1
  exact (MvPolynomial.smul_eq_C_mul p c).symm

/-! ## The full block is finitely spanned -/

/-- Numerator congruence for `awayMk`, so a rewrite under the membership certificate does not
have to fight a non-type-correct motive. -/
theorem awayMk_congr {f : MvPolynomial ι k} {e : ℕ} (hf : f ∈ polynomialGrading ι k e) (n : ℕ)
    {p q : MvPolynomial ι k} (hp : p ∈ 𝓜 (n • e)) (hq : q ∈ 𝓜 (n • e)) (h : p = q) :
    DegreeZeroLocalization.awayMk (𝓜 := 𝓜) hf n p hp =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜) hf n q hq := by
  subst h; rfl

omit [AddSubgroupClass σM (MvPolynomial ι k)]
  [SetLike.GradedSMul (polynomialGrading ι k) 𝓜] in
/-- Every monomial of a numerator is itself a numerator with coefficient one: the coefficient
plays no part in the degree bookkeeping. -/
theorem monomial_one_mem_of_mem_support {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d) {n : ℕ}
    {q : MvPolynomial ι k} (hq : q ∈ 𝓜 n) {β : ι →₀ ℕ} (hβ : β ∈ q.support) :
    MvPolynomial.monomial β (1 : k) ∈ 𝓜 n :=
  (h𝓜 n _).mpr (Or.inr ⟨β.degree, h𝓜.degree_eq_of_mem_support hq hβ,
    MvPolynomial.isHomogeneous_monomial 1 rfl⟩)

/-- A monomial surviving the filter has the filtered block as its negative support. -/
theorem intNegSupport_of_mem_support_laurentFilter (γ : ι →₀ ℕ) (m : ℕ) (F : Finset ι)
    (p : MvPolynomial ι k) {β : ι →₀ ℕ} (hβ : β ∈ (laurentFilter γ m F p).support) :
    intNegSupport (laurentExponent γ m β) = F := by
  by_contra hne
  exact (MvPolynomial.mem_support_iff.mp hβ) (coeff_laurentFilter_of_ne hne p)

open Classical in
/-- A monomial fraction with a prescribed Laurent exponent, chosen once and for all.

Every monomial fraction with that exponent equals it, so a spanning argument can name a *fixed*
finite family instead of one depending on the element being decomposed. -/
noncomputable def blockRep (γ : ι →₀ ℕ) (α : ι →₀ ℤ) :
    DegreeZeroLocalization (polynomialGrading ι k) 𝓜
      (.powers (MvPolynomial.monomial γ (1 : k))) :=
  if h : ∃ mb : ℕ × (ι →₀ ℕ),
      (MvPolynomial.monomial mb.2 (1 : k) ∈ 𝓜 (mb.1 • γ.degree)) ∧
        laurentExponent γ mb.1 mb.2 = α then
    DegreeZeroLocalization.awayMk (𝓜 := 𝓜) (monomial_one_mem_polynomialGrading (R := k) γ)
      h.choose.1 (MvPolynomial.monomial h.choose.2 1) h.choose_spec.1
  else 0

/-- **The Laurent exponent selects the representative.** A monomial fraction is the chosen
representative of its own exponent — `awayMk_monomial_eq_iff_laurentExponent` is what makes the
choice harmless. -/
theorem awayMk_eq_blockRep (γ : ι →₀ ℕ) {m : ℕ} {β : ι →₀ ℕ}
    (h : MvPolynomial.monomial β (1 : k) ∈ 𝓜 (m • γ.degree)) :
    DegreeZeroLocalization.awayMk (𝓜 := 𝓜) (monomial_one_mem_polynomialGrading (R := k) γ) m
        (MvPolynomial.monomial β 1) h =
      blockRep ι k 𝓜 γ (laurentExponent γ m β) := by
  classical
  have hex : ∃ mb : ℕ × (ι →₀ ℕ),
      (MvPolynomial.monomial mb.2 (1 : k) ∈ 𝓜 (mb.1 • γ.degree)) ∧
        laurentExponent γ mb.1 mb.2 = laurentExponent γ m β := ⟨(m, β), h, rfl⟩
  rw [blockRep, dif_pos hex]
  exact (awayMk_monomial_eq_iff_laurentExponent γ h hex.choose_spec.1).mpr
    hex.choose_spec.2.symm

/-- **The full block lies in the span of a fixed family indexed by a finite exponent set.**

Decompose into monomial fractions, filter to the full block, strip each coefficient with
`awayMk_smul`, and replace each monomial fraction by the representative of its exponent. What
survives is indexed by exponents that are negative in every variable and of total degree `d` —
the set `finite_setOf_degree_eq_of_neg` shows is finite. -/
theorem blockProj_univ_mem_span [Fintype ι] {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d) (γ : ι →₀ ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι k) 𝓜
      (.powers (MvPolynomial.monomial γ (1 : k)))) :
    blockProj h𝓜 γ Finset.univ z ∈
      Submodule.span k (blockRep ι k 𝓜 γ ''
        {α : ι →₀ ℤ | α.degree = d ∧ ∀ j : ι, α j < 0}) := by
  classical
  obtain ⟨m, p, hp, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := k) γ) (monomial_one_pow_ne_zero γ) z
  have hfilt := IsPolynomialTwist.laurentFilter_mem h𝓜 (F := Finset.univ) (γ := γ) (m := m) hp
  rw [blockProj_awayMk h𝓜 γ Finset.univ hp, awayMk_eq_sum_monomial h𝓜 γ _ hfilt]
  refine Submodule.sum_mem _ fun β hβ => ?_
  have hmem1 : MvPolynomial.monomial β (1 : k) ∈ 𝓜 (m • γ.degree) :=
    monomial_one_mem_of_mem_support ι k 𝓜 h𝓜 hfilt hβ
  have hcoeff : DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := k) γ) m
        (MvPolynomial.monomial β ((laurentFilter γ m Finset.univ p).coeff β))
        (h𝓜.monomial_coeff_mem hfilt β) =
      ((laurentFilter γ m Finset.univ p).coeff β) • blockRep ι k 𝓜 γ (laurentExponent γ m β) := by
    rw [← awayMk_eq_blockRep ι k 𝓜 γ hmem1,
      awayMk_smul ι k 𝓜 h𝓜 (monomial_one_mem_polynomialGrading (R := k) γ) m _ _ hmem1]
    exact awayMk_congr ι k 𝓜 _ _ _ _
      (by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one])
  rw [hcoeff]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨laurentExponent γ m β, ⟨?_, ?_⟩, rfl⟩)
  · exact h𝓜.degree_laurentExponent_of_mem_support hfilt hβ
  · intro j
    exact mem_intNegSupport.mp
      (by rw [intNegSupport_of_mem_support_laurentFilter ι k γ m Finset.univ p hβ]
          exact Finset.mem_univ j)

/-- **The full block of one localization is a finite-dimensional `k`-space.**

`finite_setOf_degree_eq_of_neg` bounds the exponents that can appear — every coordinate negative
with a fixed total — and `blockProj_univ_mem_span` says nothing outside that family is needed. -/
theorem fg_blockSpan [Fintype ι] {d : ℤ} (γ : ι →₀ ℕ) :
    (Submodule.span k (blockRep ι k 𝓜 γ ''
      {α : ι →₀ ℤ | α.degree = d ∧ ∀ j : ι, α j < 0})).FG :=
  Submodule.fg_span ((finite_setOf_degree_eq_of_neg d).image _)

/-- **Scaling a fraction scales its numerator**, at a general homogeneous denominator. The
`awayMk` form is the special case the spanning argument uses; this is the one the section
comparison needs, where the denominator is not a power. -/
theorem smul_mk {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d) (S : Submonoid (MvPolynomial ι k))
    (c : NumDenSameDeg (polynomialGrading ι k) 𝓜 S) (r : k) :
    r • DegreeZeroLocalization.mk c =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := ⟨r • (c.num : MvPolynomial ι k), h𝓜.smul_mem r c.num.2⟩
          den := c.den
          den_mem := c.den_mem } := by
  apply DegreeZeroLocalization.ext
  have hval : (polynomialToHomogeneousLocalization ι k S r).val =
      Localization.mk (MvPolynomial.C r) 1 := by
    show (HomogeneousLocalization.mk _).val = _
    rw [HomogeneousLocalization.val_mk]
    rfl
  show (polynomialToHomogeneousLocalization ι k S r).val •
      LocalizedModule.mk (c.num : MvPolynomial ι k) ⟨(c.den : MvPolynomial ι k), c.den_mem⟩ = _
  rw [hval, LocalizedModule.mk_smul_mk, one_mul]
  congr 1
  exact (MvPolynomial.smul_eq_C_mul _ r).symm

/-- **Enlarging the denominator submonoid is `k`-linear.** Both sides are the same fraction with
the same numerator scaled; `mapOfLE_mk` makes that visible. -/
theorem mapOfLE_smul {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d)
    {S T : Submonoid (MvPolynomial ι k)} (h : S ≤ T) (r : k)
    (z : DegreeZeroLocalization (polynomialGrading ι k) 𝓜 S) :
    DegreeZeroLocalization.mapOfLE (𝒜 := polynomialGrading ι k) (𝓜 := 𝓜) h (r • z) =
      r • DegreeZeroLocalization.mapOfLE (𝒜 := polynomialGrading ι k) (𝓜 := 𝓜) h z := by
  obtain ⟨c, rfl⟩ := DegreeZeroLocalization.mk_surjective z
  rw [smul_mk ι k 𝓜 h𝓜, DegreeZeroLocalization.mapOfLE_mk,
    DegreeZeroLocalization.mapOfLE_mk, smul_mk ι k 𝓜 h𝓜]

end MvPolynomial
