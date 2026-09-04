/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.MvPolynomial.LaurentBlock

/-!
# The contracting homotopy of a block, one localization at a time

Step 3 of #340's proof plan contracts each block `C_F` of the Čech complex through a cone point
`i₀ ∉ F`: the homotopy sends a cochain `s` to `y ↦ Π (s (i₀ :: y))`, where `Π` restricts a
fraction from the denominator of `i₀ :: y` back to the denominator of `y`. This file supplies
`Π` — here `laurentHomotopy` — and the two identities the homotopy computation
`d ∘ h + h ∘ d = id` consumes, at the level of one localization.

## The definition, and why it is a composite

The denominator of `i₀ :: y` is `X_{i₀} · Xᵞ` with `γ` the denominator exponent of `y` — but
`γ` may itself contain `i₀` (the tuple `y` may mention the cone point), and the sign
projection's defining equations require a target free of `i₀`. So `Π` projects out **all** of
`X_{i₀}` first and then reinserts the surplus:

```
Π = laurentFace (γ = X_{i₀}^t · γ'')  ∘  signProjection (X_{i₀}·Xᵞ = X_{i₀}^{1+t} · γ'')
```

with `t = γ i₀` and `γ'' = γ.erase i₀`. Both constituents are pinned by their `awayMk`
equations, so `Π` is well defined and additive with no new descent argument, and
`laurentHomotopy_awayMk` is the equation everything else runs on. When `t = 0` the reinserted
face is multiplication by `X_{i₀}^0 = 1` and `Π` is the plain sign projection.

## The two identities

* `laurentHomotopy_laurentFace_comm` — **`Π` commutes with every face**, with no restriction:
  not only the faces in a variable `e ≠ i₀` (where it reduces to the projection square of
  #539), but also the faces in `i₀` itself, where the surplus exponent `t` shifts by one and
  the reinserted power rebalances exactly. This unrestricted square is what the composite
  definition buys; the bare sign projection satisfies no such identity.
* `laurentHomotopy_laurentFace_blockProj` — **`Π` retracts the cone face on the block**: for
  `i₀ ∉ F`, applying the front face `X_{i₀}` and then `Π` is the identity on block-`F`
  elements. This is the only place the block hypothesis enters, and it is genuinely needed:
  on a block with `α i₀ < 0` the projection half of `Π` kills terms the face half cannot
  restore.

In the homotopy computation these two are the whole story: the `j = 0` face of `i₀ :: y`
produces the identity through the retraction, and every other face cancels between
`d (h s)` and `h (d s)` through the square.

## Tags

contracting homotopy, Čech complex, homogeneous localization, graded module
-/

open Finsupp GradedModule

namespace MvPolynomial

universe u

variable {ι R : Type u} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Numerator-level cancellation -/

/-- A monomial divided out of a polynomial that it wholly divides is restored by multiplying it
back. The support hypothesis cannot be dropped: on a term not divisible by `Xˢ` the division
truncates and the multiplication cannot restore it. In the retraction below the hypothesis is
supplied by the block structure — on block `F` with `i₀ ∉ F` every term carries at least
`X_{i₀}^{m·t}`. -/
theorem monomial_mul_divMonomial_cancel {s : ι →₀ ℕ} {q : MvPolynomial ι R}
    (h : ∀ β ∈ q.support, s ≤ β) :
    MvPolynomial.monomial s 1 * MvPolynomial.divMonomial q s = q := by
  ext β
  rw [MvPolynomial.coeff_monomial_mul']
  by_cases hle : s ≤ β
  · rw [if_pos hle, one_mul, MvPolynomial.coeff_divMonomial]
    congr 1
    ext j
    have hj := Finsupp.le_def.mp hle j
    simp only [Finsupp.add_apply, Finsupp.tsub_apply]
    omega
  · rw [if_neg hle]
    exact (MvPolynomial.notMem_support_iff.mp fun hs => hle (h β hs)).symm

/-- On block `F` with `i₀ ∉ F`, every numerator term carries at least the denominator's power
of `X_{i₀}`: the Laurent exponent at `i₀` is nonnegative, so `β i₀ ≥ m · γ i₀`. This is the
support bound that feeds `monomial_mul_divMonomial_cancel` in the retraction. -/
theorem laurentFilter_apply_ge {γ : ι →₀ ℕ} {F : Finset ι} {i₀ : ι} (hi₀ : i₀ ∉ F)
    (m : ℕ) (p : MvPolynomial ι R) {β : ι →₀ ℕ}
    (hβ : β ∈ (laurentFilter γ m F p).support) : m * γ i₀ ≤ β i₀ := by
  have hcoeff := MvPolynomial.mem_support_iff.mp hβ
  by_cases hN : intNegSupport (laurentExponent γ m β) = F
  · have hneg : ¬ laurentExponent γ m β i₀ < 0 := fun hlt =>
      hi₀ (hN ▸ mem_intNegSupport.mpr hlt)
    rw [laurentExponent_apply] at hneg
    have h0 : (0 : ℤ) ≤ (β i₀ : ℤ) - m * γ i₀ := by omega
    have := sub_nonneg.mp h0
    exact_mod_cast this
  · exact absurd (coeff_laurentFilter_of_ne hN p) hcoeff

/-! ## The homotopy map -/

variable {σM : Type u} [SetLike σM (MvPolynomial ι R)]
  [AddSubgroupClass σM (MvPolynomial ι R)] {𝓜 : ℕ → σM}
  [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] {d : ℤ}


/-- The full splitting of the cone denominator: `X_{i₀} · Xᵞ = X_{i₀}^{1+γ(i₀)} · Xᵞ''` with
`γ'' = γ.erase i₀`. This is the splitting the projection half of the homotopy uses; unlike the
naive `c = 1` splitting it leaves a target free of `i₀`, so the projection's equations apply
whatever the tuple `y` contains. -/
theorem laurentHomotopy_split (i₀ : ι) (γ : ι →₀ ℕ) :
    Finsupp.single i₀ 1 + γ = Finsupp.single i₀ (1 + γ i₀) + γ.erase i₀ := by
  conv_lhs => rw [← Finsupp.single_add_erase i₀ γ]
  rw [← add_assoc, ← Finsupp.single_add]

/-- The reinsertion splitting: `Xᵞ = X_{i₀}^{γ(i₀)} · Xᵞ''`. The face at this splitting puts
back the surplus power of `X_{i₀}` that the full projection removed beyond the cone factor. -/
theorem laurentHomotopy_back (i₀ : ι) (γ : ι →₀ ℕ) :
    γ = Finsupp.single i₀ (γ i₀) + γ.erase i₀ :=
  (Finsupp.single_add_erase i₀ γ).symm

/-- **The homotopy map** `Π : (A(d)_{X_{i₀}·Xᵞ})₀ → (A(d)_{Xᵞ})₀`: project out all of
`X_{i₀}`, then reinsert the surplus `X_{i₀}^{γ(i₀)}` by a face. A composite of two maps that
are already well defined and additive, so it is both, with no new descent argument. Callers
use `laurentHomotopy_awayMk`. -/
noncomputable def laurentHomotopy [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (i₀ : ι)
    (γ : ι →₀ ℕ) :
    DegreeZeroLocalization (polynomialGrading ι R)
        (𝓜)
        (.powers (MvPolynomial.monomial (Finsupp.single i₀ 1 + γ) (1 : R))) →+
      DegreeZeroLocalization (polynomialGrading ι R)
        (𝓜)
        (.powers (MvPolynomial.monomial γ (1 : R))) :=
  (laurentFace 𝓜 (laurentHomotopy_back i₀ γ)).comp
    (signProjectionHom h𝓜 (laurentHomotopy_split i₀ γ) Finsupp.erase_same)

omit [AddSubgroupClass σM (MvPolynomial ι R)]
  [SetLike.GradedSMul (polynomialGrading ι R) 𝓜] in
/-- The numerator produced by the homotopy map is a legitimate numerator for `Xᵞ`. -/
theorem laurentHomotopy_numerator_mem (h𝓜 : IsPolynomialTwist 𝓜 d) (i₀ : ι) (γ : ι →₀ ℕ)
    {m : ℕ}
    {q : MvPolynomial ι R}
    (hq : q ∈ 𝓜
      (m • (Finsupp.single i₀ 1 + γ).degree)) :
    (MvPolynomial.monomial (Finsupp.single i₀ (γ i₀)) (1 : R)) ^ m •
      MvPolynomial.divMonomial q (Finsupp.single i₀ (m * (1 + γ i₀))) ∈
      𝓜 (m • γ.degree) := by
  have hdeg : γ.degree = γ i₀ + (γ.erase i₀).degree := by
    conv_lhs => rw [← Finsupp.single_add_erase i₀ γ]
    rw [map_add, Finsupp.degree_single]
  have h1 := IsPolynomialTwist.divMonomial_mem h𝓜 (laurentHomotopy_split i₀ γ) hq
  have h2 := monomial_single_pow_smul_mem h𝓜 (e := i₀) (c' := γ i₀) h1
  rwa [← hdeg] at h2

set_option maxHeartbeats 1200000 in
/-- **The defining equation of the homotopy map**: on `q / (X_{i₀}·Xᵞ)ᵐ` it divides the
numerator by `X_{i₀}^{m(1+γ(i₀))}` and multiplies `X_{i₀}^{m·γ(i₀)}` back in. -/
theorem laurentHomotopy_awayMk [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d) (i₀ : ι)
    (γ : ι →₀ ℕ) {m : ℕ}
    {q : MvPolynomial ι R}
    (hq : q ∈ 𝓜
      (m • (Finsupp.single i₀ 1 + γ).degree)) :
    laurentHomotopy h𝓜 i₀ γ
        (DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) (Finsupp.single i₀ 1 + γ)) m q hq) =
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
        (monomial_one_mem_polynomialGrading (R := R) γ) m
        ((MvPolynomial.monomial (Finsupp.single i₀ (γ i₀)) (1 : R)) ^ m •
          MvPolynomial.divMonomial q (Finsupp.single i₀ (m * (1 + γ i₀))))
        (laurentHomotopy_numerator_mem h𝓜 i₀ γ hq) := by
  have hdeg : γ.degree = γ i₀ + (γ.erase i₀).degree := by
    conv_lhs => rw [← Finsupp.single_add_erase i₀ γ]
    rw [map_add, Finsupp.degree_single]
  have h1 := IsPolynomialTwist.divMonomial_mem h𝓜 (laurentHomotopy_split i₀ γ) hq
  have hres := monomial_single_pow_smul_mem h𝓜 (e := i₀) (c' := γ i₀) h1
  rw [laurentHomotopy, AddMonoidHom.comp_apply, signProjectionHom_apply,
    signProjection_awayMk h𝓜 (laurentHomotopy_split i₀ γ) Finsupp.erase_same,
    laurentFace_awayMk (laurentHomotopy_back i₀ γ) h1 hres,
    DegreeZeroLocalization.awayMk_deg_congr hdeg.symm
      (monomial_mem_add_degree (laurentHomotopy_back i₀ γ))
      (monomial_one_mem_polynomialGrading (R := R) γ) m _ hres
      (laurentHomotopy_numerator_mem h𝓜 i₀ γ hq)]

/-! ## The retraction on a block -/

set_option maxHeartbeats 1200000 in
/-- **`Π` retracts the cone face on the block.** For `i₀ ∉ F`, restricting a block-`F` element
along the cone face `X_{i₀}` and then applying the homotopy map gives it back.

The front face multiplies the numerator by `X_{i₀}^m`; the projection half of `Π` divides by
`X_{i₀}^{m(1+t)}`, which eats the face's factor and `X_{i₀}^{m·t}` more; the reinsertion
restores that surplus — and restoring is exact precisely because on block `F` with `i₀ ∉ F`
every term had `β i₀ ≥ m·t` to give (`laurentFilter_apply_ge`). This is the only identity in
the homotopy that sees the block. -/
theorem laurentHomotopy_laurentFace_blockProj [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    {i₀ : ι} {F : Finset ι} (hi₀ : i₀ ∉ F) (γ : ι →₀ ℕ)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜) (.powers (MvPolynomial.monomial γ (1 : R)))) :
    laurentHomotopy h𝓜 i₀ γ
        (laurentFace 𝓜 (rfl : Finsupp.single i₀ 1 + γ = Finsupp.single i₀ 1 + γ)
          (blockProj h𝓜 γ F z)) =
      blockProj h𝓜 γ F z := by
  obtain ⟨m, q₀, hq₀, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := R) γ) (monomial_one_pow_ne_zero γ) z
  rw [blockProj_awayMk h𝓜 γ F]
  have hq : laurentFilter γ m F q₀ ∈
      𝓜 (m • γ.degree) :=
    IsPolynomialTwist.laurentFilter_mem h𝓜 hq₀
  have hdeg : (Finsupp.single i₀ 1 + γ).degree = 1 + γ.degree := by
    rw [map_add, Finsupp.degree_single]
  have hres := monomial_single_pow_smul_mem h𝓜 (e := i₀) (c' := 1) hq
  have hres' : (MvPolynomial.monomial (Finsupp.single i₀ 1) (1 : R)) ^ m •
      laurentFilter γ m F q₀ ∈
      𝓜 (m • (Finsupp.single i₀ 1 + γ).degree) := by
    rw [hdeg]; exact hres
  rw [laurentFace_awayMk rfl hq hres,
    DegreeZeroLocalization.awayMk_deg_congr hdeg.symm (monomial_mem_add_degree rfl)
      (monomial_one_mem_polynomialGrading (R := R) (Finsupp.single i₀ 1 + γ)) m _ hres hres',
    laurentHomotopy_awayMk h𝓜 i₀ γ hres']
  -- The numerator: the division eats the face's `X_{i₀}^m` and `X_{i₀}^{m·t}` more, and the
  -- reinsertion restores the surplus exactly, by the block's support bound.
  have hnum : (MvPolynomial.monomial (Finsupp.single i₀ (γ i₀)) (1 : R)) ^ m •
      MvPolynomial.divMonomial
        ((MvPolynomial.monomial (Finsupp.single i₀ 1) (1 : R)) ^ m •
          laurentFilter γ m F q₀)
        (Finsupp.single i₀ (m * (1 + γ i₀))) =
      laurentFilter γ m F q₀ := by
    have hsplit : Finsupp.single i₀ (m * (1 + γ i₀)) =
        Finsupp.single i₀ m + Finsupp.single i₀ (m * γ i₀) := by
      rw [← Finsupp.single_add]
      congr 1
      ring
    simp only [monomial_one_pow, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsplit, divMonomial_monomial_mul_add]
    exact monomial_mul_divMonomial_cancel fun β hβ =>
      Finsupp.single_le_iff.mpr (laurentFilter_apply_ge hi₀ m q₀ hβ)
  have hgen : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜 (m • γ.degree))
      (hb : b ∈ 𝓜 (m • γ.degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) γ) m b hb := by
    rintro a b ha hb rfl; rfl
  exact hgen _ _ _ _ hnum

/-! ## The square with every other face -/

set_option maxHeartbeats 1600000 in
/-- **`Π` commutes with every face — no restriction.** For a face in a variable `e ≠ i₀` this
is the projection square of #539 conjugated by the reinsertion; for `e = i₀` the surplus
exponent shifts by one on the left and the reinserted power grows to match on the right, and
the two sides agree exactly. The composite definition of `Π` is what makes the `e = i₀` case
true — the bare sign projection satisfies no unrestricted square.

The two splittings are hypotheses in the lane's usual style; both are associativity-and-
commutativity rearrangements the Čech caller has in hand. -/
theorem laurentHomotopy_laurentFace_comm [IsDomain R] (h𝓜 : IsPolynomialTwist 𝓜 d)
    (i₀ e : ι) (γ₀ : ι →₀ ℕ)
    (htop : Finsupp.single i₀ 1 + (γ₀ + Finsupp.single e 1) =
      Finsupp.single e 1 + (Finsupp.single i₀ 1 + γ₀))
    (hbot : γ₀ + Finsupp.single e 1 = Finsupp.single e 1 + γ₀)
    (z : DegreeZeroLocalization (polynomialGrading ι R)
      (𝓜)
      (.powers (MvPolynomial.monomial (Finsupp.single i₀ 1 + γ₀) (1 : R)))) :
    laurentHomotopy h𝓜 i₀ (γ₀ + Finsupp.single e 1) (laurentFace 𝓜 htop z) =
      laurentFace 𝓜 hbot (laurentHomotopy h𝓜 i₀ γ₀ z) := by
  obtain ⟨m, q, hq, rfl⟩ := DegreeZeroLocalization.exists_awayMk
    (monomial_one_mem_polynomialGrading (R := R) (Finsupp.single i₀ 1 + γ₀))
    (monomial_one_pow_ne_zero _) z
  -- Left side: face up to the enlarged cone denominator, then the homotopy map.
  have hdegtop : (Finsupp.single i₀ 1 + (γ₀ + Finsupp.single e 1)).degree =
      1 + (Finsupp.single i₀ 1 + γ₀).degree := by
    rw [htop, map_add, Finsupp.degree_single]
  have hrestop := monomial_single_pow_smul_mem h𝓜 (e := e) (c' := 1) hq
  have hrestop' : (MvPolynomial.monomial (Finsupp.single e 1) (1 : R)) ^ m • q ∈
      𝓜
        (m • (Finsupp.single i₀ 1 + (γ₀ + Finsupp.single e 1)).degree) := by
    rw [hdegtop]; exact hrestop
  -- Right side: the homotopy map, then the face up to the enlarged plain denominator.
  have hdegbot : (γ₀ + Finsupp.single e 1).degree = 1 + γ₀.degree := by
    rw [hbot, map_add, Finsupp.degree_single]
  have hresbot :=
    monomial_single_pow_smul_mem h𝓜 (e := e) (c' := 1) (laurentHomotopy_numerator_mem h𝓜 i₀ γ₀ hq)
  have hresbot' : (MvPolynomial.monomial (Finsupp.single e 1) (1 : R)) ^ m •
      ((MvPolynomial.monomial (Finsupp.single i₀ (γ₀ i₀)) (1 : R)) ^ m •
        MvPolynomial.divMonomial q (Finsupp.single i₀ (m * (1 + γ₀ i₀)))) ∈
      𝓜 (m • (γ₀ + Finsupp.single e 1).degree) := by
    rw [hdegbot]; exact hresbot
  rw [laurentFace_awayMk htop hq hrestop,
    DegreeZeroLocalization.awayMk_deg_congr hdegtop.symm (monomial_mem_add_degree htop)
      (monomial_one_mem_polynomialGrading (R := R)
        (Finsupp.single i₀ 1 + (γ₀ + Finsupp.single e 1))) m _ hrestop hrestop',
    laurentHomotopy_awayMk h𝓜 i₀ (γ₀ + Finsupp.single e 1) hrestop',
    laurentHomotopy_awayMk h𝓜 i₀ γ₀ hq,
    laurentFace_awayMk hbot (laurentHomotopy_numerator_mem h𝓜 i₀ γ₀ hq) hresbot,
    DegreeZeroLocalization.awayMk_deg_congr hdegbot.symm (monomial_mem_add_degree hbot)
      (monomial_one_mem_polynomialGrading (R := R) (γ₀ + Finsupp.single e 1)) m _
      hresbot hresbot']
  -- Everything is now a single `awayMk` on each side; the content is the numerator identity.
  have hnum : (MvPolynomial.monomial
        (Finsupp.single i₀ ((γ₀ + Finsupp.single e 1 : ι →₀ ℕ) i₀)) (1 : R)) ^ m •
      MvPolynomial.divMonomial
        ((MvPolynomial.monomial (Finsupp.single e 1) (1 : R)) ^ m • q)
        (Finsupp.single i₀ (m * (1 + (γ₀ + Finsupp.single e 1 : ι →₀ ℕ) i₀))) =
      (MvPolynomial.monomial (Finsupp.single e 1) (1 : R)) ^ m •
        ((MvPolynomial.monomial (Finsupp.single i₀ (γ₀ i₀)) (1 : R)) ^ m •
          MvPolynomial.divMonomial q (Finsupp.single i₀ (m * (1 + γ₀ i₀)))) := by
    simp only [monomial_one_pow, Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases he : e = i₀
    · -- The face is in the cone variable: the surplus shifts by one and rebalances.
      subst he
      have happ : (γ₀ + Finsupp.single e 1 : ι →₀ ℕ) e = γ₀ e + 1 := by simp
      rw [happ]
      have hsplit : Finsupp.single e (m * (1 + (γ₀ e + 1))) =
          Finsupp.single e m + Finsupp.single e (m * (1 + γ₀ e)) := by
        rw [← Finsupp.single_add]
        congr 1
        ring
      rw [hsplit, divMonomial_monomial_mul_add, ← mul_assoc,
        MvPolynomial.monomial_mul, ← Finsupp.single_add, one_mul,
        show m + m * γ₀ e = m * (γ₀ e + 1) from by ring]
    · -- The face is in another variable: the #539 disjointness pulls it through.
      have happ : (γ₀ + Finsupp.single e 1 : ι →₀ ℕ) i₀ = γ₀ i₀ := by
        simp [he]
      rw [happ]
      have hdisj : ∀ j : ι, (Finsupp.single e m) j = 0 ∨
          (Finsupp.single i₀ (m * (1 + γ₀ i₀))) j = 0 := by
        intro j
        rcases eq_or_ne j i₀ with rfl | hj
        · exact Or.inl (Finsupp.single_eq_of_ne (Ne.symm he))
        · exact Or.inr (Finsupp.single_eq_of_ne hj)
      rw [divMonomial_monomial_mul_comm hdisj, mul_left_comm]
  have hgen : ∀ (a b : MvPolynomial ι R)
      (ha : a ∈ 𝓜
        (m • (γ₀ + Finsupp.single e 1).degree))
      (hb : b ∈ 𝓜
        (m • (γ₀ + Finsupp.single e 1).degree)), a = b →
      DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) (γ₀ + Finsupp.single e 1)) m a ha =
        DegreeZeroLocalization.awayMk (𝓜 := 𝓜)
          (monomial_one_mem_polynomialGrading (R := R) (γ₀ + Finsupp.single e 1)) m b hb := by
    rintro a b ha hb rfl; rfl
  exact hgen _ _ _ _ hnum

end MvPolynomial
