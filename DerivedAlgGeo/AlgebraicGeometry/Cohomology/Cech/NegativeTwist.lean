/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.Vanishing

/-!
# `H⁰(Pⁿ, O(d)) = 0` for a negative twist

The degree-zero end of the integer-twist computation. `Cech/Vanishing.lean` closes the middle
degrees at either sign; this file closes the bottom one at `d < 0`.

## The argument

`H⁰` of the Čech complex is the kernel of `d⁰`, and unfolding the differential at `n = 0` says a
cocycle is a family `(sᵢ)` of degree-`d` fractions on the variable charts agreeing on every
overlap. Fixing `i` and choosing any `j ≠ i`, the overlap condition clears denominators to

```
X_j ^ b * p = X_i ^ a * q
```

with `p` the numerator of `sᵢ`. `X_i` and `X_j` are distinct variables, hence coprime, so
`X_pow_dvd_of_cross_mul` extracts `X_i ^ a ∣ p`. The numerator of a degree-`d` fraction with
denominator `X_i ^ a` is homogeneous of degree `a + d`, and at `d < 0` that is *smaller* than `a`
— so a nonzero `p` would be a multiple of `X_i ^ a` of degree below `a`, which cannot happen.
Hence `p = 0`, hence `sᵢ = 0`.

## Where the sign enters, and where it does not

Only in the last step. Everything before it is the two-chart argument that
`polynomialToNatGlobalSections_surjective` runs for `d : ℕ`, and it is insensitive to the sign;
what changes is the conclusion drawn at the end, which for `d ≥ 0` produces a representing
polynomial and for `d < 0` produces `0`.

The sign is spent in a single inequality. A fraction with denominator `X_i ^ a` has numerator
homogeneous of degree `a + d`, so `d < 0` reads `a + d < a`, and
`eq_zero_of_X_pow_dvd_of_isHomogeneous_of_lt` closes.

`intShiftPiece_eq_bot_of_neg` states the neighbouring fact — `intShift` is `ℕ`-indexed, so a piece
whose degree `n + d` is negative is trivial outright — and is deliberately *not* on that path: the
cross equation kills the numerator while its degree is still a natural number. It is what makes the
`ℕ`-indexing of `intShift` legible, and nothing below depends on it.

## Scope

The **abelian-group** statement, per #665. The `k`-vector-space structure that
`FiniteDimensionalCohomology.finite` asks for is separate, and the comparison `AddEquiv` is not
assumed `k`-linear anywhere here.

`Nontrivial ι` is needed and is not cosmetic: with a single variable there is no second chart, the
overlap condition is vacuous, and the statement is false — `P⁰` is a point and `O(d)` is free on
it. `Fintype ι` is *not* needed; the argument uses two charts, never all of them.
-/

universe u

open CategoryTheory TopologicalSpace

open GradedModule MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k]

/-! ### The two arithmetic facts

Both are about the polynomial ring and its shifted grading, with no localization and no Čech
complex in sight. They are separated out because each is the whole content of one step above. -/

/-- **A shifted graded piece below degree zero is trivial.**

`intShift` is `ℕ`-indexed and `intShiftPiece 𝓜 d n` asks for an element of degree `n + d`. When
that is negative no natural number witnesses it, so only `0` remains. This is the single place the
sign of `d` is used in this file. -/
theorem intShiftPiece_eq_bot_of_neg {M σM : Type u} [AddCommGroup M]
    [SetLike σM M] [AddSubgroupClass σM M] (𝓜 : ℕ → σM) (d : ℤ) (n : ℕ)
    (hn : (n : ℤ) + d < 0) :
    intShiftPiece 𝓜 d n = ⊥ := by
  ext m
  simp only [AddSubgroup.mem_bot]
  constructor
  · rintro (h0 | ⟨j, hj, -⟩)
    · exact h0
    · exact absurd hj (by omega)
  · rintro rfl
    exact Or.inl rfl

/-- **A homogeneous polynomial divisible by `Xᵢ ^ a` but of degree below `a` is zero.**

The second arithmetic fact, and the one that turns the coprimality extraction into a vanishing
statement. Every monomial of a multiple of `Xᵢ ^ a` carries `Xᵢ` to at least the power `a`, so its
total degree is at least `a`; a homogeneous polynomial of degree `m < a` has none of those, hence
no monomials at all.

At a nonnegative twist this case never arises — there `m = a + d ≥ a` — which is why the
nonnegative argument produces a representing polynomial where this one produces `0`. -/
theorem eq_zero_of_X_pow_dvd_of_isHomogeneous_of_lt
    (i : ι) (a m : ℕ) (p : MvPolynomial ι k)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι k m)
    (hdvd : (MvPolynomial.X i : MvPolynomial ι k) ^ a ∣ p)
    (hlt : m < a) :
    p = 0 := by
  classical
  by_contra hne
  obtain ⟨s, hs⟩ : ∃ s, MvPolynomial.coeff s p ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (MvPolynomial.ext _ _ (by simpa using hall))
  -- Divisibility by `Xᵢ ^ a` forces the `i`-th exponent of every monomial up to `a`.
  have hsi : a ≤ s i := by
    by_contra hlt'
    push Not at hlt'
    obtain ⟨q, rfl⟩ := hdvd
    rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.coeff_monomial_mul'] at hs
    refine hs ?_
    rw [if_neg]
    intro hle
    exact absurd (by simpa using hle i) (by omega)
  -- Homogeneity pins the total degree, which is at least that exponent.
  have hdeg : (Finsupp.weight 1) s = m := hp hs
  have hle : s i ≤ (Finsupp.weight 1) s := by
    simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using
      Finset.single_le_sum (f := fun j => s j) (fun _ _ => Nat.zero_le _)
        (Finsupp.mem_support_iff.mpr (by omega : s i ≠ 0))
  omega

/-! ### The two-chart step

The overlap condition on two charts, once denominators are cleared, is exactly the cross
equation below. This is the mathematical heart of the negative-twist vanishing: everything above
it is arithmetic, everything below it is the plumbing that produces `hcross` from a Čech
cocycle. -/

/-- **A degree-`d` numerator on the `i`-chart that matches one on the `j`-chart vanishes, when
`d < 0`.**

`p / Xᵢ ^ a` and `q / Xⱼ ^ b` agree on the overlap exactly when `Xⱼ ^ b * p = Xᵢ ^ a * q` after
clearing the common denominator. Coprimality of the two variables then forces `Xᵢ ^ a ∣ p`, while
the degree bookkeeping `m = a + d` puts `p` below degree `a` as soon as `d < 0`. The two are
incompatible unless `p = 0`.

`hm` is where the twist appears: the numerator of a degree-`d` fraction with denominator `Xᵢ ^ a`
is homogeneous of degree `a + d`. That is `mem_intShiftPiece` unfolded, and it is the only fact
about `intShift` this step needs. -/
theorem num_eq_zero_of_cross_of_neg {i j : ι} (hij : i ≠ j) (d : ℤ) (hd : d < 0)
    (a b m : ℕ) (p q : MvPolynomial ι k) (hm : (m : ℤ) = (a : ℤ) + d)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι k m)
    (hcross : MvPolynomial.X j ^ b * p = MvPolynomial.X i ^ a * q) :
    p = 0 :=
  eq_zero_of_X_pow_dvd_of_isHomogeneous_of_lt ι k i a m p hp
    (X_pow_dvd_of_cross_mul ι k hij a b p q hcross) (by omega)

/-! ### Reducing `H⁰` to the kernel

Degree `0` has no incoming differential, so the general `exactAt` machinery the middle degrees use
still applies — but it degenerates. `(ComplexShape.up ℕ).prev 0 = 0` and `d 0 0 = 0` by the shape,
so exactness at `0` says precisely that the kernel of `d⁰` is trivial, with no image to quotient
by. Separating this out keeps the algebra below free of homological bookkeeping. -/

/-- Triviality of `ker d⁰` is exactly vanishing of `H⁰` for the algebraic Čech complex. -/
theorem intCechComplex_homology_zero_isZero_of_ker (d : ℤ)
    (hker : ∀ s : (polynomialVariableIntCechComplex ι k d).X 0,
      ConcreteCategory.hom ((polynomialVariableIntCechComplex ι k d).d 0 1) s = 0 → s = 0) :
    Limits.IsZero ((polynomialVariableIntCechComplex ι k d).homology 0) := by
  refine ((polynomialVariableIntCechComplex ι k d).exactAt_iff_isZero_homology 0).mp ?_
  rw [HomologicalComplex.exactAt_iff' _ 0 0 1 CochainComplex.prev_nat_zero
    (CochainComplex.next ℕ 0), ShortComplex.ab_exact_iff]
  intro s hs
  refine ⟨0, ?_⟩
  rw [map_zero]
  exact (hker s hs).symm

/-! ### From a Čech cocycle to the cross equation

The Čech differential in degree zero is `s ↦ (x ↦ face x 0 (s _) - face x 1 (s _))`, so a cocycle
says the two charts of any pair agree after both are pushed to the overlap. `faceMap_mk` writes
each push explicitly — clearing `X_i ^ a` costs `X_j ^ a` in numerator and denominator — and
`mk_eq_mk_iff` then clears the localization outright. What is left is an equation in the polynomial
ring, and cancelling the common factor leaves exactly the cross equation
`num_eq_zero_of_cross_of_neg` consumes. -/

/-- **The overlap condition on the two charts of a Čech index, cleared of denominators.**

`x` is a two-element Čech index; its faces are the single-chart indices, carrying `cj` on the
`x 1`-chart and `ci` on the `x 0`-chart. The hypothesis is that the two agree on the overlap,
which is the degree-zero cocycle condition at that index, and `hij` is what makes it say anything.

The denominators are `X_(x 0) ^ a`, `X_(x 1) ^ b` and `(X_(x 0) X_(x 1)) ^ n`; `mk_eq_mk_iff`
supplies the equation multiplied through by some `u ∈ Submonoid.powers (X_(x 0) X_(x 1))`, and
`MvPolynomial ι k` is a domain, so `u` and the common factor `X_(x 0) ^ b X_(x 1) ^ a` both
cancel. -/
theorem num_eq_zero_of_intCechFace_eq_of_neg (d : ℤ) (hd : d < 0)
    (x : Fin 2 → ι) (hij : x 0 ≠ x 1)
    (ci : NumDenSameDeg (polynomialGrading ι k) (intShift (polynomialGrading ι k) d)
      (.powers (polynomialVariableCechDenominator ι k (x ∘ (1 : Fin 2).succAbove))))
    (cj : NumDenSameDeg (polynomialGrading ι k) (intShift (polynomialGrading ι k) d)
      (.powers (polynomialVariableCechDenominator ι k (x ∘ (0 : Fin 2).succAbove))))
    (h : polynomialVariableIntCechFace ι k d x 0 (DegreeZeroLocalization.mk cj) =
      polynomialVariableIntCechFace ι k d x 1 (DegreeZeroLocalization.mk ci)) :
    (ci.num : MvPolynomial ι k) = 0 := by
  -- Dropping index `1` leaves the `x 0`-chart; the full index has both variables.
  have hdi : polynomialVariableCechDenominator ι k (x ∘ (1 : Fin 2).succAbove) =
      MvPolynomial.X (x 0) := by
    simp [polynomialVariableCechDenominator]
  have hd2 : polynomialVariableCechDenominator ι k x =
      MvPolynomial.X (x 0) * MvPolynomial.X (x 1) := by
    simp [polynomialVariableCechDenominator, Fin.prod_univ_two]
  -- `Submonoid.powers` membership arrives unreduced; pin the beta-reduced form.
  obtain ⟨a, ha'⟩ := ci.den_mem
  obtain ⟨b, hb'⟩ := cj.den_mem
  have ha : polynomialVariableCechDenominator ι k (x ∘ (1 : Fin 2).succAbove) ^ a =
      (ci.den : MvPolynomial ι k) := ha'
  have hb : polynomialVariableCechDenominator ι k (x ∘ (0 : Fin 2).succAbove) ^ b =
      (cj.den : MvPolynomial ι k) := hb'
  -- Both faces as explicit fractions, then the localization cleared.
  have e0 : polynomialVariableIntCechFace ι k d x 0 (DegreeZeroLocalization.mk cj) = _ :=
    DegreeZeroLocalization.faceMap_mk
      (𝓜 := intShift (polynomialGrading ι k) d)
      (MvPolynomial.isHomogeneous_X k (x 0))
      (polynomialVariableCechDenominator_succAbove_mem ι k x 0)
      (polynomialVariableCechDenominator_succAbove ι k x 0) cj b hb
  have e1 : polynomialVariableIntCechFace ι k d x 1 (DegreeZeroLocalization.mk ci) = _ :=
    DegreeZeroLocalization.faceMap_mk
      (𝓜 := intShift (polynomialGrading ι k) d)
      (MvPolynomial.isHomogeneous_X k (x 1))
      (polynomialVariableCechDenominator_succAbove_mem ι k x 1)
      (polynomialVariableCechDenominator_succAbove ι k x 1) ci a ha
  rw [e0, e1, DegreeZeroLocalization.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, ht'⟩ := u.2
  have ht : polynomialVariableCechDenominator ι k x ^ t = (u : MvPolynomial ι k) := ht'
  simp only [smul_eq_mul] at hu
  rw [← ht, hd2] at hu
  have hK : (MvPolynomial.X (x 0) ^ (t + b) * MvPolynomial.X (x 1) ^ (t + a) :
      MvPolynomial ι k) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (MvPolynomial.X_ne_zero (R := k) (x 0)))
      (pow_ne_zero _ (MvPolynomial.X_ne_zero (R := k) (x 1)))
  have key : (MvPolynomial.X (x 0) ^ (t + b) * MvPolynomial.X (x 1) ^ (t + a) :
        MvPolynomial ι k) * (MvPolynomial.X (x 0) ^ a * (cj.num : MvPolynomial ι k)) =
      (MvPolynomial.X (x 0) ^ (t + b) * MvPolynomial.X (x 1) ^ (t + a) : MvPolynomial ι k) *
        (MvPolynomial.X (x 1) ^ b * (ci.num : MvPolynomial ι k)) := by
    linear_combination hu
  have hcross : MvPolynomial.X (x 1) ^ b * (ci.num : MvPolynomial ι k) =
      MvPolynomial.X (x 0) ^ a * (cj.num : MvPolynomial ι k) := (mul_left_cancel₀ hK key).symm
  -- A nonzero homogeneous denominator pins the degree it was recorded at.
  have haX : (MvPolynomial.X (x 0) : MvPolynomial ι k) ^ a = (ci.den : MvPolynomial ι k) :=
    hdi ▸ ha
  have hpow : (MvPolynomial.X (x 0) : MvPolynomial ι k) ^ a ∈ polynomialGrading ι k a := by
    simpa using SetLike.pow_mem_graded (A := polynomialGrading ι k) a
      (MvPolynomial.isHomogeneous_X k (x 0))
  have hdeg : ci.deg = a := by
    apply DirectSum.degree_eq_of_mem_mem (polynomialGrading ι k) ci.den.2 (haX ▸ hpow)
    simpa only [← haX] using pow_ne_zero a (MvPolynomial.X_ne_zero (R := k) (x 0))
  -- `mem_intShiftPiece`: either the numerator is already zero, or it is homogeneous of the
  -- degree `a + d` that puts it below its own denominator.
  rcases ci.num.2 with h0 | ⟨m, hm, hmem⟩
  · exact h0
  · exact num_eq_zero_of_cross_of_neg ι k hij d hd a b m _ _ (by rw [hm, hdeg]) hmem hcross

/-- The `x 0`-chart component of a degree-zero cocycle vanishes, in the localization rather than
in its numerator. Choosing representatives is all that separates this from
`num_eq_zero_of_intCechFace_eq_of_neg`. -/
theorem intCechTerm_eq_zero_of_face_eq_of_neg (d : ℤ) (hd : d < 0)
    (x : Fin 2 → ι) (hij : x 0 ≠ x 1)
    (zi : polynomialVariableIntCechTerm ι k d 0 (x ∘ (1 : Fin 2).succAbove))
    (zj : polynomialVariableIntCechTerm ι k d 0 (x ∘ (0 : Fin 2).succAbove))
    (h : polynomialVariableIntCechFace ι k d x 0 zj =
      polynomialVariableIntCechFace ι k d x 1 zi) :
    zi = 0 := by
  obtain ⟨ci, rfl⟩ := DegreeZeroLocalization.mk_surjective zi
  obtain ⟨cj, rfl⟩ := DegreeZeroLocalization.mk_surjective zj
  have hnum := num_eq_zero_of_intCechFace_eq_of_neg ι k d hd x hij ci cj h
  apply DegreeZeroLocalization.ext
  simp [DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding, hnum]

/-! ### The cocycle condition, chart by chart

Only two charts are ever used, so `Nontrivial ι` is the whole hypothesis: a second variable has to
exist for the overlap condition to say anything. With one variable it is vacuous, and the statement
below is false rather than merely unproved. -/

/-- **A degree-zero cocycle of the integer-twist Čech complex vanishes when `d < 0`.**

Each component is read off its own two-element index `![y 0, j]`, so the choice of `j` is local to
the component and no compatible choice across all of `ι` is needed. -/
theorem intCechComplex_ker_zero_eq_zero_of_neg [Nontrivial ι] (d : ℤ) (hd : d < 0)
    (s : (polynomialVariableIntCechComplex ι k d).X 0)
    (hs : ConcreteCategory.hom ((polynomialVariableIntCechComplex ι k d).d 0 1) s = 0) :
    s = 0 := by
  let s' : ∀ y : Fin 1 → ι, polynomialVariableIntCechTerm ι k d 0 y := s
  funext y
  obtain ⟨j, hj⟩ := exists_ne (y 0)
  set x : Fin 2 → ι := ![y 0, j] with hxdef
  have hx0 : x 0 = y 0 := by simp [hxdef]
  have hx1 : x 1 = j := by simp [hxdef]
  -- Dropping index `1` from `![y 0, j]` returns the index `y` we started from.
  have hxy : x ∘ (1 : Fin 2).succAbove = y := by
    funext a
    rw [Subsingleton.elim a 0]
    show x ((1 : Fin 2).succAbove 0) = y 0
    rw [show ((1 : Fin 2).succAbove 0) = 0 from by decide, hx0]
  have hker : ConcreteCategory.hom
      ((polynomialVariableIntCechComplex ι k d).d 0 (0 + 1)) s' x = 0 :=
    congrArg (fun t => t x) hs
  rw [polynomialVariableIntCechComplex_d_apply, Fin.sum_univ_two] at hker
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul] at hker
  have hface : polynomialVariableIntCechFace ι k d x 0 (s' (x ∘ (0 : Fin 2).succAbove)) =
      polynomialVariableIntCechFace ι k d x 1 (s' (x ∘ (1 : Fin 2).succAbove)) :=
    eq_of_sub_eq_zero (by rwa [sub_eq_add_neg])
  have hzero := intCechTerm_eq_zero_of_face_eq_of_neg ι k d hd x
    (by rw [hx0, hx1]; exact hj.symm)
    (s' (x ∘ (1 : Fin 2).succAbove)) (s' (x ∘ (0 : Fin 2).succAbove)) hface
  rw [hxy] at hzero
  exact hzero

/-- **`H⁰` of the algebraic Čech complex vanishes at a negative twist.** -/
theorem polynomialVariableIntCechComplex_homology_zero_isZero [Nontrivial ι] (d : ℤ)
    (hd : d < 0) :
    Limits.IsZero ((polynomialVariableIntCechComplex ι k d).homology 0) :=
  intCechComplex_homology_zero_isZero_of_ker ι k d
    (fun s hs => intCechComplex_ker_zero_eq_zero_of_neg ι k d hd s hs)

/-- **`H⁰(Pⁿ, O(d)) = 0` for `d < 0`.**

The abelian-group statement of #665. `Nontrivial ι` is the only hypothesis on the variable set:
the argument compares two charts and never enumerates them, so no finiteness is needed, and at one
variable the statement is false rather than merely unproved. -/
theorem polynomialIntTwisting_H_zero_subsingleton [Nontrivial ι] (d : ℤ) (hd : d < 0)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u}
      (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k)))] :
    Subsingleton
      (@CategoryTheory.Sheaf.H
        (Opens (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
        (Opens.grothendieckTopology
          (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k)))
        ((_root_.AlgebraicGeometry.Scheme.Modules.toSheaf _).obj
          (associatedSheaf (polynomialGrading ι k)
            (intShift (polynomialGrading ι k) d))) _ hExt 0) := by
  obtain ⟨e⟩ := polynomialVariableIntCechComplex_computesCohomology ι k d 0
  have hsub : Subsingleton
      (((polynomialVariableIntCechComplex ι k d).homology 0 : AddCommGrpCat.{u})) :=
    AddCommGrpCat.subsingleton_of_isZero
      (polynomialVariableIntCechComplex_homology_zero_isZero ι k d hd)
  exact Equiv.subsingleton e.symm.toEquiv

end AlgebraicGeometry.Proj
