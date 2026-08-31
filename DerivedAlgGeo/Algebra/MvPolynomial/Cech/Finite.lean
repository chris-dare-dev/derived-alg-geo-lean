/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.MvPolynomial.Cech.Homotopy
import DerivedAlgGeo.Algebra.MvPolynomial.LaurentFinite

/-!
# The full blocks of a Čech degree, assembled

`LaurentFinite.lean` shows the full block of one localization is a finite-dimensional `k`-space,
stated at the monomial denominator `Xᵞ`. A Čech term is the same object at the denominator
`∏ Xₓₐ`, which is that monomial — `tupleDenominator_eq` — but not syntactically, so the subspace
has to be carried across. `powersCongrLinear` is the transport, and it is `k`-linear for the same
reason its additive form exists at all: it moves nothing but the name of the type.

## Two finiteness facts, both needed

`fg_cechBlockSpan` is one tuple: finitely many Laurent exponents can be negative in every variable
at a fixed total degree. `module_finite_pi_cechBlockSpan` is all tuples at once, and it is a
different fact: a Čech index has fixed length and `ι` is finite, so there are finitely many of
them. Neither implies the other, and the top-degree argument needs both — which is why `Fintype ι`
appears twice over in this lane rather than once.

## Scope

The cochain side only. Nothing here mentions the differential, cocycles, or cohomology, and the
`k`-action used is `degreeZeroLocalizationModule` — matching it against the `cechScalarAction`
that `module_finite_linearCoherentH_of_cech` consumes is a separate step and is not done here.
-/

universe u

open GradedModule

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k]
variable {σM : Type u} [SetLike σM (MvPolynomial ι k)]
  [AddSubgroupClass σM (MvPolynomial ι k)] (𝓜 : ℕ → σM)
  [SetLike.GradedSMul (polynomialGrading ι k) 𝓜]

/-- `powersCongr` as a `k`-linear equivalence. It moves nothing but the name of the type, so
linearity is the same `subst` its additive form is. -/
noncomputable def powersCongrLinear {f g : MvPolynomial ι k} (h : f = g) :
    DegreeZeroLocalization (polynomialGrading ι k) 𝓜 (.powers f) ≃ₗ[k]
      DegreeZeroLocalization (polynomialGrading ι k) 𝓜 (.powers g) := by
  subst h
  exact LinearEquiv.refl _ _

theorem powersCongrLinear_apply {f g : MvPolynomial ι k} (h : f = g)
    (z : DegreeZeroLocalization (polynomialGrading ι k) 𝓜 (.powers f)) :
    powersCongrLinear ι k 𝓜 h z = DegreeZeroLocalization.powersCongr h z := by
  subst h; rfl

theorem powersCongrLinear_symm_apply {f g : MvPolynomial ι k} (h : f = g)
    (z : DegreeZeroLocalization (polynomialGrading ι k) 𝓜 (.powers g)) :
    (powersCongrLinear ι k 𝓜 h).symm z =
      (DegreeZeroLocalization.powersCongr (𝒜 := polynomialGrading ι k) (𝓜 := 𝓜) h).symm z := by
  subst h; rfl

/-- The full block of a Čech term, as a `k`-subspace: the block of the monomial presentation,
carried back along the denominator comparison.

Definable without finiteness of `ι` — only its finite generation needs that. -/
noncomputable def cechBlockSpan (d : ℤ) {n : ℕ} (x : Fin (n + 1) → ι) :
    Submodule k (DegreeZeroLocalization (polynomialGrading ι k) 𝓜
      (.powers (polynomialVariableCechDenominator ι k x))) :=
  Submodule.map (powersCongrLinear ι k 𝓜 (tupleDenominator_eq ι k x)).symm.toLinearMap
    (Submodule.span k (blockRep ι k 𝓜 (tupleExponent ι x) ''
      {α : ι →₀ ℤ | α.degree = d ∧ ∀ j : ι, α j < 0}))

/-- The full-block projection of any term lands in that subspace. -/
theorem cechBlockProj_mem_cechBlockSpan [Fintype ι] {d : ℤ} (h𝓜 : IsPolynomialTwist 𝓜 d)
    {n : ℕ} (x : Fin (n + 1) → ι) (z : cechTerm ι k 𝓜 x) :
    cechBlockProj ι k h𝓜 x Finset.univ z ∈ cechBlockSpan ι k 𝓜 d x := by
  rw [cechBlockProj_apply, cechBlockSpan]
  refine ⟨blockProj h𝓜 (tupleExponent ι x) Finset.univ (cechTermEquiv ι k 𝓜 x z),
    blockProj_univ_mem_span ι k 𝓜 h𝓜 (tupleExponent ι x) _, ?_⟩
  exact powersCongrLinear_symm_apply ι k 𝓜 _ _

/-- The full block of a Čech term is finitely generated. -/
theorem fg_cechBlockSpan [Fintype ι] (d : ℤ) {n : ℕ} (x : Fin (n + 1) → ι) :
    (cechBlockSpan ι k 𝓜 d x).FG := by
  rw [cechBlockSpan]
  exact Submodule.FG.map (powersCongrLinear ι k 𝓜 (tupleDenominator_eq ι k x)).symm.toLinearMap
    (fg_blockSpan ι k 𝓜 (d := d) (tupleExponent ι x))

/-- **The full blocks of all tuples together are finite-dimensional.**

Two finiteness facts meet here and neither is enough alone: each block is finitely generated
because only finitely many Laurent exponents are negative in every variable, and there are only
finitely many tuples because `ι` is finite and a Čech index has fixed length. -/
instance module_finite_pi_cechBlockSpan [Fintype ι] (d : ℤ) {n : ℕ} :
    Module.Finite k (∀ x : Fin (n + 1) → ι, ↥(cechBlockSpan ι k 𝓜 d x)) := by
  haveI : ∀ x : Fin (n + 1) → ι, Module.Finite k ↥(cechBlockSpan ι k 𝓜 d x) := fun x =>
    Module.Finite.iff_fg.mpr (fg_cechBlockSpan ι k 𝓜 d x)
  infer_instance

end MvPolynomial
