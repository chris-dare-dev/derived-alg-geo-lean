/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Module.GradedModule.Shift
import DerivedAlgGeo.Algebra.MvPolynomial.Grading

/-!
# The variable Čech diagram of a graded polynomial module

For a tuple of variables, this file forms the product denominator, the corresponding degree-zero
localization of an arbitrary graded polynomial module, and the face map obtained by adjoining one
variable. The construction is entirely algebraic: it does not mention `Proj`, basic opens, sheaves,
or cohomology.

The natural- and integer-shift terms are definitional specializations of the arbitrary graded-family
construction. This file also owns the canonical `p / 1` element in a one-variable term. Geometric
consumers compare these localizations and elements with sections on intersections of the variable
basic-open cover.

## Tags

Čech diagram, multivariate polynomial, homogeneous localization, graded module
-/

open GradedModule

noncomputable section

namespace MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Denominators -/

/-- The product of the variables indexing one `(n + 1)`-fold Čech intersection. -/
def polynomialVariableCechDenominator
    (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    MvPolynomial ι k :=
  ∏ a, MvPolynomial.X (x a)

/-- The Čech denominator for an `(n + 1)`-fold intersection is homogeneous of degree `n + 1`. -/
theorem polynomialVariableCechDenominator_mem
    (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    polynomialVariableCechDenominator ι k x ∈ polynomialGrading ι k (n + 1) := by
  classical
  simpa [polynomialVariableCechDenominator] using
    SetLike.prod_mem_graded (polynomialGrading ι k)
      (fun _ : Fin (n + 1) => 1) (fun a => MvPolynomial.X (x a))
      (F := Finset.univ) (fun a _ => MvPolynomial.isHomogeneous_X k (x a))

/-! ## Natural-shift terms and faces -/

/-- The algebraic degree-`d` term attached to one variable Čech intersection. It is a
degree-zero homogeneous localization, with no geometric or finite-dimensionality assertion. -/
abbrev polynomialVariableCechTerm
    (ι k : Type u) [Field k] (d n : ℕ) (x : Fin (n + 1) → ι) :=
  DegreeZeroLocalization (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)
      (.powers (polynomialVariableCechDenominator ι k x))

/-- Degree-`n` algebraic Čech cochains for a natural shift. -/
abbrev polynomialVariableCechCochains
    (ι k : Type u) [Field k] (d n : ℕ) :=
  ∀ x : Fin (n + 1) → ι, polynomialVariableCechTerm ι k d n x

/-- The canonical fraction `p / 1` in the degree-zero localization at one polynomial variable. -/
def polynomialVariableFraction
    (ι k : Type u) [Field k] (d : ℕ)
    (p : homogeneousSubmodule ι k d) (i : ι) :
    DegreeZeroLocalization (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d) (.powers (X i)) :=
  DegreeZeroLocalization.mk
    { deg := 0
      num := ⟨p.1, by
        change p.1 ∈ polynomialGrading ι k (0 + d)
        simpa only [zero_add] using p.2⟩
      den := ⟨1, SetLike.one_mem_graded (polynomialGrading ι k)⟩
      den_mem := Submonoid.one_mem _ }

/-- Dropping the `j`-th index multiplies the Čech denominator back up by that variable. -/
theorem polynomialVariableCechDenominator_succAbove
    (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    polynomialVariableCechDenominator ι k (x ∘ j.succAbove) * MvPolynomial.X (x j) =
      polynomialVariableCechDenominator ι k x := by
  classical
  rw [polynomialVariableCechDenominator, polynomialVariableCechDenominator,
    Fin.prod_univ_succAbove (fun a : Fin (n + 2) => MvPolynomial.X (R := k) (x a)) j,
    mul_comm]
  rfl

/-- The `j`-th Čech denominator divides the full one, in the `Submonoid.powers` form
`faceMap` asks for. -/
theorem polynomialVariableCechDenominator_succAbove_mem
    (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    polynomialVariableCechDenominator ι k (x ∘ j.succAbove) * MvPolynomial.X (x j) ∈
      Submonoid.powers (polynomialVariableCechDenominator ι k x) :=
  ⟨1, by
    show polynomialVariableCechDenominator ι k x ^ 1 = _
    rw [pow_one, polynomialVariableCechDenominator_succAbove]⟩

/-- The `j`-th face of the algebraic variable Čech diagram for a natural shift. -/
noncomputable def polynomialVariableCechFace
    (ι k : Type u) [Field k] (d : ℕ) {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    polynomialVariableCechTerm ι k d n (x ∘ j.succAbove) →+
      polynomialVariableCechTerm ι k d (n + 1) x :=
  DegreeZeroLocalization.faceMap
    (𝓜 := natShift (polynomialGrading ι k) d)
    (MvPolynomial.isHomogeneous_X k (x j))
    (polynomialVariableCechDenominator_succAbove_mem ι k x j)
    (polynomialVariableCechDenominator_succAbove ι k x j)

/-! ## Integer-shift terms and faces -/

/-- The algebraic term attached to one variable Čech intersection, for an integer shift. -/
abbrev polynomialVariableIntCechTerm
    (ι k : Type u) [Field k] (d : ℤ) (n : ℕ) (x : Fin (n + 1) → ι) :=
  DegreeZeroLocalization (polynomialGrading ι k)
    (intShift (polynomialGrading ι k) d)
      (.powers (polynomialVariableCechDenominator ι k x))

/-- Degree-`n` algebraic Čech cochains for an integer shift. -/
abbrev polynomialVariableIntCechCochains
    (ι k : Type u) [Field k] (d : ℤ) (n : ℕ) :=
  ∀ x : Fin (n + 1) → ι, polynomialVariableIntCechTerm ι k d n x

/-- The `j`-th face of the algebraic variable Čech diagram for an integer shift. -/
noncomputable def polynomialVariableIntCechFace
    (ι k : Type u) [Field k] (d : ℤ) {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    polynomialVariableIntCechTerm ι k d n (x ∘ j.succAbove) →+
      polynomialVariableIntCechTerm ι k d (n + 1) x :=
  DegreeZeroLocalization.faceMap
    (𝓜 := intShift (polynomialGrading ι k) d)
    (MvPolynomial.isHomogeneous_X k (x j))
    (polynomialVariableCechDenominator_succAbove_mem ι k x j)
    (polynomialVariableCechDenominator_succAbove ι k x j)

/-! ## An arbitrary graded family -/

/-- The algebraic term attached to one variable Čech intersection, for an arbitrary graded
family of polynomial modules. -/
abbrev cechTerm (ι k : Type u) [Field k] {σM : Type u} [SetLike σM (MvPolynomial ι k)]
    [AddSubgroupClass σM (MvPolynomial ι k)] (𝓂 : ℕ → σM)
    [SetLike.GradedSMul (polynomialGrading ι k) 𝓂] {n : ℕ} (x : Fin (n + 1) → ι) :=
  DegreeZeroLocalization (polynomialGrading ι k) 𝓂
    (.powers (polynomialVariableCechDenominator ι k x))

/-- Degree-`n` algebraic Čech cochains for an arbitrary graded family. -/
abbrev cechCochains (ι k : Type u) [Field k] {σM : Type u} [SetLike σM (MvPolynomial ι k)]
    [AddSubgroupClass σM (MvPolynomial ι k)] (𝓂 : ℕ → σM)
    [SetLike.GradedSMul (polynomialGrading ι k) 𝓂] (n : ℕ) :=
  ∀ x : Fin (n + 1) → ι, cechTerm ι k 𝓂 x

/-- The `j`-th variable Čech face for an arbitrary graded family. -/
noncomputable def cechFace (ι k : Type u) [Field k] {σM : Type u}
    [SetLike σM (MvPolynomial ι k)] [AddSubgroupClass σM (MvPolynomial ι k)] (𝓂 : ℕ → σM)
    [SetLike.GradedSMul (polynomialGrading ι k) 𝓂] {n : ℕ} (x : Fin (n + 2) → ι)
    (j : Fin (n + 2)) :
    cechTerm ι k 𝓂 (x ∘ j.succAbove) →+ cechTerm ι k 𝓂 x :=
  DegreeZeroLocalization.faceMap (𝓜 := 𝓂)
    (MvPolynomial.isHomogeneous_X k (x j))
    (polynomialVariableCechDenominator_succAbove_mem ι k x j)
    (polynomialVariableCechDenominator_succAbove ι k x j)

/-- The natural-shift face is the arbitrary-family face at `natShift`. -/
theorem cechFace_natShift (ι k : Type u) [Field k] (d : ℕ) {n : ℕ} (x : Fin (n + 2) → ι)
    (j : Fin (n + 2)) :
    cechFace ι k (natShift (polynomialGrading ι k) d) x j =
      polynomialVariableCechFace ι k d x j :=
  rfl

/-- The integer-shift face is the arbitrary-family face at `intShift`. -/
theorem cechFace_intShift (ι k : Type u) [Field k] (d : ℤ) {n : ℕ} (x : Fin (n + 2) → ι)
    (j : Fin (n + 2)) :
    cechFace ι k (intShift (polynomialGrading ι k) d) x j =
      polynomialVariableIntCechFace ι k d x j :=
  rfl

/-! ## Cofactors -/

/-- The product of all but the first variable in a Čech index. -/
noncomputable def cechCofactor (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    MvPolynomial ι k :=
  ∏ a : Fin n, MvPolynomial.X (x a.succ)

/-- Splitting the Čech denominator off its first variable. -/
theorem X_mul_cechCofactor (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    (MvPolynomial.X (x 0) : MvPolynomial ι k) * cechCofactor ι k x =
      polynomialVariableCechDenominator ι k x :=
  (Fin.prod_univ_succ (fun a => MvPolynomial.X (x a))).symm

/-- The cofactor is homogeneous of degree `n`. -/
theorem cechCofactor_mem (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    cechCofactor ι k x ∈ polynomialGrading ι k n := by
  unfold cechCofactor
  simpa using SetLike.prod_mem_graded (polynomialGrading ι k) (fun _ : Fin n => 1)
    (fun a => MvPolynomial.X (x a.succ)) (F := Finset.univ)
    (fun a _ => MvPolynomial.isHomogeneous_X k (x a.succ))

end MvPolynomial
