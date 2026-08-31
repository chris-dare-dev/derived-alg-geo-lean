/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# The standard grading on a multivariate polynomial ring

Besides naming the grading, this file records that the polynomial variables
generate the ring over its degree-zero homogeneous submodule. Projective-space
files consume that algebraic generation theorem when proving cover and
finite-type statements.
-/

universe u

namespace MvPolynomial

/-- The standard total-degree grading on a multivariate polynomial ring. -/
abbrev polynomialGrading (ι R : Type u) [CommRing R] :
    ℕ → Submodule R (MvPolynomial ι R) :=
  MvPolynomial.homogeneousSubmodule ι R

/-- The variables generate a polynomial ring over its degree-zero homogeneous submodule. -/
theorem polynomialVariable_adjoin_eq_top (ι k : Type u) [Field k] :
    Algebra.adjoin (polynomialGrading ι k 0)
      (Set.range fun i => ((X i : MvPolynomial ι k))) = ⊤ := by
  set S := Algebra.adjoin (polynomialGrading ι k 0)
    (Set.range fun i => ((X i : MvPolynomial ι k))) with hS
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact S.algebraMap_mem ⟨C r, isHomogeneous_C (σ := ι) r⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp =>
      exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

end MvPolynomial
