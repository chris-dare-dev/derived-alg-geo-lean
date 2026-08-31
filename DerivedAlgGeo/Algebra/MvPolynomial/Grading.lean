/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The standard grading on a multivariate polynomial ring -/

universe u

namespace MvPolynomial

/-- The standard total-degree grading on a multivariate polynomial ring. -/
abbrev polynomialGrading (ι R : Type u) [CommRing R] :
    ℕ → Submodule R (MvPolynomial ι R) :=
  MvPolynomial.homogeneousSubmodule ι R

end MvPolynomial
