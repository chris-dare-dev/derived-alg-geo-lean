/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Discriminant

/-!
# Enriques surfaces, numerically

The numerical signature of a classical Enriques surface is

* `td₁(Y) = 0`, because the canonical class is torsion and disappears in the
  numerical quotient;
* `∫_Y td₂(Y) = χ(O_Y) = 1`.

`IsEnriques` records exactly this numerical shadow. It does not assert that a
geometric Enriques scheme exists, nor does it recover the non-trivial
2-torsion canonical line bundle: numerical equivalence cannot see that data.
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace Enriques

open Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 2 A N)

/-- The numerical signature of an Enriques surface: numerically trivial canonical
class and `χ(O_Y) = 1`.

This is deliberately weaker than `AlgebraicGeometry.SmoothProperVariety.IsEnriquesSurface`:
the latter is geometric and remembers non-trivial 2-torsion in `Pic`, while
this predicate lives after passage to numerical data. -/
structure IsEnriques : Prop where
  /-- `td₁(Y) = −K_Y/2 = 0` in the numerical quotient. -/
  toddComp_one : V.toddComp 1 = 0
  /-- `∫_Y td₂(Y) = χ(O_Y) = 1`. -/
  degree_toddComp_two : V.ring.degree (V.toddComp 2) = 1

/-- **Riemann--Roch on a numerical Enriques surface**:
`χ(E) = rank(E) + ∫_Y ch₂(E)`.

The `c₁` term vanishes numerically, while the rank term has coefficient one,
in contrast with the K3 coefficient two. -/
theorem chi_eq (hHRR : V.SatisfiesHRR) (hEnriques : IsEnriques V) (E : N) :
    (V.chi E : ℚ) = (V.rank E : ℚ) + V.ring.degree (V.chComp E 2) := by
  have h := V.chi_eq_sum hHRR E
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at h
  simp only [show (2 : ℕ) - 0 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
    show (2 : ℕ) - 2 = 0 from rfl] at h
  rw [h, V.chComp_zero, V.ring.degree_algebraMap_mul, V.toddComp_zero, mul_one,
    hEnriques.toddComp_one, hEnriques.degree_toddComp_two, mul_zero, map_zero]
  ring

end Enriques

end AlgebraicGeometry.Numerical
