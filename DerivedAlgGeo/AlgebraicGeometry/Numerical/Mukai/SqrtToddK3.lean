/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.SqrtTodd
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.K3

/-!
# The square-root Todd class on a K3 surface

This downstream specialization combines the generic square-root construction
with the numerical K3 axioms.  The generic construction therefore remains
importable without K3 Riemann--Roch.
-/

universe u v

namespace AlgebraicGeometry.Numerical.K3

variable {A : Type u} [CommRing A] [Algebra ℚ A]
variable {N : Type v} [AddCommGroup N]
variable {V : NumericalVarietyData 2 A N}

/-- On a K3 the linear term of `√td` vanishes, because `td₁ = 0`. -/
theorem sqrtToddComp_one (hK3 : IsK3 V) : V.sqrtToddComp 1 = 0 := by
  rw [NumericalVarietyData.sqrtToddComp, sqrtComp_one, hK3.toddComp_one, mul_zero]

/-- `∫_X √td₂ = 1`: with `td₁ = 0` the quadratic term is `td₂/2`, and
`∫td₂ = χ(O_X) = 2`. -/
theorem degree_sqrtToddComp_two (hK3 : IsK3 V) :
    V.ring.degree (V.sqrtToddComp 2) = 1 := by
  show V.ring.degree (algebraMap ℚ A (1 / 2) * V.toddComp 2
    - algebraMap ℚ A (1 / 8) * (V.toddComp 1 * V.toddComp 1)) = 1
  rw [hK3.toddComp_one, mul_zero, mul_zero, sub_zero,
    NumericalRingData.degree_algebraMap_mul, hK3.degree_toddComp_two]
  norm_num

end AlgebraicGeometry.Numerical.K3
