/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.TwistedChern
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Exponential.Twist

/-!
# Rational Chern twists and the real exponential action

The rational, intersection-ring-valued `Numerical.twist` is retained for its
geometric consumers. Taking weighted degrees and extending scalars to `ℝ`
intertwines it with `Wall.Exp.twist`. The truncation degree `m` may be smaller
than the geometric dimension `n`; the comparison requires `m ≤ n` to combine
the powers of the polarisation. The component family is arbitrary, so it may
already include a correction class.
-/

open Finset
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

namespace AlgebraicGeometry.Numerical

noncomputable section

variable {A : Type*} [CommRing A] [Algebra ℚ A] {n : ℕ}

/-- Weighted degrees intertwine the rational intersection-ring twist with the
real exponential action, at every truncation degree at most the dimension. -/
theorem twist_degree_eq_exp (R : NumericalRingData n A) (H : A) (β : ℚ)
    (c : ℕ → A) (m : ℕ) (hmn : m ≤ n) :
    (fun i : Fin (m + 1) => (R.degree (twist H β c i * H ^ (n - i.val)) : ℝ)) =
      Exp.twist m (β : ℝ)
        (fun i => (R.degree (c i * H ^ (n - i.val)) : ℝ)) := by
  funext i
  rw [Exp.twist_apply, twist, Finset.sum_mul, map_sum, Rat.cast_sum,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hpow : H ^ (i.val - j.val) * H ^ (n - i.val) = H ^ (n - j.val) := by
    rw [← pow_add]
    congr 1
    have := i.isLt
    have := j.isLt
    omega
  rw [show algebraMap ℚ A (twistCoeff β (i.val - j.val)) * c j *
        H ^ (i.val - j.val) * H ^ (n - i.val) =
      algebraMap ℚ A (twistCoeff β (i.val - j.val)) * (c j * H ^ (n - j.val)) by
        rw [← hpow]; ring,
    R.degree_algebraMap_mul]
  simp only [twistCoeff]
  push_cast
  rfl

end

end AlgebraicGeometry.Numerical
