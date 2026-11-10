/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support.Predicate.Quadratic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Finitely many lattice classes of bounded charge

The first sentence of Remark 12.3 of arXiv:1902.08184v4: if a quadratic form
`Q` is negative definite on `ker Z`, then for every `c` only finitely many
lattice classes `v` satisfy `‖Z v‖ < c` and `Q v ≥ 0`.

The statement is about a **lattice**, presented as an additive map
`ι : Λ →+ V` whose image is discrete. Stated for arbitrary vectors of `V` it is
false, and a dense image is not enough; see `finite_classes_of_isCompatible`.

## Main definitions

None. Both declarations are theorems about the existing support predicates.

## Main results

* `finite_range_inter_closedBall`: a discrete additive subgroup of a proper
  normed group, presented as the range of an additive map, meets every closed
  ball in finitely many points.
* `finite_classes_of_isCompatible`: Remark 12.3, first sentence.

## Implementation notes

The proof is the compactness direction of the support property,
`hasSupportProperty_of_isCompatible`, applied to the cone `{Q ≥ 0}`: it bounds
`‖v‖` by a multiple of `‖Z v‖` there, and a discrete subgroup meets a bounded
set of a finite-dimensional space in finitely many points. The charge target
`W` is left general, as in the basic support layer; the source uses `ℂ`.

## References

* arXiv:1902.08184v4 (Bayer, Lahoz, Macrì, Nuer, Perry, Stellari), Definition
  12.2(ii) and Remark 12.3.

## Tags

support property, quadratic form, lattice, finiteness
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.Support

variable {Λ V W : Type*} [AddCommGroup Λ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A discrete additive subgroup of a proper normed group meets every closed
ball in finitely many points.

The subgroup is presented as the range of an additive map, which is how class
maps out of a lattice reach a real vector space. -/
theorem finite_range_inter_closedBall [ProperSpace V] (ι : Λ →+ V)
    (hι : DiscreteTopology (Set.range ι)) (r : ℝ) :
    {x ∈ Set.range ι | ‖x‖ ≤ r}.Finite := by
  have hrange : ((ι.range : AddSubgroup V) : Set V) = Set.range ι := AddMonoidHom.coe_range ι
  have : DiscreteTopology ι.range := by
    change DiscreteTopology ((ι.range : AddSubgroup V) : Set V)
    rwa [hrange]
  have hclosed : IsClosed (Set.range ι) :=
    hrange ▸ AddSubgroup.isClosed_of_discreteTopology
  have hfinite := Metric.finite_isBounded_inter_isClosed
    (isDiscrete_iff_discreteTopology.mpr hι)
    (Metric.isBounded_closedBall (x := (0 : V)) (r := r)) hclosed
  refine hfinite.subset ?_
  rintro x ⟨hx, hxr⟩
  exact ⟨mem_closedBall_zero_iff.mpr hxr, hx⟩

/-- **Remark 12.3, first sentence.** If a quadratic form is negative definite
on the kernel of the charge, only finitely many lattice classes have charge of
norm less than `c` and nonnegative form.

The discreteness of `Set.range ι` is load-bearing. With `Λ = ℤ²`, `V = ℝ`,
`ι (a, b) = a + b √2`, `Z = id` and `Q x = x²`, the kernel of `Z` is zero, so
`hQ` holds vacuously, yet the image of `ι` is dense and infinitely many of its
points satisfy `‖Z x‖ < 1` and `0 ≤ Q x`. -/
theorem finite_classes_of_isCompatible (ι : Λ →+ V)
    (hι : DiscreteTopology (Set.range ι)) (Z : V →ₗ[ℝ] W) (Q : QuadraticForm ℝ V)
    (hQ : ∀ x, Z x = 0 → x ≠ 0 → Q x < 0) (c : ℝ) :
    {x ∈ Set.range ι | ‖Z x‖ < c ∧ 0 ≤ Q x}.Finite := by
  have hcompat : IsCompatible Z {x | 0 ≤ Q x} (Q : V → ℝ) :=
    ⟨fun _ hx => hx, hQ⟩
  obtain ⟨K, hK, hbound⟩ :=
    hasSupportProperty_of_isCompatible (quadraticForm_isHomogTwo Q) hcompat
  refine (finite_range_inter_closedBall ι hι (K * c)).subset ?_
  rintro x ⟨hx, hZx, hQx⟩
  exact ⟨hx, (hbound x hQx).trans (mul_le_mul_of_nonneg_left hZx.le hK.le)⟩

end CategoryTheory.Triangulated.WeakStabilityCondition.Support
