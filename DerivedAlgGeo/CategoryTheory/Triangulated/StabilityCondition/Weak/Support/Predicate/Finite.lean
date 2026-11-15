/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support.Predicate.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Finitely many lattice classes of bounded charge

The first sentence of Remark 12.3 of arXiv:1902.08184v4: if a quadratic form
`Q` is negative definite on `ker Z`, then for every `C > 0` there are only
finitely many classes `v` with `|Z(v)| < C` and `Q(v) ≥ 0`.

The classes are those of a **lattice**, presented as the range of an additive
map `ι : Λ →+ V` whose image is discrete; for `Λ` free of finite rank and
`ι : Λ → Λ ⊗ ℝ` the canonical map, these are the classes of the source. Stated
for arbitrary vectors of `V` the remark is false, and a dense image is not
enough; see `finite_classes_of_isCompatible`.

## Main results

* `HasSupportProperty.finite_classes`: under the norm-bound support property
  on `S`, only finitely many lattice points of `S` have charge of norm less
  than `c`.
* `finite_classes_of_isCompatible`: Remark 12.3, first sentence.

## Implementation notes

The support property bounds `‖v‖` by a multiple of `‖Z v‖` on `S`, and a
discrete additive subgroup of a finite-dimensional space meets a bounded set in
finitely many points. For the first sentence of the remark, `S` is the cone
`{Q ≥ 0}` and the bound is the compactness direction
`hasSupportProperty_of_isCompatible`. As in the basic support layer, `Q` need
only be continuous and homogeneous of degree two, and the charge target `W` is
left general; the source uses a quadratic form and `ℂ`.

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
/-- A discrete additive subgroup of a proper normed group, presented as the
range of an additive map, meets every closed ball in finitely many points. -/
private theorem finite_range_inter_closedBall [ProperSpace V] (ι : Λ →+ V)
    (hι : DiscreteTopology (Set.range ι)) (r : ℝ) :
    {x ∈ Set.range ι | ‖x‖ ≤ r}.Finite := by
  have hrange : ((ι.range : AddSubgroup V) : Set V) = Set.range ι := AddMonoidHom.coe_range ι
  have : DiscreteTopology ι.range := by
    change DiscreteTopology ((ι.range : AddSubgroup V) : Set V)
    rwa [hrange]
  have hclosed : IsClosed (Set.range ι) :=
    hrange ▸ AddSubgroup.isClosed_of_discreteTopology
  refine (Metric.finite_isBounded_inter_isClosed (isDiscrete_iff_discreteTopology.mpr hι)
    (Metric.isBounded_closedBall (x := (0 : V)) (r := r)) hclosed).subset ?_
  rintro x ⟨hx, hxr⟩
  exact ⟨mem_closedBall_zero_iff.mpr hxr, hx⟩

/-- **Finitely many lattice classes of bounded charge.** If the charge has the
support property on `S`, only finitely many points of the discrete lattice
`Set.range ι` lie in `S` and have charge of norm less than `c`. -/
theorem HasSupportProperty.finite_classes {Z : V →ₗ[ℝ] W} {S : Set V}
    (h : HasSupportProperty Z S) (ι : Λ →+ V) (hι : DiscreteTopology (Set.range ι))
    (c : ℝ) : {x ∈ Set.range ι | x ∈ S ∧ ‖Z x‖ < c}.Finite := by
  obtain ⟨K, hK, hbound⟩ := h
  refine (finite_range_inter_closedBall ι hι (K * c)).subset ?_
  rintro x ⟨hx, hxS, hZx⟩
  exact ⟨hx, (hbound x hxS).trans (mul_le_mul_of_nonneg_left hZx.le hK.le)⟩

/-- **Remark 12.3, first sentence.** If `Q` is negative definite on the kernel
of the charge, only finitely many points of the discrete lattice `Set.range ι`
have charge of norm less than `c` and nonnegative `Q`.

`Q` need only be continuous and homogeneous of degree two; a quadratic form
qualifies by `quadraticForm_isHomogTwo`.

The discreteness of `Set.range ι` is load-bearing. With `Λ = ℤ²`, `V = W = ℝ`,
`ι (a, b) = a + b √2`, `Z = id` and `Q x = x²`, the kernel of `Z` is zero, so
`hker` holds vacuously, yet the image of `ι` is dense and infinitely many of
its points satisfy `‖Z x‖ < 1` and `0 ≤ Q x`. -/
theorem finite_classes_of_isCompatible (ι : Λ →+ V) (hι : DiscreteTopology (Set.range ι))
    (Z : V →ₗ[ℝ] W) {Q : V → ℝ} (hQ : IsHomogTwo Q)
    (hker : ∀ x, Z x = 0 → x ≠ 0 → Q x < 0) (c : ℝ) :
    {x ∈ Set.range ι | ‖Z x‖ < c ∧ 0 ≤ Q x}.Finite := by
  refine ((hasSupportProperty_of_isCompatible (S := {x | 0 ≤ Q x}) hQ
    ⟨fun _ hx => hx, hker⟩).finite_classes ι hι c).subset ?_
  rintro x ⟨hx, hZx, hQx⟩
  exact ⟨hx, hQx, hZx⟩

end CategoryTheory.Triangulated.WeakStabilityCondition.Support
