/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support.Predicate.Quadratic

/-!
# A single quadratic support form across an indexed family

Definition 18.5 and Lemma 18.6 of arXiv:1902.08184v4 use a *uniform*
quadratic form: the same form controls the semistable classes on every fiber.
This file isolates that quantifier order.  In particular,
`HasUniformQuadraticSupportProperty Z S` is not the weaker assertion
`∀ i, HasQuadraticSupportProperty Z (S i)`, which would allow a different
form for each index.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.Support

variable {I J V V' W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup V'] [NormedSpace ℝ V']
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The union of all selected classes in an indexed family. -/
def familyLocus (S : I → Set V) : Set V := ⋃ i, S i

/-- A single genuine quadratic form compatible with every member of an
indexed family of selected loci. -/
def HasUniformQuadraticSupportProperty
    (Z : V →ₗ[ℝ] W) (S : I → Set V) : Prop :=
  ∃ Q : QuadraticForm ℝ V,
    (∀ i x, x ∈ S i → 0 ≤ Q x) ∧
    ∀ x : V, Z x = 0 → x ≠ 0 → Q x < 0

/-- Uniform support specializes to support on each index. -/
theorem HasUniformQuadraticSupportProperty.fiber
    {Z : V →ₗ[ℝ] W} {S : I → Set V}
    (h : HasUniformQuadraticSupportProperty Z S) (i : I) :
    HasQuadraticSupportProperty Z (S i) := by
  obtain ⟨Q, hnonneg, hneg⟩ := h
  exact ⟨Q, ⟨hnonneg i, hneg⟩⟩

/-- A quadratic form compatible with the union is uniformly compatible with
the indexed family. -/
theorem hasUniformQuadraticSupportProperty_of_union
    {Z : V →ₗ[ℝ] W} {S : I → Set V}
    (h : HasQuadraticSupportProperty Z (familyLocus S)) :
    HasUniformQuadraticSupportProperty Z S := by
  obtain ⟨Q, hQ⟩ := h
  refine ⟨Q, ?_, hQ.neg_of_ker⟩
  intro i x hx
  exact hQ.nonneg_of_mem x (Set.mem_iUnion.mpr ⟨i, hx⟩)

/-- Uniform compatibility is exactly compatibility on the union of all
selected classes. -/
theorem hasUniformQuadraticSupportProperty_iff_union
    {Z : V →ₗ[ℝ] W} {S : I → Set V} :
    HasUniformQuadraticSupportProperty Z S ↔
      HasQuadraticSupportProperty Z (familyLocus S) := by
  constructor
  · rintro ⟨Q, hnonneg, hneg⟩
    refine ⟨Q, ⟨?_, hneg⟩⟩
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact hnonneg i x hxi
  · exact hasUniformQuadraticSupportProperty_of_union

/-- Reindexing a uniformly controlled family preserves the same witness. -/
theorem HasUniformQuadraticSupportProperty.reindex
    {Z : V →ₗ[ℝ] W} {S : I → Set V}
    (h : HasUniformQuadraticSupportProperty Z S) (f : J → I) :
    HasUniformQuadraticSupportProperty Z (fun j => S (f j)) := by
  obtain ⟨Q, hnonneg, hneg⟩ := h
  exact ⟨Q, fun j => hnonneg (f j), hneg⟩

/-- One quadratic support form gives a uniform constant family. -/
theorem HasQuadraticSupportProperty.constant
    {Z : V →ₗ[ℝ] W} {S : Set V}
    (h : HasQuadraticSupportProperty Z S) (I : Type*) :
    HasUniformQuadraticSupportProperty Z (fun _ : I => S) := by
  obtain ⟨Q, hQ⟩ := h
  exact ⟨Q, fun _ => hQ.nonneg_of_mem, hQ.neg_of_ker⟩

/-- For a nonempty index type, a constant family is uniformly supported if
and only if its unique locus is quadratically supported. -/
theorem hasUniformQuadraticSupportProperty_constant_iff
    [Nonempty I] {Z : V →ₗ[ℝ] W} {S : Set V} :
    HasUniformQuadraticSupportProperty Z (fun _ : I => S) ↔
      HasQuadraticSupportProperty Z S := by
  constructor
  · intro h
    exact h.fiber (Classical.choice inferInstance)
  · intro h
    exact h.constant I

/-- Transport a quadratic form along a linear equivalence of class spaces. -/
def transportQuadraticForm (e : V ≃ₗ[ℝ] V') (Q : QuadraticForm ℝ V) :
    QuadraticForm ℝ V' :=
  Q.comp e.symm.toLinearMap

@[simp]
theorem transportQuadraticForm_apply
    (e : V ≃ₗ[ℝ] V') (Q : QuadraticForm ℝ V) (x : V') :
    transportQuadraticForm e Q x = Q (e.symm x) := rfl

/-- Compatibility with a genuine quadratic form is invariant under a linear
equivalence, with both the charge and selected classes transported. -/
theorem isCompatible_transport
    (e : V ≃ₗ[ℝ] V') {Z : V →ₗ[ℝ] W} {S : Set V}
    {Q : QuadraticForm ℝ V} (hQ : IsCompatible Z S Q) :
    IsCompatible (Z.comp e.symm.toLinearMap) (e '' S)
      (transportQuadraticForm e Q) := by
  constructor
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    simpa using hQ.nonneg_of_mem x hx
  · intro y hy hy0
    apply hQ.neg_of_ker (e.symm y)
    · exact hy
    · exact fun hzero => hy0 (by simpa using congrArg e hzero)

/-- Uniform quadratic support is invariant under a linear equivalence of the
class space. -/
theorem HasUniformQuadraticSupportProperty.transport
    (e : V ≃ₗ[ℝ] V') {Z : V →ₗ[ℝ] W} {S : I → Set V}
    (h : HasUniformQuadraticSupportProperty Z S) :
    HasUniformQuadraticSupportProperty (Z.comp e.symm.toLinearMap)
      (fun i => e '' S i) := by
  obtain ⟨Q, hnonneg, hneg⟩ := h
  refine ⟨transportQuadraticForm e Q, ?_, ?_⟩
  · intro i y hy
    exact (isCompatible_transport e ⟨hnonneg i, hneg⟩).nonneg_of_mem y hy
  · intro y hy hy0
    apply hneg (e.symm y)
    · exact hy
    · exact fun hzero => hy0 (by simpa using congrArg e hzero)

/-- The transport construction is an equivalence, not merely a one-way
preservation theorem. -/
theorem hasUniformQuadraticSupportProperty_transport_iff
    (e : V ≃ₗ[ℝ] V') {Z : V →ₗ[ℝ] W} {S : I → Set V} :
    HasUniformQuadraticSupportProperty
        (Z.comp e.symm.toLinearMap) (fun i => e '' S i) ↔
      HasUniformQuadraticSupportProperty Z S := by
  constructor
  · rintro ⟨Q, hnonneg, hneg⟩
    refine ⟨transportQuadraticForm e.symm Q, ?_, ?_⟩
    · intro i x hx
      simpa using hnonneg i (e x) ⟨x, hx, rfl⟩
    · intro x hx hx0
      apply hneg (e x)
      · simpa using hx
      · exact fun hzero => hx0 (by simpa using congrArg e.symm hzero)
  · intro h
    exact h.transport e

end CategoryTheory.Triangulated.WeakStabilityCondition.Support
