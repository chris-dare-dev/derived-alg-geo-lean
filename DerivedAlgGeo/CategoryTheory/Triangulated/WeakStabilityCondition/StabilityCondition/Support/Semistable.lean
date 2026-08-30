/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Support.Predicate.Uniform

/-!
# Quadratic support for ordinary semistable objects

This file binds the genuine quadratic-support interfaces to semistability in
an actual ordinary pre-stability condition.  The selected numerical locus is
the set of classes of nonzero objects in a slice `P(φ)`; callers cannot replace
it by an unrelated set.

`UniformQuadraticSupportData` is the fixed-category numerical core of the
uniform support condition in Definition 18.5, Lemma 18.6, and Definition
21.15(4) of arXiv:1902.08184v4.  One real-linear charge and one quadratic form
control every indexed member.  Varying geometric fiber categories, the
Definition 21.9 quotient, and boundedness remain separate layers.
-/

namespace CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap

open CategoryTheory Limits Pretriangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.Support

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {I J V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {v : K₀ C →+ V}

/-- Numerical classes of nonzero ordinary semistable objects, where
semistability means membership in one phase of the slicing. -/
def semistableClasses (σ : PreStabilityCondition.WithClassMap C v) : Set V :=
  {x | ∃ (φ : ℝ) (E : C), σ.slicing.P φ E ∧ ¬IsZero E ∧ x = v (K₀.of C E)}

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Membership in the ordinary semistable locus exposes the phase and object
that produced the numerical class. -/
theorem mem_semistableClasses_iff
    (σ : PreStabilityCondition.WithClassMap C v) (x : V) :
    x ∈ σ.semistableClasses ↔
      ∃ (φ : ℝ) (E : C), σ.slicing.P φ E ∧ ¬IsZero E ∧ x = v (K₀.of C E) :=
  Iff.rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A nonzero object in a slice contributes its class to the ordinary
semistable locus. -/
theorem class_mem_semistableClasses
    (σ : PreStabilityCondition.WithClassMap C v) {φ : ℝ} {E : C}
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    v (K₀.of C E) ∈ σ.semistableClasses :=
  ⟨φ, E, hP, hE, rfl⟩

/-- The norm-bound support property for the actual ordinary semistable
locus. -/
def HasSupportProperty (σ : PreStabilityCondition.WithClassMap C v)
    (Zlin : V →ₗ[ℝ] ℂ) : Prop :=
  CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasSupportProperty Zlin
    σ.semistableClasses

/-- Genuine quadratic support for one ordinary pre-stability condition,
together with identification of its additive and real-linear charges. -/
structure QuadraticSupportData (σ : PreStabilityCondition.WithClassMap C v)
    (Zlin : V →ₗ[ℝ] ℂ) : Prop where
  /-- The real-linear charge realizes the pre-stability condition's central
  charge on the full class space. -/
  charge_compatible : ∀ x : V, Zlin x = σ.Z x
  /-- One genuine quadratic form has the required signs on the ordinary
  semistable locus and the kernel of the same charge. -/
  quadratic :
    CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasQuadraticSupportProperty
      Zlin σ.semistableClasses

/-- Genuine quadratic support implies the norm-bound support property on the
same ordinary semistable locus. -/
theorem QuadraticSupportData.hasSupportProperty
    {σ : PreStabilityCondition.WithClassMap C v} {Zlin : V →ₗ[ℝ] ℂ}
    (h : σ.QuadraticSupportData Zlin) : σ.HasSupportProperty Zlin :=
  h.quadratic.hasSupportProperty

/-- A single charge and a single quadratic form controlling an indexed family
of ordinary pre-stability conditions on the same category and class space. -/
structure UniformQuadraticSupportData
    (σ : I → PreStabilityCondition.WithClassMap C v)
    (Zlin : V →ₗ[ℝ] ℂ) : Prop where
  /-- Every indexed central charge is the same fixed charge on classes. -/
  charge_compatible : ∀ i (x : V), Zlin x = (σ i).Z x
  /-- One quadratic form controls every indexed ordinary semistable locus. -/
  quadratic :
    CategoryTheory.Triangulated.WeakStabilityCondition.Support.HasUniformQuadraticSupportProperty
      Zlin (fun i => (σ i).semistableClasses)

omit [FiniteDimensional ℝ V] in
/-- Restrict a uniform ordinary support package to one index. -/
theorem UniformQuadraticSupportData.fiber
    {σ : I → PreStabilityCondition.WithClassMap C v} {Zlin : V →ₗ[ℝ] ℂ}
    (h : UniformQuadraticSupportData σ Zlin) (i : I) :
    (σ i).QuadraticSupportData Zlin :=
  ⟨h.charge_compatible i, h.quadratic.fiber i⟩

omit [FiniteDimensional ℝ V] in
/-- Reindex a uniformly supported ordinary family without changing its charge
or quadratic form. -/
theorem UniformQuadraticSupportData.reindex
    {σ : I → PreStabilityCondition.WithClassMap C v} {Zlin : V →ₗ[ℝ] ℂ}
    (h : UniformQuadraticSupportData σ Zlin) (f : J → I) :
    UniformQuadraticSupportData (fun j => σ (f j)) Zlin :=
  ⟨fun j => h.charge_compatible (f j), h.quadratic.reindex f⟩

omit [FiniteDimensional ℝ V] in
/-- One ordinary quadratic support package gives a uniform constant family. -/
theorem QuadraticSupportData.constant
    {σ : PreStabilityCondition.WithClassMap C v} {Zlin : V →ₗ[ℝ] ℂ}
    (h : σ.QuadraticSupportData Zlin) (I : Type*) :
    UniformQuadraticSupportData (fun _ : I => σ) Zlin :=
  ⟨fun _ => h.charge_compatible, h.quadratic.constant I⟩

end

end CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap
