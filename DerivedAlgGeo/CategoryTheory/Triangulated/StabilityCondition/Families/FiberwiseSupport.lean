/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Support.Semistable

/-!
# Uniform support on varying fiber categories

The ordinary support adapter in `Support.Semistable` indexes stability
conditions on one fixed triangulated category.  A family in the sense of
arXiv:1902.08184v4 instead has a category on every geometric fiber.  This file
removes that numerical fixed-category restriction: every index has its own
triangulated category, Grothendieck group, class map, and slicing, while all
classes land in one common real numerical space controlled by one charge and
one quadratic form.

This is still an abstract fiber family.  It does not provide a scheme, a
relative category, or base-change functors, and it makes no openness, relative
Harder--Narasimhan, or boundedness claim.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families

open CategoryTheory Limits Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.Support

noncomputable section

universe u

variable {I J V : Type*} {C : I → Type u}
  [∀ i : I, Category (C i)] [∀ i : I, Preadditive (C i)]
  [∀ i : I, HasZeroObject (C i)] [∀ i : I, HasShift (C i) ℤ]
  [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i : I, Pretriangulated (C i)]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {v : ∀ i, K₀ (C i) →+ V}

/-- The common numerical loci contributed by nonzero semistable objects in
the actual slicing on each fiber category. -/
def ordinaryFiberSemistableClasses
    (σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)) :
    I → Set V :=
  fun i => (σ i).semistableClasses

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Membership in a fiber locus exposes the phase and the object in that
fiber category which produced the common numerical class. -/
theorem mem_ordinaryFiberSemistableClasses_iff
    (σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i))
    (i : I) (x : V) :
    x ∈ ordinaryFiberSemistableClasses σ i ↔
      ∃ (φ : ℝ) (E : C i), (σ i).slicing.P φ E ∧
        ¬IsZero E ∧ x = v i (K₀.of (C i) E) :=
  Iff.rfl

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A nonzero object in a fiber slice contributes its class to that fiber's
selected numerical locus. -/
theorem class_mem_ordinaryFiberSemistableClasses
    (σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i))
    (i : I) {φ : ℝ} {E : C i}
    (hP : (σ i).slicing.P φ E) (hE : ¬IsZero E) :
    v i (K₀.of (C i) E) ∈ ordinaryFiberSemistableClasses σ i :=
  (σ i).class_mem_semistableClasses hP hE

/-- One real-linear charge and one genuine quadratic form controlling the
actual semistable loci of an indexed family of different fiber categories.

The common space `V` may itself be the real quotient supplied by the
Definition 21.9 comparison layer. -/
structure OrdinaryFiberUniformQuadraticSupportData
    (σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i))
    (Zlin : V →ₗ[ℝ] ℂ) : Prop where
  /-- Every fiber central charge is realized by the same charge on the common
  numerical space. -/
  charge_compatible : ∀ i (x : V), Zlin x = (σ i).Z x
  /-- One quadratic form controls every slicing-defined fiber locus. -/
  quadratic : HasUniformQuadraticSupportProperty Zlin
    (ordinaryFiberSemistableClasses σ)

omit [FiniteDimensional ℝ V] in
/-- Restrict varying-fiber uniform support to one actual fiber category. -/
theorem OrdinaryFiberUniformQuadraticSupportData.fiber
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    {Zlin : V →ₗ[ℝ] ℂ}
    (h : OrdinaryFiberUniformQuadraticSupportData σ Zlin) (i : I) :
    (σ i).QuadraticSupportData Zlin :=
  ⟨h.charge_compatible i, h.quadratic.fiber i⟩

omit [FiniteDimensional ℝ V] in
/-- Reindex a varying family without changing its common charge or quadratic
form. -/
theorem OrdinaryFiberUniformQuadraticSupportData.reindex
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    {Zlin : V →ₗ[ℝ] ℂ}
    (h : OrdinaryFiberUniformQuadraticSupportData σ Zlin) (f : J → I) :
    OrdinaryFiberUniformQuadraticSupportData
      (C := fun j => C (f j)) (v := fun j => v (f j))
      (fun j => σ (f j)) Zlin :=
  ⟨fun j => h.charge_compatible (f j), h.quadratic.reindex f⟩

omit [FiniteDimensional ℝ V] in
/-- One ordinary supported category gives the constant varying-fiber model.
This witnesses the dependent interface without using an empty index type. -/
theorem ordinaryFiberUniformQuadraticSupportData_constant
    {C₀ : Type u} [Category C₀] [Preadditive C₀] [HasZeroObject C₀]
    [HasShift C₀ ℤ] [∀ n : ℤ, (shiftFunctor C₀ n).Additive]
    [Pretriangulated C₀] {v₀ : K₀ C₀ →+ V}
    {σ : PreStabilityCondition.WithClassMap C₀ v₀}
    {Zlin : V →ₗ[ℝ] ℂ} (h : σ.QuadraticSupportData Zlin)
    (I : Type*) :
    OrdinaryFiberUniformQuadraticSupportData
      (I := I) (C := fun _ => C₀) (v := fun _ => v₀)
      (fun _ => σ) Zlin :=
  ⟨fun _ => h.charge_compatible, h.quadratic.constant I⟩

omit [FiniteDimensional ℝ V] in
/-- The inhabited `PUnit` specialization of the constant fiber family. -/
theorem ordinaryFiberUniformQuadraticSupportData_punit
    {C₀ : Type u} [Category C₀] [Preadditive C₀] [HasZeroObject C₀]
    [HasShift C₀ ℤ] [∀ n : ℤ, (shiftFunctor C₀ n).Additive]
    [Pretriangulated C₀] {v₀ : K₀ C₀ →+ V}
    {σ : PreStabilityCondition.WithClassMap C₀ v₀}
    {Zlin : V →ₗ[ℝ] ℂ} (h : σ.QuadraticSupportData Zlin) :
    OrdinaryFiberUniformQuadraticSupportData
      (I := PUnit) (C := fun _ => C₀) (v := fun _ => v₀)
      (fun _ => σ) Zlin :=
  ordinaryFiberUniformQuadraticSupportData_constant h PUnit

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families
