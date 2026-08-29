/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Families.BaseChange
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Phase.Transfer.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Support.Semistable

/-!
# Fiber pre-stability conditions and categorical base change

This file binds actual pre-stability conditions on the fibers of a
`TriangulatedFiberFamily` to its pullback functors.  The compatibility package
requires the precise non-formal witness which turns the inverse-image phase
collection into a slicing, equality with the target-fiber slicing, and
compatibility of both numerical class maps and central charges.

The package does not construct the `Slicing.PreimageData` witnesses from
geometry.  In particular, it supplies no family of schemes, derived pullback
construction, relative Harder--Narasimhan theorem, openness, or boundedness.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe u v w uV

namespace CategoryTheory.Triangulated.StabilityCondition.Families

variable {B : Type u} [Category.{v} B]

/-- Fiber pre-stability conditions whose slicings and common numerical data
are compatible with every categorical pullback functor. -/
structure FiberPreStabilityBaseChangeData
    (F : TriangulatedFiberFamily (B := B))
    {V : Type uV} [AddCommGroup V]
    (classMap : ∀ b, K₀ (F.Fiber b) →+ V)
    (sigma : ∀ b, PreStabilityCondition.WithClassMap (F.Fiber b) (classMap b)) : Prop where
  /-- The common numerical class is invariant under pullback. -/
  classMap_compatible : F.CompatibleClassMaps V classMap
  /-- Every fiber uses the same central charge on the common class group. -/
  charge_compatible : ∀ {s t} (_ : s ⟶ t), (sigma s).Z = (sigma t).Z
  /-- Pullback admits the non-formal Hom-vanishing and HN data needed to
  construct the inverse-image slicing. -/
  preimageData : ∀ {s t} (f : s ⟶ t),
    (sigma s).slicing.PreimageData (F.pull f)
  /-- The target-fiber slicing is exactly the inverse image of the
  source-fiber slicing along pullback. -/
  slicing_compatible : ∀ {s t} (f : s ⟶ t),
    (sigma t).slicing =
      (sigma s).slicing.preimage (F.pull f) (preimageData f)

namespace FiberPreStabilityBaseChangeData

variable {F : TriangulatedFiberFamily (B := B)}
  {V : Type uV} [AddCommGroup V]
  {classMap : ∀ b, K₀ (F.Fiber b) →+ V}
  {sigma : ∀ b, PreStabilityCondition.WithClassMap (F.Fiber b) (classMap b)}

/-- An object lies in a target-fiber phase exactly when its pullback lies in
the corresponding source-fiber phase. -/
theorem phase_iff (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {s t : B} (f : s ⟶ t) (phi : ℝ) (E : F.Fiber t) :
    (sigma t).slicing.P phi E ↔
      (sigma s).slicing.P phi ((F.pull f).obj E) := by
  rw [h.slicing_compatible f]
  exact Slicing.preimage_P _ _ _ _ _

/-- The witnesses attached to two successive base changes compose to a
witness for the corresponding composite of pullback functors.  This uses the
strictly typed iterated functor; comparison with `F.pull (f ≫ g)` is supplied
separately by the functoriality of the underlying category-valued family. -/
theorem preimageData_comp (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {r s t : B} (f : r ⟶ s) (g : s ⟶ t) :
    (sigma r).slicing.PreimageData (F.pull g ⋙ F.pull f) := by
  let hg : ((sigma r).slicing.preimage (F.pull f) (h.preimageData f)).PreimageData
      (F.pull g) := by
    rw [← h.slicing_compatible f]
    exact h.preimageData g
  exact (h.preimageData f).comp hg

/-- The slicing over the target of two successive base changes can be
constructed in one step along the composite pullback functor. -/
theorem slicing_compatible_comp
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {r s t : B} (f : r ⟶ s) (g : s ⟶ t) :
    (sigma t).slicing =
      (sigma r).slicing.preimage (F.pull g ⋙ F.pull f)
        (h.preimageData_comp f g) := by
  apply Slicing.ext
  funext phi E
  apply propext
  exact (h.phase_iff g phi E).trans
    (h.phase_iff f phi ((F.pull g).obj E))

/-- Phase membership transported through a composite base change agrees with
transport through its two stages. -/
theorem phase_iff_comp (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {r s t : B} (f : r ⟶ s) (g : s ⟶ t) (phi : ℝ) (E : F.Fiber t) :
    (sigma t).slicing.P phi E ↔
      (sigma r).slicing.P phi ((F.pull f).obj ((F.pull g).obj E)) :=
  (h.phase_iff g phi E).trans
    (h.phase_iff f phi ((F.pull g).obj E))

/-- Pullback preserves the common numerical class of an object. -/
theorem class_pull (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {s t : B} (f : s ⟶ t) (E : F.Fiber t) :
    classMap s (K₀.of _ ((F.pull f).obj E)) =
      classMap t (K₀.of _ E) :=
  h.classMap_compatible.class_pull f E

/-- Pullback preserves the central charge of an object. -/
theorem charge_pull (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {s t : B} (f : s ⟶ t) (E : F.Fiber t) :
    (sigma s).charge ((F.pull f).obj E) = (sigma t).charge E := by
  rw [PreStabilityCondition.WithClassMap.charge_def,
    PreStabilityCondition.WithClassMap.charge_def, h.charge_compatible f]
  exact congrArg (sigma t).Z (h.class_pull f E)

/-- One pre-stability condition supplies the constant base-change model. -/
theorem constant (C : Type w) [Category.{w} C] [Preadditive C]
    [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (V : Type*) [AddCommGroup V] (v₀ : K₀ C →+ V)
    (sigma₀ : PreStabilityCondition.WithClassMap C v₀) :
    FiberPreStabilityBaseChangeData
      (TriangulatedFiberFamily.constant B C) (fun _ ↦ v₀) (fun _ ↦ sigma₀) where
  classMap_compatible :=
    TriangulatedFiberFamily.CompatibleClassMaps.constant C V v₀
  charge_compatible := fun _ ↦ rfl
  preimageData := fun _ ↦ by
    change sigma₀.slicing.PreimageData (Functor.id C)
    exact sigma₀.slicing.preimageData_id
  slicing_compatible := fun _ ↦ by
    change sigma₀.slicing =
      sigma₀.slicing.preimage (Functor.id C) sigma₀.slicing.preimageData_id
    exact sigma₀.slicing.preimage_id.symm

variable {W : Type uV} [NormedAddCommGroup W]
  {classMap' : ∀ b, K₀ (F.Fiber b) →+ W}
  {sigma' : ∀ b, PreStabilityCondition.WithClassMap (F.Fiber b) (classMap' b)}

/-- A target-fiber semistable object whose pullback remains nonzero contributes
the same common class to the source-fiber semistable locus. -/
theorem class_mem_semistableClasses_pull
    (h : FiberPreStabilityBaseChangeData F classMap' sigma')
    {s t : B} (f : s ⟶ t) {phi : ℝ} {E : F.Fiber t}
    (hP : (sigma' t).slicing.P phi E)
    (hE : ¬IsZero ((F.pull f).obj E)) :
    classMap' t (K₀.of _ E) ∈ (sigma' s).semistableClasses := by
  rw [← h.class_pull f E]
  exact (sigma' s).class_mem_semistableClasses ((h.phase_iff f phi E).mp hP) hE

end FiberPreStabilityBaseChangeData

end CategoryTheory.Triangulated.StabilityCondition.Families
