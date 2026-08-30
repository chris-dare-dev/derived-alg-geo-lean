/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Semistability.Locus
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families.Instances.AlgebraicGeometry.Scheme

/-!
# Scheme semistable loci as categorical openness probes

The pointwise locus and its Zariski theorems are geometry-owned. This opt-in
leaf realizes the weak-family `OpenLocusProbe`,
`GenericSemistabilityProbe`, and universal openness interfaces.
-/

namespace AlgebraicGeometry.Moduli.Semistability
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Triangulated.WeakStabilityCondition.Families
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families

noncomputable section

universe u w uV

variable {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)
  {V : Type uV} [AddCommGroup V]
  (classMap : ∀ T, K₀ (F.Fiber T) →+ V)
  (sigma : ∀ T, PreStabilityCondition.WithClassMap (F.Fiber T) (classMap T))

/-- The openness probe attached to the actual residue-fiber semistable locus. -/
def schemeSemistableOpenProbe (j : SchemeSemistableLocusIndex F) :
    OpenLocusProbe :=
  OpenLocusProbe.ofScheme j.baseChange.left
    (schemeSemistableLocus F classMap sigma j)

/-- The generic-openness probe attached to the same semistable locus. -/
def schemeGenericSemistabilityProbe
    (j : SchemeGenericSemistableLocusIndex F) :
    GenericSemistabilityProbe :=
  GenericSemistabilityProbe.ofScheme j.index.baseChange.left j.genericPoint
    (schemeSemistableLocus F classMap sigma j.index)

@[simp]
theorem schemeSemistableOpenProbe_isOpen_iff
    (j : SchemeSemistableLocusIndex F) :
    (schemeSemistableOpenProbe F classMap sigma j).IsOpen ↔
      _root_.IsOpen (schemeSemistableLocus F classMap sigma j) :=
  OpenLocusProbe.ofScheme_isOpen_iff _ _

@[simp]
theorem schemeGenericSemistabilityProbe_isGenericallyOpen_iff
    (j : SchemeGenericSemistableLocusIndex F) :
    (schemeGenericSemistabilityProbe F classMap sigma j).IsGenericallyOpen ↔
      j.genericPoint ∈ schemeSemistableLocus F classMap sigma j.index →
        ∃ U : Set j.index.baseChange.left, _root_.IsOpen U ∧
          j.genericPoint ∈ U ∧
          U ⊆ schemeSemistableLocus F classMap sigma j.index :=
  GenericSemistabilityProbe.ofScheme_isGenericallyOpen_iff _ _ _

theorem universalSchemeSemistableOpenness_iff :
    UniversalOpenness
        (fun j : SchemeSemistableLocusIndex F ↦
          schemeSemistableOpenProbe F classMap sigma j) ↔
      ∀ j : SchemeSemistableLocusIndex F,
        _root_.IsOpen (schemeSemistableLocus F classMap sigma j) :=
  Iff.rfl

theorem universalSchemeGenericSemistabilityOpenness_iff :
    UniversalGenericOpenness
        (fun j : SchemeGenericSemistableLocusIndex F ↦
          schemeGenericSemistabilityProbe F classMap sigma j) ↔
      ∀ j : SchemeGenericSemistableLocusIndex F,
        j.genericPoint ∈ schemeSemistableLocus F classMap sigma j.index →
          ∃ U : Set j.index.baseChange.left, _root_.IsOpen U ∧
            j.genericPoint ∈ U ∧
            U ⊆ schemeSemistableLocus F classMap sigma j.index :=
  Iff.rfl

variable {F classMap sigma}

/-- Geometric base-change compatibility realizes universal openness. -/
theorem universalSchemeSemistableOpenness
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    UniversalOpenness
      (fun j : SchemeSemistableLocusIndex F ↦
        schemeSemistableOpenProbe F classMap sigma j) :=
  fun j ↦ (schemeSemistableOpenProbe_isOpen_iff F classMap sigma j).2
    (schemeSemistableLocus_isOpen h j)

/-- A Zariski-open semistable locus realizes the generic-openness probe. -/
theorem schemeGenericSemistabilityProbe_isGenericallyOpen
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    (j : SchemeGenericSemistableLocusIndex F) :
    (schemeGenericSemistabilityProbe F classMap sigma j).IsGenericallyOpen := by
  rw [schemeGenericSemistabilityProbe_isGenericallyOpen_iff]
  intro hj
  exact ⟨schemeSemistableLocus F classMap sigma j.index,
    schemeSemistableLocus_isOpen h j.index, hj, Set.Subset.rfl⟩

/-- Geometric base-change compatibility realizes universal generic openness. -/
theorem universalSchemeGenericSemistabilityOpenness
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    UniversalGenericOpenness
      (fun j : SchemeGenericSemistableLocusIndex F ↦
        schemeGenericSemistabilityProbe F classMap sigma j) :=
  fun j ↦ schemeGenericSemistabilityProbe_isGenericallyOpen h j

/-- The constant family realizes universal scheme semistable openness. -/
theorem universalSchemeSemistableOpenness_constant
    (S : Scheme.{u})
    (C : Type w) [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    (V : Type uV) [AddCommGroup V] (v₀ : K₀ C →+ V)
    (sigma₀ : PreStabilityCondition.WithClassMap C v₀) :
    UniversalOpenness
      (fun j : SchemeSemistableLocusIndex
          (SchemeTriangulatedFiberFamily.constant S C) ↦
        schemeSemistableOpenProbe (SchemeTriangulatedFiberFamily.constant S C)
          (fun _ ↦ v₀) (fun _ ↦ sigma₀) j) :=
  universalSchemeSemistableOpenness
    (FiberPreStabilityBaseChangeData.constant C V v₀ sigma₀)

/-- The constant family realizes universal generic openness. -/
theorem universalSchemeGenericSemistabilityOpenness_constant
    (S : Scheme.{u})
    (C : Type w) [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    (V : Type uV) [AddCommGroup V] (v₀ : K₀ C →+ V)
    (sigma₀ : PreStabilityCondition.WithClassMap C v₀) :
    UniversalGenericOpenness
      (fun j : SchemeGenericSemistableLocusIndex
          (SchemeTriangulatedFiberFamily.constant S C) ↦
        schemeGenericSemistabilityProbe
          (SchemeTriangulatedFiberFamily.constant S C)
          (fun _ ↦ v₀) (fun _ ↦ sigma₀) j) :=
  universalSchemeGenericSemistabilityOpenness
    (FiberPreStabilityBaseChangeData.constant C V v₀ sigma₀)

end

end AlgebraicGeometry.Moduli.Semistability
