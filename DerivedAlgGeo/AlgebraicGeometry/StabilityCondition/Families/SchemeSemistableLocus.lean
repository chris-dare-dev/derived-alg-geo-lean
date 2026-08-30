/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.PreStabilityBaseChange
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ResidueFiber
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.Scheme

/-!
# Scheme semistable loci

This file removes the arbitrary-set freedom from the scheme-facing openness
probes.  For an object over a scheme base change, its semistable locus is the
set of points where the actual pullback to the residue fiber belongs to the
chosen phase of the actual fiber slicing.  The associated openness and
generic-openness probes therefore use the Zariski topology of the scheme and
that definitionally fixed locus.

`FiberPreStabilityBaseChangeData` is a deliberately strong named geometric
hypothesis: it identifies every target slicing with the preimage slicing under
pullback.  Under that hypothesis, phase membership at the residue fibers is
equivalent to phase membership over the base change, so the locus is either
the whole scheme or empty and is therefore open.  The constant categorical
family supplies a concrete logically inhabited model of this implication.

No such compatibility witness is constructed here.  In particular, this file
does not assert exactness of arbitrary residue-field pullback, construct a
geometric inducing package, prove openness for an arbitrary family, construct
relative Harder--Narasimhan filtrations, or prove Theorem 22.2 of
arXiv:1902.08184v4.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Triangulated.WeakStabilityCondition.Families

noncomputable section

universe u w uV

/-- An object and a phase whose residue-fiber semistable locus is to be
measured on an actual scheme base change. -/
structure SchemeSemistableLocusIndex {S : Scheme.{u}}
    (F : SchemeTriangulatedFiberFamily S) where
  /-- The scheme base change carrying the object. -/
  baseChange : SchemeBaseChange S
  /-- The phase to test after pullback to every residue fiber. -/
  phase : ℝ
  /-- The object whose residue-fiber pullbacks are tested. -/
  object : F.Fiber baseChange

/-- A semistable-locus index together with a distinguished point at which the
generic-openness implication is tested.  Geometry may require this point to
be generic; that property remains an explicit responsibility of the caller. -/
structure SchemeGenericSemistableLocusIndex {S : Scheme.{u}}
    (F : SchemeTriangulatedFiberFamily S) where
  /-- The underlying object-and-phase index. -/
  index : SchemeSemistableLocusIndex F
  /-- The distinguished point used by the generic-openness probe. -/
  genericPoint : index.baseChange.left

variable {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)
  {V : Type uV} [AddCommGroup V]
  (classMap : ∀ T, K₀ (F.Fiber T) →+ V)
  (sigma : ∀ T, PreStabilityCondition.WithClassMap (F.Fiber T) (classMap T))

/-- The genuine pointwise semistable locus of a family object: membership is
phase membership of its actual pullback to the residue-field fiber. -/
def schemeSemistableLocus (j : SchemeSemistableLocusIndex F) :
    Set j.baseChange.left :=
  {x | (sigma (j.baseChange.residue x)).slicing.P j.phase
    ((F.pullToResidue j.baseChange x).obj j.object)}

@[simp]
theorem mem_schemeSemistableLocus_iff (j : SchemeSemistableLocusIndex F)
    (x : j.baseChange.left) :
    x ∈ schemeSemistableLocus F classMap sigma j ↔
      (sigma (j.baseChange.residue x)).slicing.P j.phase
        ((F.pullToResidue j.baseChange x).obj j.object) :=
  Iff.rfl

/-- The universal-openness probe attached to an actual residue-fiber
semistable locus on a scheme. -/
def schemeSemistableOpenProbe (j : SchemeSemistableLocusIndex F) :
    OpenLocusProbe :=
  OpenLocusProbe.ofScheme j.baseChange.left
    (schemeSemistableLocus F classMap sigma j)

/-- The generic-openness probe attached to the same actual residue-fiber
semistable locus. -/
def schemeGenericSemistabilityProbe
    (j : SchemeGenericSemistableLocusIndex F) :
    GenericSemistabilityProbe :=
  GenericSemistabilityProbe.ofScheme j.index.baseChange.left j.genericPoint
    (schemeSemistableLocus F classMap sigma j.index)

/-- Openness of the scheme probe is exactly Zariski openness of the actual
residue-fiber semistable locus. -/
@[simp]
theorem schemeSemistableOpenProbe_isOpen_iff
    (j : SchemeSemistableLocusIndex F) :
    (schemeSemistableOpenProbe F classMap sigma j).IsOpen ↔
      _root_.IsOpen (schemeSemistableLocus F classMap sigma j) :=
  OpenLocusProbe.ofScheme_isOpen_iff _ _

/-- Generic openness is exactly the existence of a Zariski-open neighborhood
inside the actual residue-fiber semistable locus. -/
@[simp]
theorem schemeGenericSemistabilityProbe_isGenericallyOpen_iff
    (j : SchemeGenericSemistableLocusIndex F) :
    (schemeGenericSemistabilityProbe F classMap sigma j).IsGenericallyOpen ↔
      j.genericPoint ∈ schemeSemistableLocus F classMap sigma j.index →
        ∃ U : Set j.index.baseChange.left, _root_.IsOpen U ∧
          j.genericPoint ∈ U ∧
          U ⊆ schemeSemistableLocus F classMap sigma j.index :=
  GenericSemistabilityProbe.ofScheme_isGenericallyOpen_iff _ _ _

/-- Universal openness for the scheme probes reduces to Zariski openness of
every definitionally fixed residue-fiber semistable locus. -/
theorem universalSchemeSemistableOpenness_iff :
    UniversalOpenness
        (fun j : SchemeSemistableLocusIndex F ↦
          schemeSemistableOpenProbe F classMap sigma j) ↔
      ∀ j : SchemeSemistableLocusIndex F,
        _root_.IsOpen (schemeSemistableLocus F classMap sigma j) :=
  Iff.rfl

/-- Universal generic openness likewise reduces to the Zariski-neighborhood
condition for the same actual loci. -/
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

/-- The geometric preimage-slicing witness identifies residue-fiber
membership with phase membership of the original family object. -/
theorem mem_schemeSemistableLocus_iff_of_baseChange
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    (j : SchemeSemistableLocusIndex F) (x : j.baseChange.left) :
    x ∈ schemeSemistableLocus F classMap sigma j ↔
      (sigma j.baseChange).slicing.P j.phase j.object :=
  (h.phase_iff (j.baseChange.residueTo x) j.phase j.object).symm

/-- Under the geometric preimage-slicing witness, a family object already in
the chosen phase has the full scheme as its residue-fiber semistable locus. -/
theorem schemeSemistableLocus_eq_univ_of_phase
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    (j : SchemeSemistableLocusIndex F)
    (hP : (sigma j.baseChange).slicing.P j.phase j.object) :
    schemeSemistableLocus F classMap sigma j = Set.univ := by
  ext x
  exact (mem_schemeSemistableLocus_iff_of_baseChange h j x).trans
    (iff_true_intro hP)

/-- Under the same witness, failure of phase membership makes the
residue-fiber semistable locus empty. -/
theorem schemeSemistableLocus_eq_empty_of_not_phase
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    (j : SchemeSemistableLocusIndex F)
    (hP : ¬(sigma j.baseChange).slicing.P j.phase j.object) :
    schemeSemistableLocus F classMap sigma j = ∅ := by
  ext x
  exact (mem_schemeSemistableLocus_iff_of_baseChange h j x).trans
    (iff_false_intro hP)

/-- A compatible geometric slicing family makes every actual semistable locus
Zariski open.  The conclusion follows from the explicit all-or-none statement,
not from a caller-supplied open set. -/
theorem schemeSemistableLocus_isOpen
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    (j : SchemeSemistableLocusIndex F) :
    _root_.IsOpen (schemeSemistableLocus F classMap sigma j) := by
  by_cases hP : (sigma j.baseChange).slicing.P j.phase j.object
  · rw [schemeSemistableLocus_eq_univ_of_phase h j hP]
    exact isOpen_univ
  · rw [schemeSemistableLocus_eq_empty_of_not_phase h j hP]
    exact isOpen_empty

/-- The named geometric base-change witness supplies universal openness for
all of the actual scheme semistable probes. -/
theorem universalSchemeSemistableOpenness
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    UniversalOpenness
      (fun j : SchemeSemistableLocusIndex F ↦
        schemeSemistableOpenProbe F classMap sigma j) :=
  fun j ↦ (schemeSemistableOpenProbe_isOpen_iff F classMap sigma j).2
    (schemeSemistableLocus_isOpen h j)

/-- The same Zariski-open locus supplies the open neighborhood required by
the generic-semistability probe. -/
theorem schemeGenericSemistabilityProbe_isGenericallyOpen
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    (j : SchemeGenericSemistableLocusIndex F) :
    (schemeGenericSemistabilityProbe F classMap sigma j).IsGenericallyOpen := by
  rw [schemeGenericSemistabilityProbe_isGenericallyOpen_iff]
  intro hj
  exact ⟨schemeSemistableLocus F classMap sigma j.index,
    schemeSemistableLocus_isOpen h j.index, hj, Set.Subset.rfl⟩

/-- The named geometric base-change witness also supplies universal generic
openness for the actual scheme semistable loci. -/
theorem universalSchemeGenericSemistabilityOpenness
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    UniversalGenericOpenness
      (fun j : SchemeGenericSemistableLocusIndex F ↦
        schemeGenericSemistabilityProbe F classMap sigma j) :=
  fun j ↦ schemeGenericSemistabilityProbe_isGenericallyOpen h j

/-- The constant categorical family is a logically inhabited model of the
universal Zariski-openness theorem.  Its loci are still computed from actual
residue-fiber pullback and slicing membership. -/
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

/-- The constant categorical family also inhabits universal generic
openness, with the distinguished points supplied by the genuine scheme
indices. -/
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

end CategoryTheory.Triangulated.StabilityCondition.Families
