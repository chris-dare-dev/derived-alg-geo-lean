/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FiniteType
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.GeometricBaseChange
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.RelativeHN
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.SchemeSemistableLocus

/-!
# Finite-type openness and relative HN consequences

This file discharges the scheme-facing openness and relative-HN interfaces
from the geometric bounded-coherent base-change witness.

The finite-type condition is the standard scheme-theoretic one: a structure
morphism is locally of finite type and quasi-compact.  It is recorded on the
actual object of `Over S`, not as a caller-chosen eligibility label.

The input is `GeometricPreStabilityBaseChangeData`, constructed from genuine
bounded coherent pullback and the phase-indexed output of the owned Appendix-A
inducing theorem.  Its exported phase equivalence has two consequences.

* Residue-fiber phase membership is independent of the point, so each actual
  semistable locus is either the whole finite-type base change or empty and is
  Zariski open.  Generic openness uses the same open locus.
* The HN filtration supplied by the slicing over a regular curve base pulls
  to every residue fiber.  This constructs `SchemeRelativeHNFiltration`
  objectwise, including its existing length, phase, factor, and further
  base-change compatibility.

No openness proposition or relative-HN existence proposition is an input.
The finite-type proofs are not needed after restricting the quantifiers,
because the geometric phase equivalence proves the stronger all-base-change
statement.  This is a consequence of the deliberately strong strict-family
interface; it is not a formalization of semistable reduction, a moduli-space
construction, or Theorem 22.2 of arXiv:1902.08184v4.
-/

namespace AlgebraicGeometry.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Triangulated.WeakStabilityCondition.Families

noncomputable section

universe u uV

/-- A semistable-locus index whose actual structure morphism is of finite
type. -/
structure FiniteTypeSchemeSemistableLocusIndex {S : Scheme.{u}}
    (F : SchemeTriangulatedFiberFamily S) where
  /-- The actual object, phase, and family object being tested. -/
  index : SchemeSemistableLocusIndex F
  /-- The structure morphism is locally of finite type and quasi-compact. -/
  finiteType : IsFiniteTypeBaseChange index.baseChange

/-- A generic semistable-locus index on an actual finite-type base change. -/
structure FiniteTypeSchemeGenericSemistableLocusIndex {S : Scheme.{u}}
    (F : SchemeTriangulatedFiberFamily S) where
  /-- The actual locus and distinguished point. -/
  index : SchemeGenericSemistableLocusIndex F
  /-- The structure morphism is locally of finite type and quasi-compact. -/
  finiteType : IsFiniteTypeBaseChange index.index.baseChange

/-- A regular curve base change is eligible for the finite-type relative-HN
statement precisely when its structure morphism is of finite type. -/
def finiteTypeRegularCurveEligible {S : Scheme.{u}}
    (T : RegularCurveBaseChange S) : Prop :=
  IsFiniteTypeBaseChange T.baseChange

variable {S : Scheme.{u}} {F : SchemeTriangulatedFiberFamily S}
  [∀ T : SchemeBaseChange S, IsLocallyNoetherian T.left]
  [∀ {T U : SchemeBaseChange S} (f : T ⟶ U),
    SchemeBaseChange.HasCoherentPullback f]
  {R : BoundedCoherentDerivedRealization F}
  {V : Type uV} [AddCommGroup V]
  {classMap : ∀ T, K₀ (F.Fiber T) →+ V}
  {sigma : ∀ T, PreStabilityCondition.WithClassMap
    (F.Fiber T) (classMap T)}

/-- Every semistable locus on an actual finite-type base change is Zariski
open, with no openness conclusion supplied by the caller. -/
theorem finiteTypeSchemeSemistableLocus_isOpen
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma)
    (j : FiniteTypeSchemeSemistableLocusIndex F) :
    _root_.IsOpen (schemeSemistableLocus F classMap sigma j.index) :=
  schemeSemistableLocus_isOpen h.toFiberPreStabilityBaseChangeData j.index

/-- Universal openness restricted to actual finite-type scheme base changes. -/
theorem universalFiniteTypeSchemeSemistableOpenness
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma) :
    UniversalOpenness
      (fun j : FiniteTypeSchemeSemistableLocusIndex F ↦
        schemeSemistableOpenProbe F classMap sigma j.index) :=
  fun j ↦ (schemeSemistableOpenProbe_isOpen_iff F classMap sigma j.index).2
    (finiteTypeSchemeSemistableLocus_isOpen h j)

/-- Generic openness is obtained from the same Zariski-open semistable locus,
not from a separate generic-openness premise. -/
theorem finiteTypeSchemeGenericSemistabilityProbe_isGenericallyOpen
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma)
    (j : FiniteTypeSchemeGenericSemistableLocusIndex F) :
    (schemeGenericSemistabilityProbe F classMap sigma j.index).IsGenericallyOpen :=
  schemeGenericSemistabilityProbe_isGenericallyOpen
    h.toFiberPreStabilityBaseChangeData j.index

/-- Universal generic openness on actual finite-type scheme base changes. -/
theorem universalFiniteTypeSchemeGenericSemistabilityOpenness
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma) :
    UniversalGenericOpenness
      (fun j : FiniteTypeSchemeGenericSemistableLocusIndex F ↦
        schemeGenericSemistabilityProbe F classMap sigma j.index) :=
  fun j ↦ finiteTypeSchemeGenericSemistabilityProbe_isGenericallyOpen h j

/-- Construct an actual relative HN filtration for one object over an eligible
regular finite-type curve.  The ordinary HN filtration comes from the slicing;
the geometric witness constructs all residue-fiber filtrations and their
compatibility. -/
noncomputable def finiteTypeSchemeRelativeHNFiltration
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma)
    (T : RegularCurveBaseChange S) (_ : finiteTypeRegularCurveEligible T)
    (E : F.Fiber T.baseChange) :
    SchemeRelativeHNFiltration F classMap sigma E :=
  SchemeRelativeHNFiltration.ofBaseChangeWitness
    ((sigma T.baseChange).slicing.hn_exists E).some
    h.toFiberPreStabilityBaseChangeData

/-- The geometric bounded-coherent witness supplies objectwise relative HN
existence on every regular finite-type curve base change. -/
theorem hasFiniteTypeSchemeRelativeHNFiltrations
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma) :
    HasSchemeRelativeHNFiltrations F classMap sigma
      finiteTypeRegularCurveEligible := by
  intro T hT E
  exact ⟨finiteTypeSchemeRelativeHNFiltration h T hT E⟩

/-- Consequently every regular finite-type curve base change integrates the
existing object-level relative-HN problem, without accepting
`HasSchemeRelativeHNFiltrations` as an input. -/
theorem integratesAfterFiniteTypeRegularCurveBaseChange
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma) :
    IntegratesAfterDedekindBaseChange
      (schemeRelativeHNProblem F classMap sigma
        finiteTypeRegularCurveEligible) :=
  integratesAfterDedekindBaseChange_of_relativeHN F classMap sigma
    (hasFiniteTypeSchemeRelativeHNFiltrations h)

/-- The three finite-type geometric conclusions exported together.  This is
an output package; none of its fields is assumed by the construction theorem
below. -/
structure FiniteTypeGeometricConsequences
    {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)
    {V : Type uV} [AddCommGroup V]
    (classMap : ∀ T, K₀ (F.Fiber T) →+ V)
    (sigma : ∀ T, PreStabilityCondition.WithClassMap
      (F.Fiber T) (classMap T)) : Prop where
  /-- Zariski openness of all actual finite-type semistable loci. -/
  semistableOpenness : UniversalOpenness
    (fun j : FiniteTypeSchemeSemistableLocusIndex F ↦
      schemeSemistableOpenProbe F classMap sigma j.index)
  /-- Generic openness derived from those same loci. -/
  genericOpenness : UniversalGenericOpenness
    (fun j : FiniteTypeSchemeGenericSemistableLocusIndex F ↦
      schemeGenericSemistabilityProbe F classMap sigma j.index)
  /-- Objectwise relative HN existence on regular finite-type curves. -/
  relativeHN : HasSchemeRelativeHNFiltrations F classMap sigma
    finiteTypeRegularCurveEligible

/-- Construct every finite-type geometric consequence from the previously
built bounded-coherent base-change input. -/
theorem GeometricPreStabilityBaseChangeData.finiteTypeConsequences
    (h : GeometricPreStabilityBaseChangeData F R classMap sigma) :
    FiniteTypeGeometricConsequences F classMap sigma where
  semistableOpenness := universalFiniteTypeSchemeSemistableOpenness h
  genericOpenness := universalFiniteTypeSchemeGenericSemistabilityOpenness h
  relativeHN := hasFiniteTypeSchemeRelativeHNFiltrations h

end

end AlgebraicGeometry.StabilityCondition.Families
