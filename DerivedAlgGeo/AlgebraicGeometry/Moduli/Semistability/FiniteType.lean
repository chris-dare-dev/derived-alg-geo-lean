/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.FiniteType
import DerivedAlgGeo.AlgebraicGeometry.Moduli.HarderNarasimhan.DedekindProblem
import DerivedAlgGeo.AlgebraicGeometry.Moduli.Semistability.LocusProbes

/-!
# Finite-type openness and relative HN consequences

This file restricts the scheme-facing openness and relative-HN interfaces to
base changes of finite type, and discharges them from the categorical
base-change witness `FiberPreStabilityBaseChangeData`, the witness the
unrestricted forms in `Locus.lean`, `LocusProbes.lean` and
`HarderNarasimhan/RelativeFiltration.lean` already use.  No openness
proposition or relative-HN existence proposition is an input.

## Main definitions

* `Semistability.FiniteTypeSchemeSemistableLocusIndex` and
  `Semistability.FiniteTypeSchemeGenericSemistableLocusIndex`: semistable-locus
  and generic-locus indices whose actual base change is of finite type.
* `Semistability.finiteTypeRegularCurveEligible`: a regular curve base change
  whose structure morphism is of finite type.
* `Semistability.finiteTypeSchemeRelativeHNFiltration`: the relative HN
  filtration of one object over an eligible regular finite-type curve.
* `Semistability.FiniteTypeGeometricConsequences`: the three finite-type
  conclusions packaged together as an output.

## Main results

* `Semistability.finiteTypeSchemeSemistableLocus_isOpen` and
  `Semistability.universalFiniteTypeSchemeSemistableOpenness`: every semistable
  locus on an actual finite-type base change is Zariski open.
* `Semistability.finiteTypeSchemeGenericSemistabilityProbe_isGenericallyOpen` and
  `Semistability.universalFiniteTypeSchemeGenericSemistabilityOpenness`: generic
  openness from the same open loci.
* `Semistability.hasFiniteTypeSchemeRelativeHNFiltrations` and
  `Semistability.integratesAfterFiniteTypeRegularCurveBaseChange`: objectwise
  relative HN existence on every regular finite-type curve base change, and its
  integration after that base change.
* `Semistability.finiteTypeConsequences_of_fiberPreStabilityBaseChangeData`:
  all three conclusions from the categorical base-change witness.
* `Semistability.finiteTypeGeometricConsequences_constant`: the constant family
  over any scheme has all three, so the hypotheses above are satisfiable.

## Implementation notes

### The finite-type condition

The finite-type condition is the standard scheme-theoretic one: a structure
morphism is locally of finite type and quasi-compact.  It is recorded on the
actual object of `Over S`, not as a caller-chosen eligibility label.

### What the witness gives

`FiberPreStabilityBaseChangeData` identifies phase membership along every
morphism of base changes, residue maps included.  So residue-fibre phase
membership is independent of the point, and every semistable locus is either
empty or the whole base change (`schemeSemistableLocus_eq_univ_of_phase` and
`schemeSemistableLocus_eq_empty_of_not_phase`); generic openness uses the same
locus.  The HN filtration supplied by the slicing over a regular curve base
pulls to every residue fibre, which constructs `SchemeRelativeHNFiltration`
objectwise.

### Scope

The finite-type restriction is the reduction of Lemma 20.3 of
arXiv:1902.08184v4, which checks the universal properties on finite-type
morphisms from an affine scheme; under this witness it adds nothing, since the
unrestricted statements hold.  Openness in the sense of Definition 20.1(2) for
a genuine family, whose loci are neither empty nor everything, is not proved
here: Definition 20.5(2) makes it an axiom of a flat family of fibrewise
stability conditions.  The geometric witness
`GeometricPreStabilityBaseChangeHypotheses` quantifies only over morphisms with
exact coherent pullback, which residue maps rarely have, so it does not supply
`FiberPreStabilityBaseChangeData`.  Nor is this a formalization of semistable
reduction, a moduli-space construction, or Theorem 22.2 of arXiv:1902.08184v4.

## References

* arXiv:1902.08184v4, Definition 20.1(2), Lemma 20.3 and Definition 20.5(2).

## Tags

semistable locus, openness, finite type, relative Harder-Narasimhan filtration,
base change, stability condition
-/

namespace AlgebraicGeometry.Moduli.Semistability
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.Moduli.HarderNarasimhan

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Triangulated.WeakStabilityCondition.Families
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families

noncomputable section

universe u w uV

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
  {V : Type uV} [AddCommGroup V]
  {classMap : ∀ T, K₀ (F.Fiber T) →+ V}
  {sigma : ∀ T, PreStabilityCondition.WithClassMap
    (F.Fiber T) (classMap T)}

/-- Every semistable locus on an actual finite-type base change is Zariski
open, with no openness conclusion supplied by the caller. -/
theorem finiteTypeSchemeSemistableLocus_isOpen
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    (j : FiniteTypeSchemeSemistableLocusIndex F) :
    _root_.IsOpen (schemeSemistableLocus F classMap sigma j.index) :=
  schemeSemistableLocus_isOpen h j.index

/-- Universal openness restricted to actual finite-type scheme base changes. -/
theorem universalFiniteTypeSchemeSemistableOpenness
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    UniversalOpenness
      (fun j : FiniteTypeSchemeSemistableLocusIndex F ↦
        schemeSemistableOpenProbe F classMap sigma j.index) :=
  fun j ↦ (schemeSemistableOpenProbe_isOpen_iff F classMap sigma j.index).2
    (finiteTypeSchemeSemistableLocus_isOpen h j)

/-- Generic openness is obtained from the same Zariski-open semistable locus,
not from a separate generic-openness premise. -/
theorem finiteTypeSchemeGenericSemistabilityProbe_isGenericallyOpen
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    (j : FiniteTypeSchemeGenericSemistableLocusIndex F) :
    (schemeGenericSemistabilityProbe F classMap sigma j.index).IsGenericallyOpen :=
  schemeGenericSemistabilityProbe_isGenericallyOpen h j.index

/-- Universal generic openness on actual finite-type scheme base changes. -/
theorem universalFiniteTypeSchemeGenericSemistabilityOpenness
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    UniversalGenericOpenness
      (fun j : FiniteTypeSchemeGenericSemistableLocusIndex F ↦
        schemeGenericSemistabilityProbe F classMap sigma j.index) :=
  fun j ↦ finiteTypeSchemeGenericSemistabilityProbe_isGenericallyOpen h j

/-- Construct an actual relative HN filtration for one object over an eligible
regular finite-type curve.  The ordinary HN filtration comes from the slicing;
the base-change witness constructs all residue-fiber filtrations and their
compatibility. -/
noncomputable def finiteTypeSchemeRelativeHNFiltration
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    (T : RegularCurveBaseChange S) (_ : finiteTypeRegularCurveEligible T)
    (E : F.Fiber T.baseChange) :
    SchemeRelativeHNFiltration F classMap sigma E :=
  SchemeRelativeHNFiltration.ofBaseChangeWitness
    ((sigma T.baseChange).slicing.hn_exists E).some h

/-- The base-change witness supplies objectwise relative HN existence on every
regular finite-type curve base change. -/
theorem hasFiniteTypeSchemeRelativeHNFiltrations
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    HasSchemeRelativeHNFiltrations F classMap sigma
      finiteTypeRegularCurveEligible := by
  intro T hT E
  exact ⟨finiteTypeSchemeRelativeHNFiltration h T hT E⟩

/-- Consequently every regular finite-type curve base change integrates the
existing object-level relative-HN problem, without accepting
`HasSchemeRelativeHNFiltrations` as an input. -/
theorem integratesAfterFiniteTypeRegularCurveBaseChange
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    IntegratesAfterDedekindBaseChange
      (schemeRelativeHNProblem F classMap sigma
        finiteTypeRegularCurveEligible) :=
  integratesAfterDedekindBaseChange_of_relativeHN F classMap sigma
    (hasFiniteTypeSchemeRelativeHNFiltrations h)

/-- The three finite-type geometric conclusions exported together.  This is
an output package; none of its fields is assumed by the construction theorems
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

/-- Construct every finite-type geometric consequence from the categorical
base-change witness. -/
theorem finiteTypeConsequences_of_fiberPreStabilityBaseChangeData
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    FiniteTypeGeometricConsequences F classMap sigma where
  semistableOpenness := universalFiniteTypeSchemeSemistableOpenness h
  genericOpenness := universalFiniteTypeSchemeGenericSemistabilityOpenness h
  relativeHN := hasFiniteTypeSchemeRelativeHNFiltrations h

/-- The constant family over any scheme has every finite-type geometric
consequence, so the hypotheses of this file are satisfiable over every base. -/
theorem finiteTypeGeometricConsequences_constant (S : Scheme.{u})
    (C : Type w) [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    (V : Type uV) [AddCommGroup V] (v₀ : K₀ C →+ V)
    (sigma₀ : PreStabilityCondition.WithClassMap C v₀) :
    FiniteTypeGeometricConsequences (SchemeTriangulatedFiberFamily.constant S C)
      (fun _ ↦ v₀) (fun _ ↦ sigma₀) :=
  finiteTypeConsequences_of_fiberPreStabilityBaseChangeData
    (FiberPreStabilityBaseChangeData.constant C V v₀ sigma₀)

end

end AlgebraicGeometry.Moduli.Semistability
