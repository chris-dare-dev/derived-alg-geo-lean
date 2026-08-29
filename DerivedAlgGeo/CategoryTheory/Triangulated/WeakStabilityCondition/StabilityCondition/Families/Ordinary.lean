/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Support.Predicate.Quotient

/-!
# Ordinary stability-in-families interface

This file combines the three ordinary clauses of Definition 20.5 with the
uniform support and boundedness clauses (4)--(5) of Definition 21.15 of
arXiv:1902.08184v4.  It is the top-level ordinary abstract family package.

The index types stand for geometric base-change, object, fiber, and numerical
moduli tests supplied by a client.  The library neither constructs nor
recognizes those geometric objects.  The support field, by contrast, is the
genuine quotient-uniform quadratic support predicate already implemented in
the support subsystem.  Vacuous-probe inhabitants -- constant-true
predicates and full-locus witnesses -- are development scaffolding, not part
of this stable interface; constant-family reindexings that consume a genuine
support datum remain stable API.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory.Triangulated.StabilityCondition.Support

noncomputable section

variable {JCharge JOpen D I M V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private local instance quotientSubmoduleClosed (V₀ : Submodule ℝ V) :
    IsClosed (V₀ : Set V) :=
  V₀.closed_of_finiteDimensional

/-- The five separately auditable ordinary family conditions: Definition
20.5(1)--(3) followed by Definition 21.15(4)--(5). -/
structure OrdinaryStabilityInFamiliesData
    (charge : JCharge → ChargeProbe ℂ)
    (stable : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] W)
    (hV₀ : V₀ ≤ LinearMap.ker Z) (semistableClasses : I → Set V)
    (boundedness : BoundednessProblem M) : Prop where
  /-- Definition 20.5(1)--(3). -/
  definition20_5 : OrdinaryDefinition20_5Conditions charge stable dedekind
  /-- Definition 21.15(4). -/
  uniformSupport : HasUniformQuadraticSupportPropertyModulo
    V₀ Z hV₀ semistableClasses
  /-- Definition 21.15(5). -/
  bounded : UniversalBoundedness boundedness

/-- The geometric and numerical input conditions used by deformation
arguments: openness, relative HN integration, uniform quotient support, and
boundedness.  The theorem consuming these inputs is deliberately not named or
indexed here. -/
structure OrdinaryDeformationInputConditions
    (stable : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] W)
    (hV₀ : V₀ ≤ LinearMap.ker Z) (semistableClasses : I → Set V)
    (boundedness : BoundednessProblem M) : Prop where
  /-- Universal openness of geometric stability. -/
  openness : UniversalOpenness stable
  /-- Relative HN structures after every eligible Dedekind base change. -/
  dedekindHN : IntegratesAfterDedekindBaseChange dedekind
  /-- One quotient quadratic form controls every fiber semistable locus. -/
  uniformSupport : HasUniformQuadraticSupportPropertyModulo
    V₀ Z hV₀ semistableClasses
  /-- Every supplied numerical moduli problem is bounded. -/
  bounded : UniversalBoundedness boundedness

end

end CategoryTheory.Triangulated.StabilityCondition.Families
