/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Basic.Complex.Basic
import DerivedAlgGeo.CategoryTheory.Moduli.Boundedness
import DerivedAlgGeo.CategoryTheory.Moduli.Probes

/-!
# Input conditions for stability conditions in families

This file bundles the clauses of Definition 20.5 of arXiv:1902.08184v4 which
make sense without schemes, derived categories over a base, or moduli stacks.
The probes they are stated in (`ChargeProbe`, `OpenLocusProbe`,
`GenericSemistabilityProbe`, `DedekindHNProblem` and `WeakDedekindHNProblem`,
with their predicates) are neutral family vocabulary: they live in
`DerivedAlgGeo.CategoryTheory.Moduli.Probes`, which this file imports and
re-exports, and keep this namespace.  The generic `BoundednessProblem`
interface names the moduli problems whose boundedness is required by
Definition 21.15(5).

* `OrdinaryFamilyConditions` bundles clauses (1), (2) and (3);
* `WeakFamilyConditions` bundles clauses (1), (2') and (3').

A caller supplies *all* geometric tests, so these bundles prove no geometric
theorem.  Deliberately constant, full-locus, and proposition-only inhabitants
are kept out of this stable module.  Compile-only demonstrations of logical
inhabitance live under
`DerivedAlgGeo.Development.StabilityCondition.Families.Scaffolding`.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.Families

universe u₁ u₂ u₃

/-- The three ordinary clauses of Definition 20.5, kept as separately named
fields so a review can inspect their quantifier boundaries independently. -/
structure OrdinaryFamilyConditions
    {JCharge : Type u₁} {JOpen : Type u₂} {D : Type u₃}
    (charge : JCharge → ChargeProbe ℂ)
    (stable : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D) : Prop where
  /-- Definition 20.5(1). -/
  locallyConstantCharge : UniversallyLocallyConstantCharge charge
  /-- Definition 20.5(2). -/
  opennessOfGeometricStability : UniversalOpenness stable
  /-- Definition 20.5(3). -/
  dedekindHN : IntegratesAfterDedekindBaseChange dedekind

/-- The topological and relative-HN parts of the weak variant of Definition
20.5.  Clause (0), which refers to an actual weak stability function, is
bound to the repository's weak API in `Families.Weak`. -/
structure WeakFamilyConditions
    {JCharge : Type u₁} {JGeneric : Type u₂} {D : Type u₃}
    (charge : JCharge → ChargeProbe ℂ)
    (semistable : JGeneric → GenericSemistabilityProbe)
    (dedekind : WeakDedekindHNProblem D) : Prop where
  /-- Definition 20.5(1). -/
  locallyConstantCharge : UniversallyLocallyConstantCharge charge
  /-- Definition 20.5(2'). -/
  genericOpennessOfSemistability : UniversalGenericOpenness semistable
  /-- Definition 20.5(3'). -/
  dedekindWeakHN : WeakIntegratesAfterDedekindBaseChange dedekind

end CategoryTheory.Triangulated.WeakStabilityCondition.Families
