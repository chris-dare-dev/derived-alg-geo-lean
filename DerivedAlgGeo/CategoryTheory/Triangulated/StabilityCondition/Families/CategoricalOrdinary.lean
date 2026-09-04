/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.FiberwiseOrdinary
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.PreStabilityBaseChange

/-!
# Ordinary stability conditions on a categorical family

This file joins the five-clause ordinary stability-in-families interface to
one contravariant family of triangulated categories.  The resulting package
contains both the existing source-clause data and compatibility of its actual
fiber pre-stability conditions under the categorical pullback functors.

This remains an abstract adapter.  It does not construct a family of schemes,
derived pullback, the required preimage/HN witnesses from geometry, relative
Harder--Narasimhan structures, openness, boundedness, or a moduli space, and it
does not assert a deformation-theoretic conclusion.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families

open CategoryTheory Limits Pretriangulated
open CategoryTheory.Moduli
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.Families
open CategoryTheory.Triangulated.WeakStabilityCondition.Support
open CategoryTheory.Triangulated.WeakStabilityCondition.Families

noncomputable section

universe u v w uV

variable {B : Type u} [Category.{v} B]
variable {JCharge JOpen D M : Type*}
variable (F : TriangulatedFiberFamily (B := B))
  {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
  (classMap : ∀ b, K₀ (F.Fiber b) →+ V)
  (sigma : ∀ b, PreStabilityCondition.WithClassMap (F.Fiber b) (classMap b))

private local instance quotientSubmoduleClosed (V₀ : Submodule ℝ V) :
    IsClosed (V₀ : Set V) :=
  V₀.closed_of_finiteDimensional

/-- The five ordinary stability-in-families clauses on the fibers of one
categorical family, together with compatibility under its pullbacks. -/
structure CategoricalOrdinaryFiberStabilityInFamiliesData
    (charge : JCharge → ChargeProbe ℂ)
    (stable : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Z)
    (boundedness : BoundednessProblem M) : Prop where
  /-- The existing five-clause interface, with support bound to actual fiber
  slicings. -/
  ordinary : OrdinaryFiberStabilityInFamiliesData
    (I := B) (C := F.Fiber) (v := classMap)
    charge stable dedekind V₀ Z hV₀ sigma boundedness
  /-- The same fiber conditions are compatible with every categorical
  pullback. -/
  baseChange : FiberPreStabilityBaseChangeData F classMap sigma

namespace CategoricalOrdinaryFiberStabilityInFamiliesData

variable {F classMap sigma}
  {charge : JCharge → ChargeProbe ℂ}
  {stable : JOpen → OpenLocusProbe} {dedekind : DedekindHNProblem D}
  {V₀ : Submodule ℝ V} {Z : V →ₗ[ℝ] ℂ}
  {hV₀ : V₀ ≤ LinearMap.ker Z}
  {boundedness : BoundednessProblem M}

/-- Project the geometric and numerical conditions used by deformation
arguments.  This proves no geometric or analytic conclusion. -/
theorem toDeformationInputConditions
    (h : CategoricalOrdinaryFiberStabilityInFamiliesData F classMap sigma
      charge stable dedekind V₀ Z hV₀ boundedness) :
    OrdinaryDeformationInputConditions stable dedekind V₀ Z hV₀
      (ordinaryFiberSemistableClasses sigma) boundedness :=
  h.ordinary.toDeformationInputConditions

/-- The actual slicing-defined semistable locus is stable under a pullback
which does not annihilate the chosen object. -/
theorem class_mem_semistableClasses_pull
    (h : CategoricalOrdinaryFiberStabilityInFamiliesData F classMap sigma
      charge stable dedekind V₀ Z hV₀ boundedness)
    {s t : B} (f : s ⟶ t) {phi : ℝ} {E : F.Fiber t}
    (hP : (sigma t).slicing.P phi E)
    (hE : ¬IsZero ((F.pull f).obj E)) :
    classMap t (K₀.of _ E) ∈ ordinaryFiberSemistableClasses sigma s :=
  h.baseChange.class_mem_semistableClasses_pull f hP hE

/-- The common real-linear charge evaluates the preserved object class as the
fiber central charge on either side of pullback. -/
theorem commonCharge_pull
    (h : CategoricalOrdinaryFiberStabilityInFamiliesData F classMap sigma
      charge stable dedekind V₀ Z hV₀ boundedness)
    {s t : B} (f : s ⟶ t) (E : F.Fiber t) :
    Z (classMap s (K₀.of _ ((F.pull f).obj E))) = (sigma t).charge E := by
  rw [h.baseChange.class_pull f E, h.ordinary.charge_compatible t]

end CategoricalOrdinaryFiberStabilityInFamiliesData

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families
