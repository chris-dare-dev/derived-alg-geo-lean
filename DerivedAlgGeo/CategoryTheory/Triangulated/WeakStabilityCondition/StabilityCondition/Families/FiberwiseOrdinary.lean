/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.FiberwiseSupport
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.Ordinary

/-!
# The ordinary families interface on actual fiber categories

`OrdinaryStabilityInFamiliesData` keeps its semistable loci abstract so that
the five source clauses can be audited independently of category theory.  The
adapter in this file removes that freedom: its support locus is definitionally
the set of classes of nonzero objects in phases of actual slicings on a family
of possibly different triangulated categories.

The geometric inputs remain honest premises.  In particular, this file does
not construct a scheme, a relative category, base-change functors, relative
Harder--Narasimhan structures, or bounded moduli spaces.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families

open CategoryTheory Limits Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.Families
open CategoryTheory.Triangulated.WeakStabilityCondition.Support
open CategoryTheory.Triangulated.WeakStabilityCondition.Families

noncomputable section

universe u

variable {JCharge JOpen D I M V : Type*} {C : I → Type u}
  [∀ i : I, Category (C i)] [∀ i : I, Preadditive (C i)]
  [∀ i : I, HasZeroObject (C i)] [∀ i : I, HasShift (C i) ℤ]
  [∀ (i : I) (n : ℤ), (shiftFunctor (C i) n).Additive]
  [∀ i : I, Pretriangulated (C i)]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {v : ∀ i, K₀ (C i) →+ V}

private local instance quotientSubmoduleClosed (V₀ : Submodule ℝ V) :
    IsClosed (V₀ : Set V) :=
  V₀.closed_of_finiteDimensional

/-- The five ordinary stability-in-families clauses with the support locus
bound to actual slicings on the fiber categories.

The `charge`, `stable`, `dedekind`, and `boundedness` parameters are still
client-supplied geometric probes.  The numerical support parameter is not:
it is forced to be `ordinaryFiberSemistableClasses σ`. -/
structure OrdinaryFiberStabilityInFamiliesData
    (charge : JCharge → ChargeProbe ℂ)
    (stable : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Z)
    (σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i))
    (boundedness : BoundednessProblem M) : Prop where
  /-- Definition 20.5(1)--(3), still expressed through explicit client
  probes. -/
  definition20_5 : OrdinaryDefinition20_5Conditions charge stable dedekind
  /-- The one real-linear charge on the common class space realizes the
  central charge of every fiber pre-stability condition. -/
  charge_compatible : ∀ i (x : V), Z x = (σ i).Z x
  /-- Definition 21.15(4), on the quotient, for the actual slicing-defined
  semistable classes of every fiber. -/
  uniformSupport : HasUniformQuadraticSupportPropertyModulo
    V₀ Z hV₀ (ordinaryFiberSemistableClasses σ)
  /-- Definition 21.15(5), retained as the caller's geometric boundedness
  obligation. -/
  bounded : UniversalBoundedness boundedness

/-- Forget that the support loci came from actual fiber slicings and recover
the existing five-clause abstract package. -/
theorem OrdinaryFiberStabilityInFamiliesData.toOrdinaryStabilityInFamiliesData
    {charge : JCharge → ChargeProbe ℂ}
    {stable : JOpen → OpenLocusProbe} {dedekind : DedekindHNProblem D}
    {V₀ : Submodule ℝ V} {Z : V →ₗ[ℝ] ℂ}
    {hV₀ : V₀ ≤ LinearMap.ker Z}
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    {boundedness : BoundednessProblem M}
    (h : OrdinaryFiberStabilityInFamiliesData charge stable dedekind
      V₀ Z hV₀ σ boundedness) :
    OrdinaryStabilityInFamiliesData charge stable dedekind V₀ Z hV₀
      (ordinaryFiberSemistableClasses σ) boundedness :=
  ⟨h.definition20_5, h.uniformSupport, h.bounded⟩

/-- Project the geometric and numerical conditions used by deformation
arguments.  This does not produce a geometric or analytic conclusion. -/
theorem OrdinaryFiberStabilityInFamiliesData.toDeformationInputConditions
    {charge : JCharge → ChargeProbe ℂ}
    {stable : JOpen → OpenLocusProbe} {dedekind : DedekindHNProblem D}
    {V₀ : Submodule ℝ V} {Z : V →ₗ[ℝ] ℂ}
    {hV₀ : V₀ ≤ LinearMap.ker Z}
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    {boundedness : BoundednessProblem M}
    (h : OrdinaryFiberStabilityInFamiliesData charge stable dedekind
      V₀ Z hV₀ σ boundedness) :
    OrdinaryDeformationInputConditions stable dedekind V₀ Z hV₀
      (ordinaryFiberSemistableClasses σ) boundedness :=
  ⟨h.definition20_5.opennessOfGeometricStability,
    h.definition20_5.dedekindHN, h.uniformSupport, h.bounded⟩

/-- The quotient-uniform support field specializes to genuine quadratic
support for the actual semistable locus of each fiber. -/
theorem OrdinaryFiberStabilityInFamiliesData.fiberSupport
    {charge : JCharge → ChargeProbe ℂ}
    {stable : JOpen → OpenLocusProbe} {dedekind : DedekindHNProblem D}
    {V₀ : Submodule ℝ V} {Z : V →ₗ[ℝ] ℂ}
    {hV₀ : V₀ ≤ LinearMap.ker Z}
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    {boundedness : BoundednessProblem M}
    (h : OrdinaryFiberStabilityInFamiliesData charge stable dedekind
      V₀ Z hV₀ σ boundedness) (i : I) :
    HasQuadraticSupportProperty (quotientCharge V₀ Z hV₀)
      (V₀.mkQ '' ordinaryFiberSemistableClasses σ i) :=
  h.uniformSupport.fiber i

/-- On every original fiber class, the descended common charge agrees with
the central charge stored by that fiber's pre-stability condition. -/
theorem OrdinaryFiberStabilityInFamiliesData.quotientCharge_mkQ
    {charge : JCharge → ChargeProbe ℂ}
    {stable : JOpen → OpenLocusProbe} {dedekind : DedekindHNProblem D}
    {V₀ : Submodule ℝ V} {Z : V →ₗ[ℝ] ℂ}
    {hV₀ : V₀ ≤ LinearMap.ker Z}
    {σ : ∀ i, PreStabilityCondition.WithClassMap (C i) (v i)}
    {boundedness : BoundednessProblem M}
    (h : OrdinaryFiberStabilityInFamiliesData charge stable dedekind
      V₀ Z hV₀ σ boundedness) (i : I) (x : V) :
    quotientCharge V₀ Z hV₀ (V₀.mkQ x) = (σ i).Z x := by
  rw [CategoryTheory.Triangulated.WeakStabilityCondition.Support.quotientCharge_mkQ]
  exact h.charge_compatible i x

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families
