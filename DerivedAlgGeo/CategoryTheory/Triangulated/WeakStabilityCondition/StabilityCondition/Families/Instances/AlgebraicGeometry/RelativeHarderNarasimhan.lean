/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Moduli.HarderNarasimhan.RelativeFiltration

/-!
# Relative Harder--Narasimhan realizations of categorical family interfaces

The geometric filtration is owned by
`AlgebraicGeometry.Moduli.HarderNarasimhan`. This opt-in leaf packages it as
the generic `DedekindHNProblem` and its integration predicate.
-/

namespace AlgebraicGeometry.Moduli.HarderNarasimhan
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Triangulated.WeakStabilityCondition.Families

noncomputable section

universe u w uV

variable {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)
  {V : Type uV} [AddCommGroup V]
  (classMap : ∀ T, K₀ (F.Fiber T) →+ V)
  (sigma : ∀ T, PreStabilityCondition.WithClassMap (F.Fiber T) (classMap T))

/-- The categorical Dedekind-HN problem realized by regular curve base changes
and object-level relative HN filtrations. -/
def schemeRelativeHNProblem
    (IsEligible : RegularCurveBaseChange S → Prop) :
    DedekindHNProblem (RegularCurveBaseChange S) where
  IsEligible := IsEligible
  HNStructure := fun T ↦
    ∀ E : F.Fiber T.baseChange,
      SchemeRelativeHNFiltration F classMap sigma E

/-- Objectwise existence of relative HN filtrations on eligible curve bases. -/
def HasSchemeRelativeHNFiltrations
    (IsEligible : RegularCurveBaseChange S → Prop) : Prop :=
  ∀ (T : RegularCurveBaseChange S), IsEligible T →
    ∀ E : F.Fiber T.baseChange,
      Nonempty (SchemeRelativeHNFiltration F classMap sigma E)

/-- Objectwise relative-HN existence realizes the categorical integration clause. -/
theorem integratesAfterDedekindBaseChange_of_relativeHN
    {IsEligible : RegularCurveBaseChange S → Prop}
    (h : HasSchemeRelativeHNFiltrations F classMap sigma IsEligible) :
    IntegratesAfterDedekindBaseChange
      (schemeRelativeHNProblem F classMap sigma IsEligible) := by
  intro T hT
  exact ⟨fun E ↦ (h T hT E).some⟩

/-- The constant categorical family realizes relative-HN existence. -/
theorem hasSchemeRelativeHNFiltrations_constant
    (S : Scheme.{u})
    (C : Type w) [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    (V : Type uV) [AddCommGroup V] (v₀ : K₀ C →+ V)
    (sigma₀ : PreStabilityCondition.WithClassMap C v₀)
    (IsEligible : RegularCurveBaseChange S → Prop) :
    HasSchemeRelativeHNFiltrations
      (SchemeTriangulatedFiberFamily.constant S C)
      (fun _ ↦ v₀) (fun _ ↦ sigma₀) IsEligible := by
  intro T _ E
  exact SchemeRelativeHNFiltration.constant_nonempty S C V v₀ sigma₀
    T.baseChange E

/-- The constant family consequently realizes categorical Dedekind integration. -/
theorem integratesAfterDedekindBaseChange_relativeHN_constant
    (S : Scheme.{u})
    (C : Type w) [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    (V : Type uV) [AddCommGroup V] (v₀ : K₀ C →+ V)
    (sigma₀ : PreStabilityCondition.WithClassMap C v₀)
    (IsEligible : RegularCurveBaseChange S → Prop) :
    IntegratesAfterDedekindBaseChange
      (schemeRelativeHNProblem
        (SchemeTriangulatedFiberFamily.constant S C)
        (fun _ ↦ v₀) (fun _ ↦ sigma₀) IsEligible) :=
  integratesAfterDedekindBaseChange_of_relativeHN
    (SchemeTriangulatedFiberFamily.constant S C)
    (fun _ ↦ v₀) (fun _ ↦ sigma₀)
    (hasSchemeRelativeHNFiltrations_constant S C V v₀ sigma₀ IsEligible)

end

end AlgebraicGeometry.Moduli.HarderNarasimhan
