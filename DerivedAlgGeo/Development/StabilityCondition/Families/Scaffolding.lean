/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.CategoricalOrdinary
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families.Weak

/-!
# Compile-only scaffolding for abstract stability-in-families inputs

This module records that the abstract condition structures are logically
inhabitable by constant functions, full loci, `PUnit` witnesses, and a
constant-true boundedness predicate.  Those inhabitants are useful for API
reconnaissance, but they are not mathematical families and therefore expose
no public declarations.

The stable family modules deliberately provide no such vacuous-probe
constructors: nothing in stable discharges a field with a constant-true
predicate, a full-locus probe, or an arbitrary-`Prop` ledger.  Stable modules
do still export constant-family reindexings (`_constant`/`_punit` witnesses
in `FiberwiseSupport`, `PreStabilityBaseChange.constant`, and the scheme and
relative-HN constant models); each of those requires a genuine support or
pre-stability input and asserts nothing vacuously (2026-08-18 adversarial
review, finding P2-10).
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.Development

open CategoryTheory Limits Pretriangulated
open CategoryTheory.Triangulated
open CategoryTheory.Triangulated.Families
open CategoryTheory.Triangulated.WeakStabilityCondition.Support
open CategoryTheory.Triangulated.WeakStabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.Families
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families

noncomputable section

universe u v

private def constantChargeProbe (X : Type u) [TopologicalSpace X]
    {A : Type v} (a : A) : ChargeProbe A where
  Point := X
  topology := inferInstance
  value := Function.const X a

private theorem constantChargeProbe_isLocallyConstant
    (X : Type u) [TopologicalSpace X] {A : Type v} (a : A) :
    (constantChargeProbe X a).IsLocallyConstant := by
  change _root_.IsLocallyConstant (Function.const X a)
  exact _root_.IsLocallyConstant.const a

private def fullOpenLocusProbe (X : Type u) [TopologicalSpace X] :
    OpenLocusProbe where
  Point := X
  topology := inferInstance
  locus := Set.univ

private theorem fullOpenLocusProbe_isOpen
    (X : Type u) [TopologicalSpace X] :
    (fullOpenLocusProbe X).IsOpen := by
  change _root_.IsOpen (Set.univ : Set X)
  exact isOpen_univ

private def fullGenericSemistabilityProbe
    (X : Type u) [TopologicalSpace X] (genericPoint : X) :
    GenericSemistabilityProbe where
  Point := X
  topology := inferInstance
  genericPoint := genericPoint
  semistableLocus := Set.univ

private theorem fullGenericSemistabilityProbe_isGenericallyOpen
    (X : Type u) [TopologicalSpace X] (genericPoint : X) :
    (fullGenericSemistabilityProbe X genericPoint).IsGenericallyOpen := by
  intro _
  refine ⟨Set.univ, ?_, Set.mem_univ _, Set.Subset.rfl⟩
  exact @isOpen_univ X inferInstance

private def constantDedekindHNProblem (D : Type u) (HN : Type v) :
    DedekindHNProblem D where
  IsEligible := fun _ ↦ True
  HNStructure := fun _ ↦ HN

private theorem constantDedekindHNProblem_integrates
    (D : Type u) (HN : Type v) [Nonempty HN] :
    IntegratesAfterDedekindBaseChange (constantDedekindHNProblem D HN) :=
  fun _ _ ↦ (inferInstance : Nonempty HN)

private def constantWeakDedekindHNProblem (D : Type u) (HN : Type v) :
    WeakDedekindHNProblem D where
  IsEligible := fun _ ↦ True
  HNStructure := fun _ ↦ HN
  ZeroChargeNoetherian := fun _ ↦ True

private theorem constantWeakDedekindHNProblem_integrates
    (D : Type u) (HN : Type v) [Nonempty HN] :
    WeakIntegratesAfterDedekindBaseChange
      (constantWeakDedekindHNProblem D HN) :=
  fun _ _ ↦ ⟨(inferInstance : Nonempty HN), trivial⟩

private def trueBoundednessProblem (M : Type u) : BoundednessProblem M where
  IsBounded := fun _ ↦ True

private theorem trueBoundednessProblem_isUniversal (M : Type u) :
    UniversalBoundedness (trueBoundednessProblem M) :=
  fun _ ↦ trivial

variable {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

private local instance quotientSubmoduleClosed (V₀ : Submodule ℝ V) :
    IsClosed (V₀ : Set V) :=
  V₀.closed_of_finiteDimensional

private theorem ordinaryPUnit
    (a : ℂ) (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Z) (S : Set V)
    (hQ : HasQuadraticSupportProperty (quotientCharge V₀ Z hV₀)
      (V₀.mkQ '' S)) :
    OrdinaryStabilityInFamiliesData
      (fun _ : PUnit.{1} ↦ constantChargeProbe PUnit.{1} a)
      (fun _ : PUnit.{1} ↦ fullOpenLocusProbe PUnit.{1})
      (constantDedekindHNProblem PUnit.{1} PUnit.{1})
      V₀ Z hV₀ (fun _ : PUnit.{1} ↦ S)
      (trueBoundednessProblem PUnit.{1}) where
  definition20_5 :=
    { locallyConstantCharge := fun _ ↦
        constantChargeProbe_isLocallyConstant PUnit.{1} a
      opennessOfGeometricStability := fun _ ↦
        fullOpenLocusProbe_isOpen PUnit.{1}
      dedekindHN :=
        constantDedekindHNProblem_integrates PUnit.{1} PUnit.{1} }
  uniformSupport := hQ.constant_modulo V₀ Z hV₀ PUnit.{1}
  bounded := trueBoundednessProblem_isUniversal PUnit.{1}

example
    (a : ℂ) (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Z) (S : Set V)
    (hQ : HasQuadraticSupportProperty (quotientCharge V₀ Z hV₀)
      (V₀.mkQ '' S)) :
    OrdinaryStabilityInFamiliesData
      (fun _ : PUnit.{1} ↦ constantChargeProbe PUnit.{1} a)
      (fun _ : PUnit.{1} ↦ fullOpenLocusProbe PUnit.{1})
      (constantDedekindHNProblem PUnit.{1} PUnit.{1})
      V₀ Z hV₀ (fun _ : PUnit.{1} ↦ S)
      (trueBoundednessProblem PUnit.{1}) :=
  ordinaryPUnit a V₀ Z hV₀ S hQ

variable {C : Type u} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
  {v₀ : K₀ C →+ V}

omit [IsTriangulated C] in
private theorem ordinaryFiberPUnit
    (a : ℂ) (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Z)
    (sigma₀ : PreStabilityCondition.WithClassMap C v₀)
    (hZ : ∀ x : V, Z x = sigma₀.Z x)
    (hQ : HasQuadraticSupportProperty (quotientCharge V₀ Z hV₀)
      (V₀.mkQ '' sigma₀.semistableClasses)) :
    OrdinaryFiberStabilityInFamiliesData
      (I := PUnit.{1}) (C := fun _ ↦ C) (v := fun _ ↦ v₀)
      (fun _ : PUnit.{1} ↦ constantChargeProbe PUnit.{1} a)
      (fun _ : PUnit.{1} ↦ fullOpenLocusProbe PUnit.{1})
      (constantDedekindHNProblem PUnit.{1} PUnit.{1})
      V₀ Z hV₀ (fun _ ↦ sigma₀)
      (trueBoundednessProblem PUnit.{1}) where
  definition20_5 :=
    { locallyConstantCharge := fun _ ↦
        constantChargeProbe_isLocallyConstant PUnit.{1} a
      opennessOfGeometricStability := fun _ ↦
        fullOpenLocusProbe_isOpen PUnit.{1}
      dedekindHN :=
        constantDedekindHNProblem_integrates PUnit.{1} PUnit.{1} }
  charge_compatible := fun _ ↦ hZ
  uniformSupport := hQ.constant_modulo V₀ Z hV₀ PUnit.{1}
  bounded := trueBoundednessProblem_isUniversal PUnit.{1}

example
    (a : ℂ) (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Z)
    (sigma₀ : PreStabilityCondition.WithClassMap C v₀)
    (hZ : ∀ x : V, Z x = sigma₀.Z x)
    (hQ : HasQuadraticSupportProperty (quotientCharge V₀ Z hV₀)
      (V₀.mkQ '' sigma₀.semistableClasses)) :
    CategoricalOrdinaryFiberStabilityInFamiliesData
      (TriangulatedFiberFamily.constant PUnit.{1} C)
      (fun _ ↦ v₀) (fun _ ↦ sigma₀)
      (fun _ : PUnit.{1} ↦ constantChargeProbe PUnit.{1} a)
      (fun _ : PUnit.{1} ↦ fullOpenLocusProbe PUnit.{1})
      (constantDedekindHNProblem PUnit.{1} PUnit.{1})
      V₀ Z hV₀ (trueBoundednessProblem PUnit.{1}) where
  ordinary := ordinaryFiberPUnit a V₀ Z hV₀ sigma₀ hZ hQ
  baseChange := FiberPreStabilityBaseChangeData.constant C V v₀ sigma₀

private def constantWeakChargeProbe
    (X : Type u) [TopologicalSpace X] {I Λ : Type*} (i : I) (k : Λ) :
    WeakChargeProbe I Λ where
  Point := X
  topology := inferInstance
  fiber := Function.const X i
  klass := Function.const X k

private def constantWeakSemistabilityProbe
    (X : Type u) [TopologicalSpace X] (genericPoint : X)
    {I C : Type*} (i : I) (E : C) : WeakSemistabilityProbe I C where
  Point := X
  topology := inferInstance
  genericPoint := genericPoint
  fiber := Function.const X i
  object := Function.const X E

omit [IsTriangulated C] in
private theorem constantWeakChargeProbe_isLocallyConstant
    {t : TStructure C} (W : WeakStabilityFunction t) (k : K₀ C) :
    ((constantWeakChargeProbe PUnit.{1} PUnit.unit k).toChargeProbe
      (fun _ : PUnit.{1} ↦ W)).IsLocallyConstant := by
  unfold ChargeProbe.IsLocallyConstant WeakChargeProbe.toChargeProbe
  change _root_.IsLocallyConstant (Function.const PUnit ((W.Z k)))
  exact _root_.IsLocallyConstant.const _

omit [IsTriangulated C] in
private theorem constantWeakSemistabilityProbe_isGenericallyOpen
    {t : TStructure C} (W : WeakStabilityFunction t) (E : C) :
    ((constantWeakSemistabilityProbe PUnit.{1} PUnit.unit PUnit.unit E).toGenericProbe
      (fun _ : PUnit.{1} ↦ W)).IsGenericallyOpen := by
  intro hgeneric
  refine ⟨Set.univ, ?_, Set.mem_univ _, fun _ _ ↦ hgeneric⟩
  exact @isOpen_univ PUnit.{1} inferInstance

omit [IsTriangulated C] in
private theorem weakClauseZeroConstant
    {t : TStructure C} (W : WeakStabilityFunction t)
    (hZ : HasGaussianRationalValues W.Z)
    (hN : IsNoetherianTorsionSubcategory t W.zeroCharge) :
    WeakDefinition20_5ClauseZero (fun _ : PUnit.{1} ↦ W) :=
  ⟨fun _ ↦ hZ, fun _ ↦ hN⟩

omit [IsTriangulated C] in
private theorem weakSupportConstant
    {t : TStructure C} {W : WeakStabilityFunction t}
    {V₀ : Submodule ℝ V} {Zlin : V →ₗ[ℝ] ℂ}
    {hV₀ : V₀ ≤ LinearMap.ker Zlin}
    (hQ : WeakQuotientQuadraticSupportData W v₀ V₀ Zlin hV₀) :
    WeakStabilityFunction.QuotientUniformQuadraticSupportData
      (fun _ : PUnit.{1} ↦ W) v₀ V₀ Zlin hV₀ :=
  ⟨fun _ ↦ hQ.charge_compatible, fun _ ↦ hQ.zero_class_mem,
    hQ.quadratic.constant_modulo V₀ Zlin hV₀ PUnit.{1}⟩

omit [IsTriangulated C] in
example
    {t : TStructure C} (W : WeakStabilityFunction t)
    (hZ : HasGaussianRationalValues W.Z)
    (hN : IsNoetherianTorsionSubcategory t W.zeroCharge)
    (V₀ : Submodule ℝ V) (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (hQ : WeakQuotientQuadraticSupportData W v₀ V₀ Zlin hV₀)
    (k : K₀ C) (E : C) :
    WeakStabilityInFamiliesData (v := v₀)
      (fun _ : PUnit.{1} ↦ W)
      (fun _ : PUnit.{1} ↦
        constantWeakChargeProbe PUnit.{1} PUnit.unit k)
      (fun _ : PUnit.{1} ↦
        constantWeakSemistabilityProbe PUnit.{1} PUnit.unit PUnit.unit E)
      (constantWeakDedekindHNProblem PUnit.{1} PUnit.{1})
      V₀ Zlin hV₀ (trueBoundednessProblem PUnit.{1}) where
  clauseZero := weakClauseZeroConstant W hZ hN
  definition20_5 :=
    { locallyConstantCharge := fun _ ↦
        constantWeakChargeProbe_isLocallyConstant W k
      genericOpennessOfSemistability := fun _ ↦
        constantWeakSemistabilityProbe_isGenericallyOpen W E
      dedekindWeakHN :=
        constantWeakDedekindHNProblem_integrates PUnit.{1} PUnit.{1} }
  uniformSupport := weakSupportConstant hQ
  bounded := trueBoundednessProblem_isUniversal PUnit.{1}

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.Development
