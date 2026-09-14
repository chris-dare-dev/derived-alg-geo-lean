/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.Jacobson.Ring
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.MassHom.Basic

/-!
# Mass--Hom bounds over finite-type field extensions

This file isolates the cancellation in inequality (8.4) of
arXiv:2607.28411v1, Theorem 8.23.  A finite-type extension of fields is
finite by Zariski's lemma.  The remaining two geometric inputs are stated
exactly as the formulas used in the paper:

* adjunction and restriction of scalars multiply the extension-field Hom
  dimension by the degree of the extension;
* pushforward of the base-changed HN filtration multiplies mass by the same
  degree.

The theorem cancels this positive common factor.  It does not manufacture
either formula or a scalar-base-change stability condition; those are the
geometric outputs of the Theorem 2.8 lane.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated CategoryTheory.SerreFunctor

namespace CategoryTheory.Triangulated.StabilityCondition.WithClassMap

noncomputable section

universe w w' v u u' v' u''

/-- A uniform numerical mass--Hom estimate on an arbitrary index of
field/object tests.  This is the common codomain of the cancellation theorem
below and HLR Theorem 2.35(1). -/
def UniformMassHomBound {J : Type*}
    (dimension : J → ℕ) (mass : J → ℝ) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ j, (dimension j : ℝ) ≤ K * mass j

namespace UniformMassHomBound

/-- Cancel a positive degree from the two sides of a uniform mass--Hom
estimate.  The three mathematical inputs are the base estimate, the
adjunction dimension formula, and the HN mass formula. -/
theorem of_scaled {J : Type*}
    {baseDimension dimension : J → ℕ}
    {baseMass mass degree : J → ℝ}
    (hdegree : ∀ j, 0 < degree j)
    (hbase : UniformMassHomBound baseDimension baseMass)
    (hadjunction : ∀ j,
      degree j * (dimension j : ℝ) = (baseDimension j : ℝ))
    (hHNMass : ∀ j, baseMass j = degree j * mass j) :
    UniformMassHomBound dimension mass := by
  obtain ⟨K, hK, hbound⟩ := hbase
  refine ⟨K, hK, fun j ↦ ?_⟩
  refine le_of_mul_le_mul_left ?_ (hdegree j)
  rw [hadjunction j]
  calc
    (baseDimension j : ℝ) ≤ K * baseMass j := hbound j
    _ = degree j * (K * mass j) := by rw [hHNMass j]; ring

end UniformMassHomBound

/-- Zariski's lemma in the exact form used in Theorem 8.23: a finite-type
extension of fields is finite-dimensional. -/
theorem finiteDimensional_of_finiteType_field
    (k : Type w) (ell : Type w') [Field k] [Field ell]
    [Algebra k ell] [Algebra.FiniteType k ell] :
    FiniteDimensional k ell :=
  finite_of_finite_type_of_isJacobsonRing k ell

variable {k : Type w} {ell : Type w'} [Field k] [Field ell]
  [Algebra k ell] [Algebra.FiniteType k ell]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [HomFinite k C]
variable {Cell : Type u''} [Category.{v'} Cell] [Preadditive Cell]
  [Linear ell Cell] [HasZeroObject Cell] [HasShift Cell ℤ]
  [∀ n : ℤ, (shiftFunctor Cell n).Additive]
  [Pretriangulated Cell] [HomFinite ell Cell]
variable {Lambda : Type u'} [AddCommGroup Lambda]
  {LambdaEll : Type*} [AddCommGroup LambdaEll]
  {vC : K₀ C →+ Lambda} {vCell : K₀ Cell →+ LambdaEll}

/-- The adjunction/restriction-of-scalars dimension formula used in (8.4).
Its geometric constructor is deliberately left to scalar base change. -/
def FieldExtensionAdjunctionDimensionFormula
    (push : Cell ⥤ C) (G : C) (Gell : Cell) : Prop :=
  ∀ F : Cell,
    (Module.finrank k ell : ℝ) *
        (Module.finrank ell (Gell ⟶ F) : ℝ) =
      (Module.finrank k (G ⟶ push.obj F) : ℝ)

/-- The HN-preserving pushforward mass formula used in (8.4).  This is the
mass consequence supplied by the scalar-base-change stability machinery. -/
def FieldExtensionHNMassFormula
    (sigma : StabilityCondition.WithClassMap C vC)
    (sigmaEll : StabilityCondition.WithClassMap Cell vCell)
    (push : Cell ⥤ C) : Prop :=
  ∀ F : Cell,
    (stabilityMass sigma (push.obj F)).toReal =
      (Module.finrank k ell : ℝ) *
        (stabilityMass sigmaEll F).toReal

/-- Inequality (8.4) for one finite-type field extension.  The same constant
as the base mass--Hom bound works after extension: Zariski's lemma makes the
degree positive, and the two named formulas cancel it. -/
theorem inequality84
    (sigma : StabilityCondition.WithClassMap C vC)
    (sigmaEll : StabilityCondition.WithClassMap Cell vCell)
    (push : Cell ⥤ C) (G : C) (Gell : Cell)
    (hG : sigma.HasMassHomBoundFor (k := k) G)
    (hadjunction : FieldExtensionAdjunctionDimensionFormula
      (k := k) (ell := ell) push G Gell)
    (hHNMass : FieldExtensionHNMassFormula
      (k := k) (ell := ell) sigma sigmaEll push) :
    sigmaEll.HasMassHomBoundFor (k := ell) Gell := by
  letI : FiniteDimensional k ell :=
    finiteDimensional_of_finiteType_field k ell
  obtain ⟨K, hK, hbound⟩ := hG
  refine ⟨K, hK, fun F ↦ ?_⟩
  have hdegreeNat : 0 < Module.finrank k ell := Module.finrank_pos
  have hdegree : 0 < (Module.finrank k ell : ℝ) := by
    exact_mod_cast hdegreeNat
  refine le_of_mul_le_mul_left ?_ hdegree
  rw [hadjunction F]
  calc
    (Module.finrank k (G ⟶ push.obj F) : ℝ) ≤
        K * (stabilityMass sigma (push.obj F)).toReal := hbound _
    _ = (Module.finrank k ell : ℝ) *
        (K * (stabilityMass sigmaEll F).toReal) := by
      rw [hHNMass F]
      ring

end

end CategoryTheory.Triangulated.StabilityCondition.WithClassMap
