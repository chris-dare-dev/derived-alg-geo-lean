/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.PreStabilityBaseChange
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.ResidueFiber
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Symmetry.Autoequivalence.Slicing.Transport

/-!
# Relative Harder--Narasimhan filtrations over curve bases

This file replaces the proposition-valued Dedekind-HN placeholder at the
scheme-facing boundary with object-level data.  A `SchemeRelativeHNFiltration`
is an actual `HNFiltration` of an object in the category over a scheme base
change.  Its tower, factors, strictly decreasing phases, and semistability
proofs are exposed directly.

Given the explicit `FiberPreStabilityBaseChangeData` witness, the filtration
pulls back along every morphism of scheme base changes.  Specializing to the
canonical residue-field morphism produces an ordinary `HNFiltration` in the
point fiber, with the same length and phases and factors obtained by actual
categorical pullback.

`RegularCurveBaseChange` packages a genuine scheme over the fixed base whose
scheme is Noetherian, whose local rings are regular of dimension at most one,
and which has a point of local dimension one.  An additional predicate remains
available in `schemeRelativeHNProblem` for the source's essentially-finite-type
or other eligibility conditions.

Existence for a general geometric family is deliberately retained as the named
premise `HasSchemeRelativeHNFiltrations`.  The constant categorical family is
inhabited using the HN existence field of its slicing.  No semistable reduction,
bounded coherent/perfect realization, moduli construction, or conclusion of
Theorem 22.2 is asserted.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry
open CategoryTheory.Triangulated.WeakStabilityCondition.Families
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families

noncomputable section

universe u w uV

/-- An actual scheme base change whose underlying scheme has the local
properties of a regular one-dimensional Noetherian curve. -/
structure RegularCurveBaseChange (S : Scheme.{u}) where
  /-- The actual scheme over `S`. -/
  baseChange : SchemeBaseChange S
  /-- The curve is Noetherian. -/
  noetherian : IsNoetherian baseChange.left
  /-- Every local ring is regular. -/
  regular : ∀ x : baseChange.left,
    IsRegularLocalRing (baseChange.left.presheaf.stalk x)
  /-- Every local ring has Krull dimension at most one. -/
  dimensionLEOne : ∀ x : baseChange.left,
    Ring.KrullDimLE 1 (baseChange.left.presheaf.stalk x)
  /-- At least one local ring has positive dimension, excluding the
  zero-dimensional case. -/
  hasDimensionOne : ∃ x : baseChange.left,
    ¬Ring.KrullDimLE 0 (baseChange.left.presheaf.stalk x)

namespace RegularCurveBaseChange

variable {S : Scheme.{u}}

instance (T : RegularCurveBaseChange S) : IsNoetherian T.baseChange.left :=
  T.noetherian

instance (T : RegularCurveBaseChange S) (x : T.baseChange.left) :
    IsRegularLocalRing (T.baseChange.left.presheaf.stalk x) :=
  T.regular x

instance (T : RegularCurveBaseChange S) (x : T.baseChange.left) :
    Ring.KrullDimLE 1 (T.baseChange.left.presheaf.stalk x) :=
  T.dimensionLEOne x

end RegularCurveBaseChange

variable {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)
  {V : Type uV} [AddCommGroup V]
  (classMap : ∀ T, K₀ (F.Fiber T) →+ V)
  (sigma : ∀ T, PreStabilityCondition.WithClassMap (F.Fiber T) (classMap T))

/-- An object-level relative HN filtration over an actual scheme base change.
The underlying `HNFiltration` contains the finite Postnikov tower, factors,
strict phase ordering, and phase-slice membership. -/
structure SchemeRelativeHNFiltration {T : SchemeBaseChange S}
    (E : F.Fiber T) where
  /-- The actual HN filtration in the category over the base change. -/
  filtration : HNFiltration (F.Fiber T) (sigma T).slicing.P E
  /-- The ordinary HN filtration obtained at every actual residue fiber. -/
  fiberFiltration : ∀ x : T.left,
    HNFiltration (F.ResidueFiber T x)
      (sigma (T.residue x)).slicing.P ((F.pullToResidue T x).obj E)
  /-- Fiber restriction preserves the number of factors. -/
  fiber_length : ∀ x : T.left, (fiberFiltration x).n = filtration.n
  /-- Fiber restriction preserves every factor phase. -/
  fiber_phase : ∀ (x : T.left) (i : Fin filtration.n),
    (fiberFiltration x).φ (Fin.cast (fiber_length x).symm i) = filtration.φ i
  /-- Each fiber factor is the actual pullback of its relative factor. -/
  fiberFactorIso : ∀ (x : T.left) (i : Fin filtration.n),
    (fiberFiltration x).factor (Fin.cast (fiber_length x).symm i) ≅
      (F.pullToResidue T x).obj (filtration.factor i)

namespace SchemeRelativeHNFiltration

variable {F classMap sigma} {T : SchemeBaseChange S} {E : F.Fiber T}

/-- The finite Postnikov tower underlying a relative HN filtration. -/
def tower (H : SchemeRelativeHNFiltration F classMap sigma E) :
    PostnikovTower (F.Fiber T) E :=
  H.filtration.toPostnikovTower

/-- The number of relative semistable factors. -/
def length (H : SchemeRelativeHNFiltration F classMap sigma E) : ℕ :=
  H.filtration.n

/-- The `i`-th relative factor. -/
def factor (H : SchemeRelativeHNFiltration F classMap sigma E)
    (i : Fin H.length) : F.Fiber T :=
  H.filtration.factor i

/-- The phase of the `i`-th relative factor. -/
def phase (H : SchemeRelativeHNFiltration F classMap sigma E)
    (i : Fin H.length) : ℝ :=
  H.filtration.φ i

/-- Relative factor phases are strictly decreasing. -/
theorem phase_strictAnti (H : SchemeRelativeHNFiltration F classMap sigma E) :
    StrictAnti H.phase :=
  H.filtration.hφ

/-- Every relative factor lies in its recorded phase slice. -/
theorem factor_semistable (H : SchemeRelativeHNFiltration F classMap sigma E)
    (i : Fin H.length) :
    (sigma T).slicing.P (H.phase i) (H.factor i) :=
  H.filtration.semistable i

/-- Reindex a relative factor by the equality of relative and point-fiber
lengths. -/
def fiberIndex (H : SchemeRelativeHNFiltration F classMap sigma E)
    (x : T.left) (i : Fin H.length) : Fin (H.fiberFiltration x).n :=
  Fin.cast (H.fiber_length x).symm i

/-- Construct coherent relative data from an HN filtration over the base
change and the explicit geometric preimage-slicing witness. -/
noncomputable def ofBaseChangeWitness
    (filtration : HNFiltration (F.Fiber T) (sigma T).slicing.P E)
    (h : FiberPreStabilityBaseChangeData F classMap sigma) :
    SchemeRelativeHNFiltration F classMap sigma E where
  filtration := filtration
  fiberFiltration := fun x ↦
    HNFiltration.mapF filtration (F.pullToResidue T x)
      (fun phi X hX ↦ (h.phase_iff (T.residueTo x) phi X).mp hX)
  fiber_length := fun _ ↦ rfl
  fiber_phase := fun _ _ ↦ rfl
  fiberFactorIso := fun _ _ ↦ Iso.refl _

/-- Pull an object-level relative HN filtration along a morphism of scheme
base changes.  The geometric slicing witness supplies semistability of the
pulled-back factors. -/
noncomputable def pullback
    (H : SchemeRelativeHNFiltration F classMap sigma E)
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {U : SchemeBaseChange S} (f : U ⟶ T) :
    SchemeRelativeHNFiltration F classMap sigma ((F.pull f).obj E) :=
  ofBaseChangeWitness
    (HNFiltration.mapF H.filtration (F.pull f)
      (fun phi X hX ↦ (h.phase_iff f phi X).mp hX)) h

@[simp]
theorem pullback_length
    (H : SchemeRelativeHNFiltration F classMap sigma E)
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {U : SchemeBaseChange S} (f : U ⟶ T) :
    (H.pullback h f).length = H.length :=
  rfl

@[simp]
theorem pullback_phase
    (H : SchemeRelativeHNFiltration F classMap sigma E)
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {U : SchemeBaseChange S} (f : U ⟶ T) (i : Fin H.length) :
    (H.pullback h f).phase i = H.phase i :=
  rfl

/-- Each factor of the pulled-back filtration is the actual pullback of the
corresponding relative factor. -/
def pullbackFactorIso
    (H : SchemeRelativeHNFiltration F classMap sigma E)
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {U : SchemeBaseChange S} (f : U ⟶ T) (i : Fin H.length) :
    (H.pullback h f).factor i ≅ (F.pull f).obj (H.factor i) :=
  Iso.refl _

/-- Restriction of a relative filtration to a point is an ordinary HN
filtration in the actual residue fiber. -/
noncomputable def restrictToFiber
    (H : SchemeRelativeHNFiltration F classMap sigma E)
    (x : T.left) :
    HNFiltration (F.ResidueFiber T x)
      (sigma (T.residue x)).slicing.P ((F.pullToResidue T x).obj E) :=
  H.fiberFiltration x

@[simp]
theorem restrictToFiber_length
    (H : SchemeRelativeHNFiltration F classMap sigma E)
    (x : T.left) :
    (H.restrictToFiber x).n = H.length :=
  H.fiber_length x

@[simp]
theorem restrictToFiber_phase
    (H : SchemeRelativeHNFiltration F classMap sigma E)
    (x : T.left) (i : Fin H.length) :
    (H.restrictToFiber x).φ (H.fiberIndex x i) = H.phase i :=
  H.fiber_phase x i

/-- The factor in the point-fiber HN filtration is the pullback of the
relative factor. -/
def restrictToFiberFactorIso
    (H : SchemeRelativeHNFiltration F classMap sigma E)
    (x : T.left) (i : Fin H.length) :
    (H.restrictToFiber x).factor (H.fiberIndex x i) ≅
      (F.pullToResidue T x).obj (H.factor i) :=
  H.fiberFactorIso x i

/-- Direct pullback and two-stage pullback preserve the same phase function.
This is the filtration-level numerical coherence supplied by the
contravariant family and the compositional slicing witness. -/
theorem pullback_comp_phase
    (H : SchemeRelativeHNFiltration F classMap sigma E)
    (h : FiberPreStabilityBaseChangeData F classMap sigma)
    {R U : SchemeBaseChange S} (f : R ⟶ U) (g : U ⟶ T)
    (i : Fin H.length) :
    (H.pullback h (f ≫ g)).phase i =
      ((H.pullback h g).pullback h f).phase i :=
  rfl

/-- One ordinary HN filtration supplies an object-level relative filtration
in a constant categorical family over any actual scheme base change. -/
theorem constant_nonempty
    (S : Scheme.{u})
    (C : Type w) [Category.{w} C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C]
    (V : Type uV) [AddCommGroup V] (v₀ : K₀ C →+ V)
    (sigma₀ : PreStabilityCondition.WithClassMap C v₀)
    (T : SchemeBaseChange S) (E : C) :
    Nonempty
      (SchemeRelativeHNFiltration
        (SchemeTriangulatedFiberFamily.constant S C)
        (fun _ ↦ v₀) (fun _ ↦ sigma₀) (T := T) E) :=
  (sigma₀.slicing.hn_exists E).map fun H ↦
    ofBaseChangeWitness H
      (FiberPreStabilityBaseChangeData.constant C V v₀ sigma₀)

end SchemeRelativeHNFiltration

/-- The old Dedekind-HN problem specialized to actual regular curve base
changes and object-level relative HN filtrations.  `IsEligible` is kept
explicit for geometric conditions not encoded by `RegularCurveBaseChange`,
such as an essentially-finite-type hypothesis. -/
def schemeRelativeHNProblem
    (IsEligible : RegularCurveBaseChange S → Prop) :
    DedekindHNProblem (RegularCurveBaseChange S) where
  IsEligible := IsEligible
  HNStructure := fun T ↦
    ∀ E : F.Fiber T.baseChange,
      SchemeRelativeHNFiltration F classMap sigma E

/-- The named general geometric existence premise for object-level relative
HN filtrations on every eligible regular curve base change. -/
def HasSchemeRelativeHNFiltrations
    (IsEligible : RegularCurveBaseChange S → Prop) : Prop :=
  ∀ (T : RegularCurveBaseChange S), IsEligible T →
    ∀ E : F.Fiber T.baseChange,
      Nonempty (SchemeRelativeHNFiltration F classMap sigma E)

/-- Objectwise relative-HN existence supplies the legacy integration clause.
The choice of one filtration for every object is made explicitly here. -/
theorem integratesAfterDedekindBaseChange_of_relativeHN
    {IsEligible : RegularCurveBaseChange S → Prop}
    (h : HasSchemeRelativeHNFiltrations F classMap sigma IsEligible) :
    IntegratesAfterDedekindBaseChange
      (schemeRelativeHNProblem F classMap sigma IsEligible) := by
  intro T hT
  exact ⟨fun E ↦ (h T hT E).some⟩

/-- The constant categorical family inhabits the named relative-HN existence
premise on every supplied regular curve, for any explicit eligibility
predicate. -/
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

/-- Consequently the constant categorical family also inhabits the legacy
Dedekind-HN integration interface with genuine object-level filtration data. -/
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

end CategoryTheory.Triangulated.StabilityCondition.Families
