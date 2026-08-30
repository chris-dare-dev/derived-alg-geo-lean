/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.Relative
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineFamilyPseudofunctor

/-!
# The relative-perfect locus in affine derived families

This file cuts out the honest relative-perfect, universally-gluable locus in
the affine family pseudofunctor.  For a fixed affine morphism
`X : B ⟶ R` and a test `B`-algebra `A`, the predicate is evaluated on the
derived category of the actual base-changed total space
`Spec (R ⊔_B A)` relative to `Spec A`.

Only the object locus is constructed here.  In particular, this file does
not install a `Pseudofunctor.ObjectProperty.IsClosedUnderMapObj` instance:
that instance is precisely the pending theorem that arbitrary derived base
change preserves pseudo-coherence, finite Tor amplitude, and fiberwise
negative Ext vanishing.  Once those results are proved, Mathlib's
`Pseudofunctor.ObjectProperty.fullsubcategory` packages the restricted
pseudofunctor and all of its coherence automatically.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

/-- The affine bounded-projective objects whose realization on the actual
base-changed total space is relative-perfect and universally gluable over
the test scheme. -/
def affineFamilyUniversallyGluableRelativePerfect
    {B : CommRingCat.{u}} (X A : Under B) :
    ObjectProperty
      (AffineBoundedAboveProjectiveQuasicoherentDerivedCategory
        (AffineFamilyCoordinateRing X A)) :=
  (schemeUniversallyGluableRelativePerfect
      (affineFamilyToTestScheme X A)).inverseImage
    (affineGeometricBoundedAboveProjectiveDerivedToDqc
      (AffineFamilyCoordinateRing X A))

instance affineFamilyUniversallyGluableRelativePerfect_isClosedUnderIsomorphisms
    {B : CommRingCat.{u}} (X A : Under B) :
    (affineFamilyUniversallyGluableRelativePerfect X A).IsClosedUnderIsomorphisms :=
  by
    change
      ((schemeUniversallyGluableRelativePerfect
        (affineFamilyToTestScheme X A)).inverseImage
          (affineGeometricBoundedAboveProjectiveDerivedToDqc
            (AffineFamilyCoordinateRing X A))).IsClosedUnderIsomorphisms
    infer_instance

/-- The full derived category of bounded-projective affine family objects
that are genuinely relative-perfect and universally gluable. -/
abbrev AffineFamilyUniversallyGluableRelativePerfectCategory
    {B : CommRingCat.{u}} (X A : Under B) :=
  (affineFamilyUniversallyGluableRelativePerfect X A).FullSubcategory

/-- The relative-perfect condition as an object property on every fiber of
the affine family moduli-groupoid pseudofunctor. -/
noncomputable def affineFamilyUniversallyGluableRelativePerfectCoreProperty
    {B : CommRingCat.{u}} (X : Under B) :
    (affineFamilyBoundedAboveProjectivePseudofunctor X).ObjectProperty where
  prop A :=
    (affineFamilyUniversallyGluableRelativePerfect X A.as).inverseImage
      (Core.inclusion _)

instance affineFamilyUniversallyGluableRelativePerfectCoreProperty_isClosed
    {B : CommRingCat.{u}} (X : Under B) :
    Pseudofunctor.ObjectProperty.IsClosedUnderIsomorphisms
      (affineFamilyUniversallyGluableRelativePerfectCoreProperty X) where
  isClosedUnderIsomorphisms A := by
    change
      ((affineFamilyUniversallyGluableRelativePerfect X A.as).inverseImage
        (Core.inclusion _)).IsClosedUnderIsomorphisms
    infer_instance

/-- The actual groupoid fiber of relative-perfect, universally-gluable
affine families over the test `B`-algebra `A`. -/
abbrev AffineFamilyUniversallyGluableRelativePerfectModuliFiber
    {B : CommRingCat.{u}} (X A : Under B) :=
  Core (AffineFamilyUniversallyGluableRelativePerfectCategory X A)

instance affineFamilyUniversallyGluableRelativePerfectModuliFiber_isGroupoid
    {B : CommRingCat.{u}} (X A : Under B) :
    IsGroupoid
      (AffineFamilyUniversallyGluableRelativePerfectModuliFiber X A) :=
  inferInstance

/-- Include the relative-perfect affine-family moduli groupoid in the
ambient bounded-projective moduli groupoid. -/
noncomputable def affineFamilyUniversallyGluableRelativePerfectCoreInclusion
    {B : CommRingCat.{u}} (X A : Under B) :
    AffineFamilyUniversallyGluableRelativePerfectModuliFiber X A ⥤
      AffineFamilyBoundedAboveProjectiveModuliFiber X A :=
  (ObjectProperty.ι
    (affineFamilyUniversallyGluableRelativePerfect X A)).core

/-- Forget a relative-perfect affine family to the honest `Dqc` category of
its base-changed total space. -/
noncomputable def affineFamilyUniversallyGluableRelativePerfectModuliForget
    {B : CommRingCat.{u}} (X A : Under B) :
    AffineFamilyUniversallyGluableRelativePerfectModuliFiber X A ⥤
      SchemeQuasicoherentDerivedCategory
        (Spec (AffineFamilyCoordinateRing X A)) :=
  affineFamilyUniversallyGluableRelativePerfectCoreInclusion X A ⋙
    affineFamilyBoundedAboveProjectiveModuliForget X A

end

end CategoryTheory.Triangulated.StabilityCondition.Families
