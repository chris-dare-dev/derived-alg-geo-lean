/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.PseudofunctorObjectProperty
import DerivedAlgGeo.AlgebraicGeometry.Moduli.PerfectComplex.AffineFamilyRelativePerfect

/-!
# A universally stable affine relative-perfect pseudofunctor

The full affine relative-perfect locus has been defined, but showing that
every one of its objects remains relative-perfect and universally gluable
after arbitrary base change is the main pending geometric theorem.

This file constructs the honest supported sub-pseudofunctor consisting of
objects that satisfy the concrete relative-perfect predicate after every
base change.  Preservation is a theorem of the pseudofunctor compositor, not
caller-supplied data.  The resulting object property is contained in the full
relative-perfect locus by the pseudofunctor unit.  Proving the reverse
containment is exactly the remaining preservation boundary.
-/

namespace AlgebraicGeometry
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Dqc
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory

noncomputable section

universe u

/-- The affine relative-perfect objects that satisfy the concrete predicate
after every further morphism of test algebras. -/
noncomputable def
    affineFamilyUniversallyStableRelativePerfectCoreProperty
    {B : CommRingCat.{u}} (X : Under B) :
    (affineFamilyBoundedAboveProjectivePseudofunctor X).ObjectProperty :=
  Pseudofunctor.ObjectProperty.universallyStable
    (affineFamilyUniversallyGluableRelativePerfectCoreProperty X)

instance
    affineFamilyUniversallyStableRelativePerfectCoreProperty_isClosedUnderMapObj
    {B : CommRingCat.{u}} (X : Under B) :
    Pseudofunctor.ObjectProperty.IsClosedUnderMapObj
      (affineFamilyUniversallyStableRelativePerfectCoreProperty X) := by
  change Pseudofunctor.ObjectProperty.IsClosedUnderMapObj
    (Pseudofunctor.ObjectProperty.universallyStable
      (affineFamilyUniversallyGluableRelativePerfectCoreProperty X))
  infer_instance

/-- Universally base-change-stable relative-perfect affine families form an
actual groupoid-valued sub-pseudofunctor. -/
noncomputable def
    affineFamilyUniversallyStableRelativePerfectPseudofunctor
    {B : CommRingCat.{u}} (X : Under B) :
    Pseudofunctor (LocallyDiscrete (Under B)) Cat.{u + 1, u + 1} :=
  (affineFamilyUniversallyStableRelativePerfectCoreProperty X).fullsubcategory

/-- The universally stable relative-perfect pseudofunctor includes in the
ambient bounded-projective affine family pseudofunctor. -/
noncomputable def
    affineFamilyUniversallyStableRelativePerfectInclusion
    {B : CommRingCat.{u}} (X : Under B) :
    Pseudofunctor.StrongTrans
      (affineFamilyUniversallyStableRelativePerfectPseudofunctor X)
      (affineFamilyBoundedAboveProjectivePseudofunctor X) :=
  (affineFamilyUniversallyStableRelativePerfectCoreProperty X).ι

/-- Every universally base-change-stable object satisfies the concrete
relative-perfect and universally-gluable predicate in its original fiber. -/
theorem affineFamilyUniversallyStableRelativePerfect_le_fullLocus
    {B : CommRingCat.{u}} (X : Under B)
    (A : LocallyDiscrete (Under B)) :
    (affineFamilyUniversallyStableRelativePerfectCoreProperty X).prop A ≤
      (affineFamilyUniversallyGluableRelativePerfectCoreProperty X).prop A :=
  Pseudofunctor.ObjectProperty.universallyStable_le_self
    (affineFamilyUniversallyGluableRelativePerfectCoreProperty X) A

/-- Once arbitrary affine pullback is proved to preserve the full concrete
relative-perfect locus, the supported universally stable locus agrees with
it fiberwise. -/
theorem affineFamilyUniversallyStableRelativePerfect_eq_fullLocus
    {B : CommRingCat.{u}} (X : Under B)
    [Pseudofunctor.ObjectProperty.IsClosedUnderMapObj
      (affineFamilyUniversallyGluableRelativePerfectCoreProperty X)]
    (A : LocallyDiscrete (Under B)) :
    (affineFamilyUniversallyStableRelativePerfectCoreProperty X).prop A =
      (affineFamilyUniversallyGluableRelativePerfectCoreProperty X).prop A :=
  Pseudofunctor.ObjectProperty.universallyStable_eq_self
    (affineFamilyUniversallyGluableRelativePerfectCoreProperty X) A

end

end AlgebraicGeometry
