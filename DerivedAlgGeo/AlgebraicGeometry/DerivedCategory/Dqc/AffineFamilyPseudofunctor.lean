/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineGeometricCorePseudofunctor

/-!
# Affine derived families over a fixed affine morphism

For a fixed affine morphism `Spec R ⟶ Spec B`, a test `B`-algebra `A`
does not carry the family directly.  Its total space has coordinate ring the
pushout `R ⊗_B A`, and hence is the scheme pullback
`Spec R ×_{Spec B} Spec A`.

This file makes that geometry explicit.  It constructs the coordinate-ring
base-change functor on `Under B`, proves that its spectra form the required
pullback squares, and reindexes the geometric affine moduli-groupoid
pseudofunctor along this functor.  The result is the correctly indexed affine
substrate for the relative-perfect and universally-gluable restriction.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families
open AlgebraicGeometry.DerivedCategory
open AlgebraicGeometry.DerivedCategory.Families
open AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

/-- For `X : B ⟶ R`, send a test `B`-algebra `A` to the coordinate ring of
the affine base change `Spec R ×_{Spec B} Spec A`. -/
noncomputable def affineFamilyCoordinateRingFunctor
    {B : CommRingCat.{u}} (X : Under B) : Under B ⥤ CommRingCat.{u} :=
  Under.pushout X.hom ⋙ Under.forget X.right

/-- The coordinate ring of the affine family obtained from `X` over a test
`B`-algebra `A`. -/
abbrev AffineFamilyCoordinateRing {B : CommRingCat.{u}}
    (X A : Under B) : CommRingCat.{u} :=
  (affineFamilyCoordinateRingFunctor X).obj A

/-- The projection from the affine base-changed total space to the test
scheme. -/
noncomputable def affineFamilyToTestScheme {B : CommRingCat.{u}}
    (X A : Under B) :
    Spec (AffineFamilyCoordinateRing X A) ⟶ Spec A.right :=
  Spec.map (pushout.inl A.hom X.hom)

/-- The projection from the affine base-changed total space to the original
total space. -/
noncomputable def affineFamilyToTotalSpace {B : CommRingCat.{u}}
    (X A : Under B) :
    Spec (AffineFamilyCoordinateRing X A) ⟶ Spec X.right :=
  Spec.map (pushout.inr A.hom X.hom)

/-- The spectra used by the affine family construction form the actual
scheme pullback square over `Spec B`. -/
theorem affineFamily_isPullback {B : CommRingCat.{u}} (X A : Under B) :
    IsPullback (affineFamilyToTestScheme X A)
      (affineFamilyToTotalSpace X A) (Spec.map A.hom) (Spec.map X.hom) :=
  AlgebraicGeometry.isPullback_SpecMap_pushout A.hom X.hom

/-- The groupoid of geometric bounded-above projective complexes on the
affine base-changed total space. -/
abbrev AffineFamilyBoundedAboveProjectiveModuliFiber
    {B : CommRingCat.{u}} (X A : Under B) :=
  AffineBoundedAboveProjectiveModuliFiber
    (AffineFamilyCoordinateRing X A)

/-- Pullback of affine derived families along a morphism of test
`B`-algebras. -/
noncomputable def affineFamilyBoundedAboveProjectivePullback
    {B : CommRingCat.{u}} (X : Under B) {A A' : Under B} (f : A ⟶ A') :
    AffineFamilyBoundedAboveProjectiveModuliFiber X A ⥤
      AffineFamilyBoundedAboveProjectiveModuliFiber X A' :=
  affineGeometricBoundedAboveProjectiveCorePullback
    ((affineFamilyCoordinateRingFunctor X).map f)

/-- The affine geometric moduli-groupoid pseudofunctor, reindexed over test
`B`-algebras by forming the actual affine base-changed total space. -/
noncomputable def affineFamilyBoundedAboveProjectivePseudofunctor
    {B : CommRingCat.{u}} (X : Under B) :
    Pseudofunctor (LocallyDiscrete (Under B)) Cat.{u + 1, u + 1} :=
  Pseudofunctor.comp
    (affineFamilyCoordinateRingFunctor X).toPseudofunctor
    affineGeometricBoundedAboveProjectiveCorePseudofunctor

/-- A transition in the reindexed family pseudofunctor is the concrete
arbitrary affine derived pullback along the induced map of pushout rings. -/
theorem affineFamilyBoundedAboveProjectivePseudofunctor_map_toFunctor
    {B : CommRingCat.{u}} (X : Under B) {A A' : Under B} (f : A ⟶ A') :
    ((affineFamilyBoundedAboveProjectivePseudofunctor X).map
      (.mk f)).toFunctor = affineFamilyBoundedAboveProjectivePullback X f :=
  rfl

/-- Forget an affine family moduli groupoid to the honest `Dqc` category of
its base-changed total space. -/
noncomputable def affineFamilyBoundedAboveProjectiveModuliForget
    {B : CommRingCat.{u}} (X A : Under B) :
    AffineFamilyBoundedAboveProjectiveModuliFiber X A ⥤
      SchemeQuasicoherentDerivedCategory
        (Spec (AffineFamilyCoordinateRing X A)) :=
  affineBoundedAboveProjectiveModuliForget
    (AffineFamilyCoordinateRing X A)

end

end CategoryTheory.Triangulated.StabilityCondition.Families
