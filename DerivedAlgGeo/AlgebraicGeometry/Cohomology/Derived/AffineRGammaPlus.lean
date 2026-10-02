/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import DerivedAlgGeo.AlgebraicGeometry.Modules.AB
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Extensions

/-!
# Bounded-below derived affine global sections

The affine global-sections functor from module sheaves on `Spec R` to modules
has a right derived functor on Mathlib's bounded-below derived category. Its
unit carries Mathlib's right-derived universal property. The construction
uses injective resolutions of all module sheaves, with no quasicoherence
assumption on their terms or on the input.
Finite-limit preservation of affine sections specializes the generic H⁰
unit theorem to all affine module sheaves, without a quasicoherence premise.

## Main definitions

This file introduces no carrier or category. The additive structure needed
for the existing affine global-sections functor is local to this construction.

## Main results

* `AlgebraicGeometry.Cohomology.affineRGammaPlus` is the bounded-below right
  derived global-sections functor.
* `AlgebraicGeometry.Cohomology.affineRGammaPlusUnit` is its derived unit.
* `AlgebraicGeometry.Cohomology.affineRGammaPlusHomologyZeroSingleIso` is the
  pointwise comparison on degree-zero single objects.
* `AlgebraicGeometry.Cohomology.affineRGammaPlusHomologyZeroSingleNatIso`
  is the natural comparison on degree-zero single objects.
* `AlgebraicGeometry.Cohomology.affineRGammaPlus_isRightDerivedFunctor` records
  the right-derived universal property.
* `AlgebraicGeometry.Cohomology.isIso_homologyZero_map_affineRGammaPlusUnit_of_isStrictlyGE_zero`
  gives the H⁰ unit isomorphism on strictly nonnegative complexes.

## Implementation notes

Finite-product preservation makes the affine sections functor additive. Mathlib's
`CategoryTheory.Functor.rightDerivedFunctorPlus` constructs the functor and its unit from
that fact and enough injectives in the category of module sheaves.
Finite-limit preservation discharges both outgoing-kernel premises of the
generic H⁰ theorem. The degree-zero single comparison is natural and agrees
with its pointwise predecessor. No natural H⁰ identification on arbitrary
bounded-below Dqc objects follows.

## References

Mathlib's `CategoryTheory.Functor.rightDerivedFunctorPlus` and
`CategoryTheory.Functor.rightDerivedFunctorPlusUnit` at the pinned revision;
the affine source functor is `AlgebraicGeometry.affineΓ`.

## Tags

affine scheme, global sections, right derived functor, bounded below
-/

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Cohomology

private theorem affineGamma_additive (R : CommRingCat.{u}) :
    (AlgebraicGeometry.affineΓ R).Additive :=
  Functor.additive_of_preserves_binary_products _

attribute [local instance] affineGamma_additive

/-- Right-derived global sections of module sheaves on an affine scheme,
restricted to Mathlib's bounded-below derived categories. The definition
itself uses no H⁰ comparison or unbounded Dqc identification. -/
noncomputable def affineRGammaPlus (R : CommRingCat.{u}) :
    DerivedCategory.Plus (Spec R).Modules ⥤ DerivedCategory.Plus (ModuleCat R) :=
  (AlgebraicGeometry.affineΓ R).rightDerivedFunctorPlus

/-- Mathlib's injective-resolution construction supplies this comparison from
homotopy-level affine sections to the bounded-below derived functor. -/
noncomputable def affineRGammaPlusUnit (R : CommRingCat.{u}) :
    (AlgebraicGeometry.affineΓ R).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ affineRGammaPlus R :=
  (AlgebraicGeometry.affineΓ R).rightDerivedFunctorPlusUnit

/-- This universal property is inherited by unfolding the specialization to
Mathlib's right-derived functor; no affine acyclicity theorem is needed here. -/
instance affineRGammaPlus_isRightDerivedFunctor (R : CommRingCat.{u}) :
    (affineRGammaPlus R).IsRightDerivedFunctor (affineRGammaPlusUnit R)
      (HomotopyCategory.Plus.quasiIso (Spec R).Modules) := by
  dsimp only [affineRGammaPlus, affineRGammaPlusUnit]
  infer_instance

/-- Affine sections preserve finite limits, so they preserve both the input's
degree-zero outgoing kernel and those in its nonnegative injective resolutions.
The generic right-derived unit theorem then gives an H⁰ isomorphism. -/
theorem isIso_homologyZero_map_affineRGammaPlusUnit_of_isStrictlyGE_zero
    (R : CommRingCat.{u}) (K : CochainComplex.Plus (Spec R).Modules)
    [K.obj.IsStrictlyGE 0] :
    IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).map
      ((affineRGammaPlusUnit R).app
        ((HomotopyCategory.Plus.quotient (Spec R).Modules).obj K))) := by
  have h := (AlgebraicGeometry.affineΓ R)
    |>.isIso_homologyZero_map_rightDerivedFunctorPlusUnit_of_isStrictlyGE_zero
      K inferInstance (fun _ _ _ => inferInstance)
  exact h

/-- On an arbitrary affine module sheaf, invert H⁰ of the derived unit on
its degree-zero single and normalize the source to ordinary affine sections.
Its agreement with the natural comparison below is proved separately. -/
noncomputable def affineRGammaPlusHomologyZeroSingleIso
    (R : CommRingCat.{u}) (M : (Spec R).Modules) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).obj
      ((affineRGammaPlus R).obj
        ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj M)) ≅
      (AlgebraicGeometry.affineΓ R).obj M := by
  haveI : CategoryTheory.Limits.PreservesFiniteLimits (AlgebraicGeometry.affineΓ R) :=
    inferInstance
  exact (AlgebraicGeometry.affineΓ R)
    |>.rightDerivedFunctorPlusHomologyZeroSingleIsoOfPreservesFiniteLimits M

/-- Affine sections preserve finite limits, so the generic natural H⁰
comparison specializes to all module sheaves on an affine scheme. -/
noncomputable def affineRGammaPlusHomologyZeroSingleNatIso
    (R : CommRingCat.{u}) :
    (DerivedCategory.Plus.singleFunctor (Spec R).Modules 0 ⋙ affineRGammaPlus R) ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0 ≅
    AlgebraicGeometry.affineΓ R := by
  haveI : CategoryTheory.Limits.PreservesFiniteLimits (AlgebraicGeometry.affineΓ R) :=
    inferInstance
  exact (AlgebraicGeometry.affineΓ R)
    |>.rightDerivedFunctorPlusHomologyZeroSingleNatIsoOfPreservesFiniteLimits

/-- The natural affine comparison recovers the earlier pointwise comparison
at every module sheaf by the generic component-agreement theorem. -/
theorem affineRGammaPlusHomologyZeroSingleNatIso_app
    (R : CommRingCat.{u}) (M : (Spec R).Modules) :
    (affineRGammaPlusHomologyZeroSingleNatIso R).app M =
      affineRGammaPlusHomologyZeroSingleIso R M := by
  haveI : CategoryTheory.Limits.PreservesFiniteLimits (AlgebraicGeometry.affineΓ R) :=
    inferInstance
  exact (AlgebraicGeometry.affineΓ R)
    |>.rightDerivedFunctorPlusHomologyZeroSingleNatIsoOfPreservesFiniteLimits_app M

end AlgebraicGeometry.Cohomology
