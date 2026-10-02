/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import DerivedAlgGeo.AlgebraicGeometry.Modules.AB
import DerivedAlgGeo.AlgebraicGeometry.Modules.Quasicoherent.Extensions

/-!
# Bounded-below derived affine global sections

The affine global-sections functor from module sheaves on `Spec R` to modules
has a right derived functor on Mathlib's bounded-below derived category. Its
unit carries Mathlib's right-derived universal property. The construction
uses injective resolutions of all module sheaves, with no quasicoherence
assumption on their terms or on the input.

## Main definitions

This file introduces no carrier or category. The additive structure needed
for the existing affine global-sections functor is local to this construction.

## Main results

* `AlgebraicGeometry.Cohomology.affineRGammaPlus` is the bounded-below right
  derived global-sections functor.
* `AlgebraicGeometry.Cohomology.affineRGammaPlusUnit` is its derived unit.
* `AlgebraicGeometry.Cohomology.affineRGammaPlus_isRightDerivedFunctor` records
  the right-derived universal property.

## Implementation notes

Finite-product preservation makes the affine sections functor additive. Mathlib's
`CategoryTheory.Functor.rightDerivedFunctorPlus` constructs the functor and its unit from
that fact and enough injectives in the category of module sheaves.

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
restricted to Mathlib's bounded-below derived categories. This definition
makes no H⁰ comparison or unbounded Dqc identification. -/
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

end AlgebraicGeometry.Cohomology
