/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineRGammaPlusHom

/-!
# Negative-bound affine derived Hom probe

This compile-only example ensures the injective-model transport accepts an
explicit negative lower bound. The proof uses the same evaluation map.

## Main definitions

No new definition is exported; the example checks the public equivalence.

## Main results

The evaluation map remains bijective with lower bound `-2`.

## Implementation notes

The example instantiates the bound and invokes the exact public map's
additive equivalence.

## References

The affine derived-sections comparison in this repository.

## Tags

affine scheme, derived sections, negative bound, development probe
-/

open CategoryTheory AlgebraicGeometry
attribute [local instance] HasDerivedCategory.standard

universe u
noncomputable section

example (R : CommRingCat.{u}) (M : DerivedCategory.Plus (Spec R).Modules)
    [M.IsGE (-2)] : Function.Bijective
      (AlgebraicGeometry.Cohomology.affineRGammaPlusEvalAddHom R M) :=
  (AlgebraicGeometry.Cohomology.affineRGammaPlusEvalAddEquiv R M).bijective
