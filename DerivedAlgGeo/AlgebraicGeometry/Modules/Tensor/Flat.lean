/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Stalk
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import Mathlib.RingTheory.Flat.CategoryTheory

/-!
# Finite-limit preservation by flat scheme-module tensor

A module sheaf flat over the identity has flat stalk modules. The natural
tensor-stalk comparison transports Mathlib's categorical flatness theorem
through module stalks, which jointly detect finite-limit preservation.

## Main definitions

This module introduces no new definitions. It uses the existing scheme-module
tensor functor and the natural stalk comparison.

## Main results

* `AlgebraicGeometry.Scheme.Modules.tensorLeftFunctor_preservesFiniteLimits_of_isFlatOverId`
  gives finite-limit preservation for tensoring by a fixed identity-flat sheaf.

## Implementation notes

The proof takes a finite-limit theorem in each stalk module category across
the natural tensor-stalk isomorphism, then applies stalkwise detection.

## References

This uses `Module.Flat.iff_preservesFiniteLimits_tensorLeft`,
`AlgebraicGeometry.Scheme.Modules.isFlatOverId_iff_stalkwiseFlat`, and
`AlgebraicGeometry.Scheme.Modules.preservesFiniteLimits_of_stalkwise`.

## Tags

module sheaf, flatness, tensor, finite limits
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry

universe u
noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

private theorem tensorLeftFunctor_preservesFiniteLimits_of_stalkwiseFlat
    (X : Scheme.{u}) (L : X.Modules)
    (hflat : ∀ x : X, Module.Flat (X.presheaf.stalk x)
      ((moduleStalkFunctor X x).obj L)) :
    PreservesFiniteLimits (tensorLeftFunctor L) := by
  apply preservesFiniteLimits_of_stalkwise (tensorLeftFunctor L)
  intro x
  haveI : PreservesFiniteLimits
      (tensorLeft ((moduleStalkFunctor X x).obj L)) :=
    (Module.Flat.iff_preservesFiniteLimits_tensorLeft _).mp (hflat x)
  haveI : PreservesFiniteLimits (moduleStalkFunctor X x) :=
    moduleStalkFunctor_preservesFiniteLimits X x
  haveI : PreservesFiniteLimits
      (moduleStalkFunctor X x ⋙
        tensorLeft ((moduleStalkFunctor X x).obj L)) := inferInstance
  exact preservesFiniteLimits_of_natIso
    (tensorLeftFunctorStalkNatIso X L x).symm

/-- Tensoring by a scheme-module sheaf flat over the identity preserves
finite limits. This is a property of the fixed tensor factor, not a
flatness assumption on the input diagram. -/
theorem tensorLeftFunctor_preservesFiniteLimits_of_isFlatOverId
    (X : Scheme.{u}) (L : X.Modules) (hL : IsFlatOver (𝟙 X) L) :
    PreservesFiniteLimits (tensorLeftFunctor L) :=
  tensorLeftFunctor_preservesFiniteLimits_of_stalkwiseFlat X L
    ((isFlatOverId_iff_stalkwiseFlat X L).mp hL)

end AlgebraicGeometry.Scheme.Modules
