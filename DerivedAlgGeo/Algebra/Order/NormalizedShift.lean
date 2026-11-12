/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Order.NormalizedShift.Basic
import DerivedAlgGeo.Algebra.Order.NormalizedShift.UniformContinuity

/-!
# Order automorphisms of `ℝ` commuting with unit translation

The group `NormalizedShift` of increasing bijections `f : ℝ ≃o ℝ` with
`f (φ + 1) = f φ + 1`, and the uniform continuity that `+1`-equivariance
forces.

## Main definitions

None: this umbrella re-exports its children. The group itself is
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.NormalizedShift`.

## Main results

None; this module re-exports its children, among them
`NormalizedShift.uniformContinuous`, in the same namespace as the group.

## Implementation notes

This is a neutral core: it is a group of order isomorphisms of `ℝ`, it
mentions no category, no slicing and no central charge, and its two consumers
are independent of each other -- the universal cover of `GL⁺(2, ℝ)` below
`LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover/`, and the phase
relabelling of slicings below
`CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/Action/`.

## References

Mathlib's `OrderIso` and `UniformContinuous`.

## Tags

order isomorphism, translation equivariance, uniform continuity
-/
