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

This is the neutral core of MO1.12 (#1323): it is a group of order
isomorphisms of `ℝ`, it mentions no category, no slicing and no central
charge, and its two consumers are independent of each other -- the
universal cover of `GL⁺(2, ℝ)` below
`LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover/`, and the phase
relabelling of slicings below
`CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/Action/`.
-/
