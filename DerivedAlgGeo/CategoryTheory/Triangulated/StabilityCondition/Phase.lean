/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Order
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer

/-!
# Phase transformations

Phase order theory and the transfer of phase data along functors.

## Main definitions

None in this module. Its children define the phase orders
`CategoryTheory.Triangulated.Slicing.Precedes` and
`CategoryTheory.Triangulated.Slicing.PrecedesWeak` (`Phase/Order/Basic.lean`)
and the preimage slicing `CategoryTheory.Triangulated.Slicing.preimage`
(`Phase/Transfer/Basic.lean`).

## Main results

None; this module re-exports its children `Phase/Order.lean` and
`Phase/Transfer.lean`.

## Implementation notes

The normalized phase shifts themselves are neutral -- a group of order
automorphisms of `ℝ` commuting with unit translation, mentioning no category --
and live at `Algebra/Order/NormalizedShift/`.

## References

This module cites no literature. It builds on
`CategoryTheory.Triangulated.Slicing`.

## Tags

slicing, phase, stability condition, transfer along functors
-/
