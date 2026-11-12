/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Action

/-!
# Lifted linear symmetries

The action of `G̃L⁺(2, ℝ)` on slicings, pre-stability conditions and stability
conditions, and its continuity.

## Main definitions

None in this module. Its children under `GLTilde/Action/`, in the namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`,
define the phase relabelling `relabel` and the actions `gltildeSlicingMulAction`,
`preMulAction` and `stabMulAction` of `GLTilde` on slicings, pre-stability
conditions and stability conditions.

## Main results

None; this module re-exports its child `GLTilde/Action.lean`.

## Implementation notes

The group itself -- the compatible-pair construction, its deck transformations,
the covering map, simple connectedness and the topological-group laws -- is not
here. It is neutral mathematics and lives beside the general-linear-group API,
under `LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover/`, with the
`+1`-equivariant order automorphisms of `ℝ` under
`Algebra/Order/NormalizedShift/` and the general product-of-coverings lemma
under `Topology/Covering/`.

## References

This module cites no literature. It builds on the group `GroupAction.GLTilde`
and the order automorphisms `GroupAction.NormalizedShift`, in the namespace
above.

## Tags

stability condition, group action, universal cover, general linear group
-/
