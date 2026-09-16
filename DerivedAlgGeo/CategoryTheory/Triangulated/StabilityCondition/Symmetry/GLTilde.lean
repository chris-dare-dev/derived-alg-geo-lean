/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Action

/-!
# Lifted linear symmetries

The action of `G̃L⁺(2, ℝ)` on slicings, pre-stability conditions and stability
conditions, and its continuity.

The group itself -- the compatible-pair construction, its deck transformations,
the covering map, simple connectedness and the topological-group laws -- is not
here. It is neutral mathematics and lives beside the general-linear-group API,
under `LinearAlgebra/Matrix/GeneralLinearGroup/UniversalCover/`, with the
`+1`-equivariant order automorphisms of `ℝ` under
`Algebra/Order/NormalizedShift/` and the general product-of-coverings lemma
under `Topology/Covering/`. MO1.12 (#1323), cutover-ledger row 08.
-/
