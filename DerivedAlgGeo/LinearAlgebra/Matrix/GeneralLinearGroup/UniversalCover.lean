/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.UniversalCover.Basic
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.UniversalCover.ComplexRepresentation
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.UniversalCover.Fibre
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.UniversalCover.Map
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.UniversalCover.SourceTopology
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.UniversalCover.Surjectivity
import DerivedAlgGeo.LinearAlgebra.Matrix.GeneralLinearGroup.UniversalCover.TopologicalGroup

/-!
# The universal cover of `GL⁺(2, ℝ)`

`GLTilde`, Bridgeland's concrete presentation of `G̃L⁺(2, ℝ)` as compatible
pairs, together with the covering-space development on it: the `ℤ` fibre and
its deck transformations, surjectivity of the matrix projection, the global
chart that makes the source contractible and simply connected, the
covering-map property, and the topological-group instance.

## Main definitions

None: this umbrella re-exports its children. The group itself is `GLTilde`, in
the namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`.

## Main results

None of its own; it re-exports `GLTilde.universalCoverData` and
`exact_deckHom_toMatHom`, described below.

## Implementation notes

### What the name does and does not assert

`GLTilde` is a *name*; the universal-cover statement is a *theorem*, and the
two are kept apart deliberately. The statement this development proves is the
explicit conjunction

* `GLTilde.universalCoverData` -- `IsCoveringMap GLTilde.mat`,
  `Function.Surjective GLTilde.mat` and `SimplyConnectedSpace GLTilde`; and
* `exact_deckHom_toMatHom` -- the `ℤ` deck group as the kernel of the
  projection.

Mathlib has no bundled universal-cover predicate at the pinned revision, so
there is nothing upstream to instantiate and no covering theorem may be read
off the identifier. Cite those two declarations.

### Placement

This development is independent of stability conditions: nothing here
mentions a category, a slicing, a heart or a central charge, and no module
below this directory imports the stability tree or `AlgebraicGeometry/`. The
action on slicings, charges and stability conditions -- and the π phase
convention as it is consumed there -- is below
`CategoryTheory/Triangulated/StabilityCondition/Symmetry/GLTilde/Action/`.

The declarations live in the
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`
namespace of that action, which keeps their names fixed; the divergence
between path and namespace is deliberate, not an oversight.

## References

* Bridgeland, *Stability conditions on triangulated categories*, Ann. of Math.
  (2007), §8.

## Tags

universal cover, general linear group, covering map, simply connected, deck transformation
-/
