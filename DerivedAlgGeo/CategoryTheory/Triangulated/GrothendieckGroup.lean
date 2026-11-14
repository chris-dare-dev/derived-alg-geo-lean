/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/

import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Biproduct
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.RankOne
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.HeartComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.HomFiniteWitness
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Realization

/-!
# The triangulated Grothendieck group

`K₀` of a triangulated category, its presentation by generators and
three-term relations, and its functoriality in triangulated functors.

## Main definitions

None: this umbrella re-exports its children. Among them are
`CategoryTheory.Triangulated.K₀` and `CategoryTheory.Triangulated.K₀.of`
(`Basic`), `CategoryTheory.Triangulated.K₀.map` (`Functorial`),
`CategoryTheory.Triangulated.K₀.Realization` (`Realization`),
`CategoryTheory.Triangulated.K₀.EulerForm` (`EulerForm`) and
`CategoryTheory.K₀Ab.toAmbient` (`HeartComparison`).

## Main results

None; this module re-exports its children.

## Implementation notes

Nothing here mentions a slicing, a phase, or a stability condition. These
modules are generic triangulated theory, so they sit under
`Triangulated/GrothendieckGroup/` rather than under the stability tree, and a
consumer of a Grothendieck group does not inherit stability conditions as a
dependency.

## References

The library's `GrothendieckPresentation`.

## Tags

Grothendieck group, triangulated category, distinguished triangle
-/
