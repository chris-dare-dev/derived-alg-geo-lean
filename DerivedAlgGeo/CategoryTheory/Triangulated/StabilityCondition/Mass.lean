/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mass.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mass.Subadditivity
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mass.Uniqueness

/-!
# Harder--Narasimhan mass

The mass `m_σ(E)` of an object with respect to a stability condition: the sum
of the norms of the central charges of its Harder--Narasimhan factors. This
module re-exports the definition, its subadditivity along distinguished
triangles, and its independence of the chosen HN filtration.

## Main definitions

None in this module. Its child `Mass/Basic.lean` defines
`CategoryTheory.Triangulated.HNFiltration.mass` and the choice-free
`CategoryTheory.Triangulated.stabilityMass`.

## Main results

None; this module re-exports its children `Mass/Basic.lean`,
`Mass/Subadditivity.lean` and `Mass/Uniqueness.lean`.

## Implementation notes

### Placement

Mass is a sibling of `Metric/`, not a child of it. It is an invariant of an
object and a stability condition, and its consumers are not only the distance
construction: the mass--Hom estimates under `StabilityCondition/MassHom/` use
mass without using the metric, and dynamical constructions do the same. That
independent consumer is what justifies the separate root; the metric
construction is downstream and imports this API.

The Euclidean content of the subadditivity proof does **not** live here. The
polygonal-path carrier, the real continuous linear functionals on `ℂ` and the
perimeter comparison are neutral planar geometry and own
`DerivedAlgGeo/Analysis/Convex/ComplexPolygonalPath/`; what stays below
`Subadditivity/` is the Harder--Narasimhan reading of those statements.

## References

This module cites no literature. It builds on
`CategoryTheory.Triangulated.HNFiltration` and
`CategoryTheory.Triangulated.StabilityCondition.WithClassMap`.

## Tags

stability condition, Harder--Narasimhan filtration, mass, central charge
-/
