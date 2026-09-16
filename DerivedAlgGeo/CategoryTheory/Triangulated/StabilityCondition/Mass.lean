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
of the norms of the central charges of its Harder--Narasimhan factors.

## Placement

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
MO1.13 (#1324).
-/
