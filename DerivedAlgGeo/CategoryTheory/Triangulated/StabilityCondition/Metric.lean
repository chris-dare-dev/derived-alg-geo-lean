/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Distance
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Isometry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Hausdorff

/-!
# Metric geometry of stability conditions

Stability distance, isometries, topology, and Hausdorff separation of the
stability space.

## Main definitions

None in this module. Its child `Metric/Distance/Basic.lean` defines the
extended distance `CategoryTheory.Triangulated.stabilityDist` on stability
conditions with a class map.

## Main results

None; this module re-exports its children `Metric/Distance.lean`,
`Metric/Isometry.lean` and `Metric/Hausdorff.lean`.

## Implementation notes

Harder--Narasimhan mass is **not** here. It is the sibling
`StabilityCondition/Mass/`: mass is an invariant of an object and a stability
condition, and it has consumers besides this metric -- the mass--Hom estimates
under `StabilityCondition/MassHom/` are one. The distance construction is
downstream of mass, so the leaves below import the mass API they use
(`Metric/Distance/Basic.lean` and `Metric/Hausdorff.lean` do) and this umbrella
does not re-export a sibling root.

## References

This module cites no literature. It builds on
`CategoryTheory.Triangulated.stabilityMass` and
`CategoryTheory.Triangulated.StabilityCondition.WithClassMap`.

## Tags

stability condition, stability space, metric, distance, isometry
-/
