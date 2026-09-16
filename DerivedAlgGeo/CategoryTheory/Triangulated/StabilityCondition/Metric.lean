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

Harder--Narasimhan mass is **not** here. It is the sibling
`StabilityCondition/Mass/`: mass is an invariant of an object and a stability
condition, and it has consumers besides this metric -- the mass--Hom estimates
under `StabilityCondition/MassHom/` are one. The distance construction is
downstream of mass, so the leaves below import the mass API they use
(`Metric/Distance/Basic.lean` and `Metric/Hausdorff.lean` do) and this umbrella
does not re-export a sibling root. MO1.13 (#1324).
-/
