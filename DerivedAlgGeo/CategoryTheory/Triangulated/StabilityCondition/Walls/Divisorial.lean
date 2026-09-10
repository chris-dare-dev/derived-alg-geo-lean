/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Charge
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Circle
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Coordinates
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Discriminant
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Mukai
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Region
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Signature
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Slice
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Support

/-!
# Divisorial central charges and their walls

The charge attached to a real divisor space with a symmetric intersection form,
an additive Chern-character triple valued in it, and two independent divisor
parameters `B` and `omega`.  Nothing in this subtree mentions a scheme, a
sheaf, a numerical intersection ring, or a stability condition: it is the
arithmetic that `Walls/Numerical/` performs in three compressed real
coordinates, done instead in the uncompressed divisor space.

Declarations use the strong-child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial`.

Geometric consumers — the adapters from a rational `NumericalRingData`, the
scalar extension, and the `P²`, smooth-quadric and K3 models — live under
`AlgebraicGeometry/Numerical/Stability/` and import this subtree.
-/
