/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Circle
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Region
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Signature
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Slice

/-!
# Divisorial wall loci

The divisorial charges and discriminants live upstream under
`CentralCharge/Divisorial/`; support theorems live under `Support/Divisorial`.
This subtree owns only their wall loci, circle geometry, and finiteness.

Declarations use the strong-child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial`.

Geometric consumers — the adapters from a rational `NumericalRingData`, the
scalar extension, and the `P²`, smooth-quadric and K3 models — live under
`AlgebraicGeometry/Numerical/Stability/` and import this subtree.
-/
