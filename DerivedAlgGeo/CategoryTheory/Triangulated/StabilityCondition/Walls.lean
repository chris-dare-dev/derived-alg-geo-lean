/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Alignment
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Rotation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Spherical
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Threefold

/-!
# Wall loci in stability spaces

Central-charge families are owned upstream by `StabilityCondition/CentralCharge`;
this subtree adds determinant-alignment loci and their geometry.  `Rotation.lean`
is the one child that reads the tilting lane: it identifies the charge-family
phase rotation with the tilt rotation that `Weak/Tilting/` already owns, which
is why the rotation is not in the stability-neutral charge-family root.

Declarations in this subtree use the strong-child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall`.
-/
