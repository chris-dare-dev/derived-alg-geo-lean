/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.Scheme
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.RelativeHN
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.SchemeSemistableLocus
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.GeometricBaseChange
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.FiniteTypeGeometry
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families.InducingPullback

/-!
# Geometric stability conditions in families

Algebraic-geometric realizations that actually depend on the abstract stability
interfaces in
`DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`.
Neutral scheme-derived categories, `Dqc`, pullback, and kernels live under
`DerivedAlgGeo.AlgebraicGeometry.DerivedCategory`.

The declarations retain their established
`CategoryTheory.Triangulated.StabilityCondition.Families` namespace during the
module migration. This keeps theorem names stable while module ownership and
dependency direction become explicit.
-/
