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

Declarations in this subtree use
`AlgebraicGeometry.StabilityCondition.Families`, matching their geometric
owner while remaining consumers of the generic categorical family interfaces.
-/
