/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.FourierMukai

/-!
# Compatibility import for stability conditions in families

This leaf umbrella re-exports the generic categorical interfaces, neutral
scheme-derived realizations, and stability-specific geometric adapters that
formerly shared one families umbrella. It provides a staged migration path for
clients that need the former combined surface. New code should import the
narrow owner directly.

This import preserves module availability, not retired qualified declaration
names. Neutral categorical family declarations use
`CategoryTheory.Triangulated.Families`; weak-family declarations use
`CategoryTheory.Triangulated.WeakStabilityCondition.Families`.
-/
