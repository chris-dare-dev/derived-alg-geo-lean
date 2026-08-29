/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families
import DerivedAlgGeo.AlgebraicGeometry.StabilityCondition.Families

/-!
# Compatibility import for stability conditions in families

This leaf umbrella re-exports both the generic categorical interfaces and the
scheme-specific realizations that formerly shared the CategoryTheory umbrella.
It provides a staged migration path for clients that need the former combined
surface. New code should import the narrow owner directly.
-/
