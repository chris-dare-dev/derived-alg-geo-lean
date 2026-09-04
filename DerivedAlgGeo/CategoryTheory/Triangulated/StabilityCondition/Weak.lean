/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Families
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.HarderNarasimhan
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Metric
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Charge

/-!
# Weak stability conditions

The dependency parent for Bridgeland stability: weak central charges,
Harder--Narasimhan theory, support, and tilting. It is the child `Weak/` of
`StabilityCondition/`, the way `PseudoMetricSpace` is `MetricSpace/Pseudo/`
in Mathlib: the directory is named for the canonical concept and the
weakened variant by its adjective, while the dependency runs the other way.
Nothing below `Weak/` imports the Bridgeland theory, and this umbrella is
importable without it. Declaration namespaces remain
`CategoryTheory.Triangulated.WeakStabilityCondition`.
-/
