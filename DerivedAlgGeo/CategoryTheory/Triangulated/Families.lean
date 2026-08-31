/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Families.BaseChange

/-!
# Families of triangulated categories

Generic contravariant pseudofunctorial families of triangulated categories,
their pullback functors, and their unit and composition coherence. Ordinary
strict functors enter through `TriangulatedFiberFamily.ofFunctor`. Stability
data on such fibers is added by the weak- and Bridgeland-stability descendants.
Neutral moduli boundedness belongs to the independent
`CategoryTheory/Moduli/` root.

The neutral declarations use the matching
`CategoryTheory.Triangulated.Families` namespace.
-/
