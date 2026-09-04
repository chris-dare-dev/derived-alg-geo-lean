/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Sheaf cohomology on a site

Extensions of Mathlib's `CategoryTheory/Sites/SheafCohomology/`: the Čech
complex of a covering family, its bicomplex with an injective resolution, and
the comparison with derived sheaf cohomology. Every signature here uses an
arbitrary site; the results for sheaves on a topological space, where a
compact-open basis or flasqueness enters, live in `Topology/Sheaves/Cech/`.
-/
