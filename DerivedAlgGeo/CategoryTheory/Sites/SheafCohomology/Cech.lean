/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.Bicomplex
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.ComplexNaturality
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.Contractible
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.Differential
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.InitialPage
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.ModuleForget
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.SmallSiteResolution
import DerivedAlgGeo.CategoryTheory.Sites.SheafCohomology.Cech.TotalComparison

/-!
# Čech complexes on a site

The Čech nerve and cosimplicial object of a covering family, its cochain
complex and bicomplex against an injective resolution, contractibility, the
first page, the forgetful comparison to abelian groups, the total-complex
comparison with derived sheaf cohomology, and injective resolutions on a
small site. Every signature here uses an arbitrary Grothendieck topology.
The results that mention a topological space and its opens, including the
global-sections comparison, live in `Topology/Sheaves/Cech/`; `Comparison`
and `ComplexNaturality` import that half, as Mathlib's `Sites/Spaces.lean`
imports `Topology/Sets/Opens`.
-/
