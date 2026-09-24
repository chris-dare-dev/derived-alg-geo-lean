/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.Bounded
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.Coproducts
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyLinear
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyNaturality
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexLocalization
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexPostcomp

/-!
# The homotopy category

Extensions of Mathlib's `HomotopyCategory`: the bounded homotopy category,
coproducts in the homotopy category and their preservation by the quotient
functor, and the dg enhancement of the homotopy category by the dg category
of cochain complexes. Hom-complex localization and a map-natural linear adapter
for its cohomology classes are also owned here. The enhancement *interface* is a
structure on an abstract triangulated category and lives in
`CategoryTheory/Triangulated/DGEnhancement/`; its realization for this
particular object lives here, with the object.
-/
