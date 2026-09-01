/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.Bounded
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement

/-!
# The homotopy category

Extensions of Mathlib's `HomotopyCategory`: the bounded homotopy category, and
the dg enhancement of the homotopy category by the dg category of cochain
complexes. The enhancement *interface* is a structure on an abstract
triangulated category and lives in
`CategoryTheory/Triangulated/DGEnhancement/`; its realization for this
particular object lives here, with the object.
-/
