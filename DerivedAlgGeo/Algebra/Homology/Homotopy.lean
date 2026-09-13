/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Homotopy.Sigma
import DerivedAlgGeo.Algebra.Homology.Homotopy.HomologyModel
import DerivedAlgGeo.Algebra.Homology.Homotopy.ModuleCatFormality
import DerivedAlgGeo.Algebra.Homology.Homotopy.FiniteCohomologyPresentation
import DerivedAlgGeo.Algebra.Homology.Homotopy.FiniteCohomologyPresentationOfSupport

/-!
# Homotopies

Extensions of Mathlib's `Homotopy` between chain maps: homotopies on the
summands of a coproduct of complexes assemble to a homotopy on the coproduct,
complexes of vector spaces split noncanonically as their homology, and explicit
finite cohomology presentations record chosen finite homotopy splittings.
-/
