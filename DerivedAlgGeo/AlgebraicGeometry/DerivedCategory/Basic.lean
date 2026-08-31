/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Derived categories of module sheaves on schemes

For a scheme `X`, Mathlib's abelian category `X.Modules` supplies the generic
derived category and its bounded subcategory. This module records those
scheme-specific specializations without introducing a second derived-category
construction.
-/

namespace AlgebraicGeometry.DerivedCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

/-- The standard derived-category localization for module sheaves on a
scheme. Registering it at the scheme-derived owner lets every geometric
consumer use the same instance instead of choosing one locally. -/
noncomputable instance (priority := 1100) schemeModulesHasDerivedCategory
    (X : Scheme.{u}) : HasDerivedCategory X.Modules :=
  HasDerivedCategory.standard X.Modules

/-- The same registered localization with the module-sheaf carrier exposed.
This syntactic form is needed by generic sheaf APIs whose category parameter
is written as `SheafOfModules X.ringCatSheaf` rather than `X.Modules`. -/
noncomputable instance (priority := 1100) schemeSheafOfModulesHasDerivedCategory
    (X : Scheme.{u}) :
    HasDerivedCategory (SheafOfModules X.ringCatSheaf) :=
  schemeModulesHasDerivedCategory X

/-- The derived category of sheaves of modules on a scheme, constructed using
Mathlib's standard localization at quasi-isomorphisms. -/
abbrev SchemeDerivedCategory (X : Scheme.{u}) :=
  DerivedCategory X.Modules

/-- The bounded derived category of sheaves of modules on a scheme, defined
using the canonical t-structure on `SchemeDerivedCategory X`. -/
abbrev SchemeBoundedDerivedCategory (X : Scheme.{u}) :=
  DerivedCategory.Bounded X.Modules

namespace SchemeDerivedCategory

/-- The localization functor from cochain complexes of module sheaves to the
scheme's derived category. -/
abbrev Q (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ SchemeDerivedCategory X :=
  DerivedCategory.Q

/-- The canonical inclusion of the bounded derived category into the
unbounded derived category. -/
abbrev boundedInclusion (X : Scheme.{u}) :
    SchemeBoundedDerivedCategory X ⥤ SchemeDerivedCategory X :=
  DerivedCategory.Bounded.ι

end SchemeDerivedCategory

end


end AlgebraicGeometry.DerivedCategory
