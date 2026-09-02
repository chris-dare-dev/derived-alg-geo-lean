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

/-! ### The chosen localization

Mathlib's `HasDerivedCategory C` records a *chosen* localization at the
quasi-isomorphisms, and its guidance is that the standard large localization
`HasDerivedCategory.standard C` be introduced locally where a construction needs
it, never registered globally. There is therefore no global instance here: this
file and every geometric consumer that spells a derived category declare
`attribute [local instance] HasDerivedCategory.standard` after
their preamble, so that the instance argument elaborated into every signature is
literally `HasDerivedCategory.standard _` and agrees across files and across the
two spellings `X.Modules` and `SheafOfModules X.ringCatSheaf`, which are
reducibly equal. A consumer that wants a different localization takes
`[HasDerivedCategory C]` as a hypothesis instead. -/

attribute [local instance] HasDerivedCategory.standard

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
