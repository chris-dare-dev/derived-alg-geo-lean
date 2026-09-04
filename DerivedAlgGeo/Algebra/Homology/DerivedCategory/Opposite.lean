/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Opposites of derived categories

For an abelian category `C`, using a derived contravariant functor with source
`(DerivedCategory C)ᵒᵖ` requires comparing that category with
`DerivedCategory Cᵒᵖ`. The pinned Mathlib supplies the corresponding
opposite-category constructions on complexes and the localization machinery,
but does not yet bundle this derived-category equivalence.

`OppositeComparison` records exactly that remaining comparison. It is generic
categorical data: a later construction may provide it for any abelian
category, while module and geometric duality consume the same root.
-/

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe w v u

open CategoryTheory

namespace CategoryTheory.DerivedCategory

variable (C : Type u) [Category.{v} C] [Abelian C] [Abelian Cᵒᵖ]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} Cᵒᵖ]

/-- Explicit comparison between taking the opposite before and after forming
a derived category. -/
structure OppositeComparison where
  /-- The equivalence from the opposite derived category to the derived
  category of the opposite abelian category. -/
  equivalence : (DerivedCategory C)ᵒᵖ ≌ DerivedCategory Cᵒᵖ

end CategoryTheory.DerivedCategory
