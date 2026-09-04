/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Lift
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Orthogonal

/-! # Object properties

Repository-owned extensions of Mathlib's `ObjectProperty`, at the path Mathlib
defines it. The full subcategory a property cuts out is Mathlib's; what is added
here is the restriction of a functor, and of an adjunction, to the subcategories
picked out by a property and its inverse image, and closure of a left orthogonal
under colimits.
-/
