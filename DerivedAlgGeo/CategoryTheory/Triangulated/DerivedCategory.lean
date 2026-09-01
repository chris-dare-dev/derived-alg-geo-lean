/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.TStructure
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.Opposite
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.LinearDual
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.ExactFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.Homology
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.Ext
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.KProjective
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.BoundedAboveProjective
import DerivedAlgGeo.CategoryTheory.Triangulated.DerivedCategory.BoundedAboveProjective.Unitality

/-! # Derived categories of abelian categories

Generic results about derived categories belong to the triangulated category
layer. This includes opposite-category comparison data and the exact derived
lift of algebraic linear duality. Algebraic geometry supplies abelian
categories such as `Coh X` and then consumes this API; it does not own the
derived-category construction.
-/
