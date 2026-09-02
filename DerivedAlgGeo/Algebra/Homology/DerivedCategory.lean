/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Opposite
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.LinearDual
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Homology
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KProjective
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective.Unitality

/-! # Derived categories of abelian categories

Extensions of Mathlib's `DerivedCategory C` for an abelian category `C`, at
Mathlib's path `Algebra/Homology/DerivedCategory/`: t-structure results,
exact functors, homology comparison, cohomology object properties, the
opposite-category comparison, the exact derived lift of algebraic linear
duality, `Ext` adjunction and dimension shift, and K-projective and
bounded-above-projective models. Algebraic geometry supplies abelian
categories such as `Coh X` and consumes this API; it does not own the
derived-category construction.
-/
