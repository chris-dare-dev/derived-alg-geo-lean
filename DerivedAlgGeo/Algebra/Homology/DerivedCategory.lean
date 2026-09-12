/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Bounded
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Coproducts
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.SingleTriangle
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Opposite
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.LinearDual
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor.Bounded
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Heart
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Homology
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KProjective
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KFlatResolution
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective.Unitality

/-! # Derived categories of abelian categories

Extensions of Mathlib's `DerivedCategory C` for an abelian category `C`, at
Mathlib's path `Algebra/Homology/DerivedCategory/`: t-structure results,
exact functors, homology comparison, cohomology object properties, the
functoriality laws for short-exact triangles, the opposite-category
comparison, the exact derived lift of algebraic linear duality, `Ext`
adjunction and dimension shift, K-projective and bounded-above-projective
models, and the construction of derived tensor from a K-flat resolution.
Algebraic geometry supplies abelian categories such as `Coh X` and consumes
this API; it does not own the derived-category construction.
-/
