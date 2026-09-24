/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.Bounded
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomFinite
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.CohomologyObjectProperty.HomVanishing
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Coproducts
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.SingleTriangle
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Opposite
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.LinearDual
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ModuleCatLocalization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor.Bounded
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.FGModuleCatInclusion
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.ExactFunctor.Coproducts
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Heart
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedHeart
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.GrothendieckGroup
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.GrothendieckGroup.Comparison
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Homology
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Ext
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KProjective
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomology
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLinear
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLocalization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLocalizationNaturality
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyFiniteResolutionLocalization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyDegreeZeroLocalization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyFiniteReplacementLocalization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyBoundedComplexLocalization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyIntLocalization
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.KFlatResolution
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedAboveProjective.Unitality

/-! # Derived categories of abelian categories

Extensions of Mathlib's `DerivedCategory C` for an abelian category `C`, at
Mathlib's path `Algebra/Homology/DerivedCategory/`: t-structure results,
exact functors, homology comparison, cohomology object properties,
bounded-derived Hom-finiteness from explicit heart Ext-finiteness, the
functoriality laws for short-exact triangles, the opposite-category
comparison, the exact derived lift of algebraic linear duality, `Ext`
adjunction and dimension shift, K-projective and bounded-above-projective
models, and the construction of derived tensor from a K-flat resolution.
Canonical localization of modules is naturally isomorphic, as an exact derived
functor, to scalar extension to the localization.
Degree-zero Hom-complex classes identify with derived-category morphisms when
the source is K-projective. For module complexes, a conditional localization
comparison assumes K-projectivity of both the source and its localization;
an ordinary integer-linear adapter is available separately.
A finite module over a noetherian ring has a chosen finite-term, bounded-above
projective resolution whose derived-category Hom-set map into a bounded-below
complex localizes. Its quasi-isomorphism comparison now gives localization of
the derived-category Hom-set map from the module's degree-zero complex into
a bounded-below complex.
A bounded-above complex of finite modules also has a chosen finite-projective
replacement whose derived-category Hom map into a bounded-below complex
localizes. The quasi-isomorphism comparison now transports this localization
to derived-category Hom-sets out of the original bounded-above complex.
The codomains remain degreewise localizations of the displayed complexes.
No internal derived-Hom or geometric base-change comparison is asserted.
Algebraic geometry supplies abelian categories such as `Coh X` and consumes
this API; it does not own the derived-category construction.
-/
