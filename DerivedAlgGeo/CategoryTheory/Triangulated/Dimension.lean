/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.GenerationTime
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.Rouquier
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.ExtensionClosureComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension.Composition

/-! # Dimension theory of triangulated categories

The numerical layer over Mathlib's triangulated envelopes: generation time, the `ℕ∞`-valued
count of extension steps one object property needs to reach another. Rouquier dimension,
comparisons with the owner's extension closure, the composition law for iterated envelopes, and
transport along triangulated functors append here. The composition law is multiplicative in
Rouquier's indexing, and generation time plus one is submultiplicative.

Generic triangulated vocabulary: nothing under this umbrella imports `AlgebraicGeometry/**` or the
stability track.
-/
