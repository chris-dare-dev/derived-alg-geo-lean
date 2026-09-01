/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Basic
import DerivedAlgGeo.Algebra.Homology.DGCategory.Functor
import DerivedAlgGeo.Algebra.Homology.DGCategory.H0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Instances
import DerivedAlgGeo.Algebra.Homology.DGCategory.Linear
import DerivedAlgGeo.Algebra.Homology.DGCategory.LinearH0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Opposite
import DerivedAlgGeo.Algebra.Homology.DGCategory.Product
import DerivedAlgGeo.Algebra.Homology.DGCategory.Shift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated
import DerivedAlgGeo.Algebra.Homology.DGCategory.Model

/-!
# Dg categories

Dg categories, their dg functors and elementary constructions, their internal
pretriangulated refinement, and raw dg models.

`DGCategory` is a bespoke class built on Mathlib's `CochainComplex.HomComplex`
(ADR-0010, ADR-0011); it does not extend `EnrichedCategory`, because the
ℤ-graded cochain complexes it would enrich over are not monoidal at the pin.
By definition site it therefore lives here, beside the homotopy category it
enhances, and not under `CategoryTheory/Enriched/`. If the enriched encoding
(ADR-0010 Option A′) lands, the subtree moves there in the same change.

The triangulated category carried by `H⁰` of a pretriangulated dg category and
the notion of a dg enhancement are exported separately from
`DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement`.
-/
