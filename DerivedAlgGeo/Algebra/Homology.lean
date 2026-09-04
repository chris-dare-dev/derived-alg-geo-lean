/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory
import DerivedAlgGeo.Algebra.Homology.DerivedCategory
import DerivedAlgGeo.Algebra.Homology.HomologicalComplexLimits
import DerivedAlgGeo.Algebra.Homology.Homotopy
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory
import DerivedAlgGeo.Algebra.Homology.Localization
import DerivedAlgGeo.Algebra.Homology.ShortComplex
import DerivedAlgGeo.Algebra.Homology.Subcomplex
import DerivedAlgGeo.Algebra.Homology.SpectralSequence
import DerivedAlgGeo.Algebra.Homology.EulerCharacteristic

/-!
# Homological algebra

Extensions of Mathlib's `Algebra/Homology/`, at Mathlib's paths: derived
categories of abelian categories, the homotopy category and its dg
enhancement, spectral sequences of filtered and total complexes, the
bespoke dg-category class built on Mathlib's `HomComplex`, and the
degreewise description of coproducts of complexes with the homotopies
they carry.

A derived category is a triangulated category, and Mathlib still files it
here rather than under `CategoryTheory/Triangulated/`, because this is where
the construction from complexes lives. This repository follows that choice so
that an upstream pull request is a copy. Structures on an *abstract*
triangulated category, including the dg-enhancement interface and stability
conditions, stay under `CategoryTheory/Triangulated/`.
-/
