/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.Exact
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.GrothendieckGroup

/-!
# Dg enhancements of triangulated categories

Comparison between `H⁰` of a pretriangulated dg category and a *specified*
ordinary or triangulated category, and the transport of structure across it.

Two strengths are distinguished here, and the distinction is the point of the
directory. `Enhancement` is the underlying **H⁰ presentation**: an equivalence
`H⁰ A ≌ T` with `T` an arbitrary category and no compatibility asked of the
comparison. `Enhancement.Exact` is the refinement carrying the data the
literature means by an enhancement -- a `CommShift` on the comparison and the
proof that it is triangulated. The refinement is supplied data; nothing here
proves that a presentation admits one, and no declaration in this repository
asserts uniqueness of enhancements in either strength.

The intrinsic `H⁰` theory of a dg category -- shift, distinguished triangles,
cone diagrams, functor exactness -- is not here: it belongs to the definition
owner, `Algebra/Homology/DGCategory/Pretriangulated/H0/`. The realization for
Mathlib's homotopy category, and the proved agreement for the complexes model,
live with that object in `Algebra/Homology/HomotopyCategory/DGEnhancement/`.
-/
