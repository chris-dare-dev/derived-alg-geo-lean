/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ConeFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.MorphismCone
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.HomCohomologyEuler
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearEvaluationK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationConeK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ObjectTwistK0

/-!
# Reading `H⁰` in a presented category, and in its Grothendieck group

The declarations here need something beyond the dg category: either a *chosen*
ordinary category and the comparison equivalence of an `Enhancement`, or the
Grothendieck group of the triangulated structure.

## Main definitions

None; this module re-exports its children.

## Main results

None; this module re-exports its children.

## Implementation notes

The intrinsic side -- the shift, the distinguished triangles, the functorial
cone diagrams and the exactness of `DGFunctor.h0` -- lives with its definition
owner, `Algebra/Homology/DGCategory/Pretriangulated/H0/`, and nothing there
imports this directory.

`ConeFunctor` and `MorphismCone` transport dg cones across a comparison, and
carry that comparison's shift and exactness compatibilities as hypotheses. The
four `K0` modules read triangles and twists in `K₀`, and consume
`CategoryTheory/Triangulated/GrothendieckGroup/`.

## References

The subtree builds on `CategoryTheory.Enhancement` and `CategoryTheory.DGFunctor.h0`.

## Tags

dg enhancement, H⁰, dg cone, Grothendieck group, triangulated category
-/
