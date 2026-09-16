/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.Basic
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.Shift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.Triangle
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.ConeFunctor
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.HomCohomology
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.Functor
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.FunctorTransport
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.ShiftedFunctor
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.NaturalTransformationCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.NaturalTransformationConeShift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.AdjunctionCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.AdjunctionComparison
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.AdjunctionConePresentation
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.AdjunctionCotwistPresentation
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.ObjectTwist
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.LinearObjectTwist
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0.LinearObjectTwistAdjunction

/-!
# The pretriangulated `H⁰` of a dg category

The intrinsic triangulated theory of `H⁰ C` for a pretriangulated dg category
`C`: the zero object, the shift, the distinguished triangles built from dg
cones, the functorial cone diagrams, and the exactness of the functors and
natural transformations `DGFunctor.h0` produces.

Every statement below is about `C` alone. No ordinary category has been chosen,
no comparison equivalence appears, and nothing here imports an enhancement
consumer, a scheme realization or a stability module. Comparing this structure
with a *specified* triangulated category is
`CategoryTheory/Triangulated/DGEnhancement/`; realizing it on Mathlib's homotopy
category is `Algebra/Homology/HomotopyCategory/DGEnhancement/`.

The Grothendieck-group readings of these triangles -- Euler forms, `K₀` classes
of twists and cones -- consume `CategoryTheory/Triangulated/GrothendieckGroup/`
and stay with it, below `DGEnhancement/H0/`. They are downstream of this root,
not part of it.
-/
