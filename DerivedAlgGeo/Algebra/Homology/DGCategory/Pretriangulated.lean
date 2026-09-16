/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionComparison
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ConeExactness
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Cone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ConeCategory
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Functor
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.FunctorCategory
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.FunctorCategoryShift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.H0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.HomogeneousLift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.HomogeneousShift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Lift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearShiftIso
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearShiftHomology
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearObjectTwist
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.LinearObjectTwistAdjunction
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationShift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ObjectTwist
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Rotate
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ShiftIso

/-!
# Pretriangulated dg categories

The internal dg data of zero objects, shifts, and cones, together with the
intrinsic triangulated theory of `H⁰` it induces (`Pretriangulated/H0/`).

Comparison with a *specified* triangulated category -- an equivalence, and the
shift and exactness compatibilities that make it an enhancement -- is owned by
`DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement`, and the homotopy-
category realization by
`DerivedAlgGeo.Algebra.Homology.HomotopyCategory.DGEnhancement`. Both import
this root; neither is imported by it.
-/
