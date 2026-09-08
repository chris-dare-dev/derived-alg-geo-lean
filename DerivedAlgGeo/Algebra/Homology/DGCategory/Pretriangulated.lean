/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Basic
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.AdjunctionCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Cone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ConeCategory
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Functor
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.HomogeneousLift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Lift
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationCone
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.Rotate
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.ShiftIso

/-!
# Pretriangulated dg categories

The internal dg data of zero objects, shifts, and cones. Its triangulated
realization on `H⁰` is owned by
`DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement`.
-/
