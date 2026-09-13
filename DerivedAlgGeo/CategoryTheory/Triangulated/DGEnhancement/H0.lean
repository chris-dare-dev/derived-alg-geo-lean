/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Shift
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.HomCohomology
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.HomCohomologyEuler
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearEvaluationK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearObjectTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearObjectTwistAdjunction
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.LinearObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ShiftedFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionCone
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.AdjunctionConePresentation
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationCone
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.NaturalTransformationConeK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ObjectTwist
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Triangle
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.ConeFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.MorphismCone

/-!
# The triangulated homotopy category of a dg category

Shifts and distinguished triangles on `H⁰` induced by pretriangulated dg
structure, the functorial dg cone diagrams they carry, presentation of dg
adjunction counit triangles on equivalent ordinary categories, and the
transport of dg-functor capabilities to `H⁰`.
-/
