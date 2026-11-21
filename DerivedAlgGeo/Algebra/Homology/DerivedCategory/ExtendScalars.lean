/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.ChangeOfRings
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.Homology
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived extension of scalars along a flat ring map

Extension of scalars along a flat map of commutative rings `f : R ⟶ S` is an exact functor
`ModuleCat R ⥤ ModuleCat S` (`ModuleCat.preservesFiniteLimits_extendScalars_of_flat`), so
Mathlib's `Functor.mapDerivedCategory` turns it into a triangulated functor
`ModuleCat.extendScalarsDerivedOfFlat f hf : D(R) ⥤ D(S)`. On a complex it is computed termwise:
`ModuleCat.extendScalarsDerivedOfFlatFactors`. It commutes with cohomology:
`ModuleCat.extendScalarsDerivedOfFlatHomologyIso`.

Flatness is used only to make the functor exact. Derived base change along an arbitrary ring map
needs a derived tensor product and is not constructed here.
-/

open CategoryTheory Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace ModuleCat

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (hf : f.hom.Flat)

/-- Derived extension of scalars along a flat ring map `f : R ⟶ S`: the functor
`D(R) ⥤ D(S)` induced by the exact functor `ModuleCat.extendScalars f.hom`. -/
noncomputable def extendScalarsDerivedOfFlat :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} S) :=
  haveI := preservesFiniteLimits_extendScalars_of_flat hf
  (extendScalars.{u, u, u} f.hom).mapDerivedCategory

noncomputable instance : (extendScalarsDerivedOfFlat f hf).CommShift ℤ :=
  haveI := preservesFiniteLimits_extendScalars_of_flat hf
  inferInstanceAs ((extendScalars.{u, u, u} f.hom).mapDerivedCategory.CommShift ℤ)

instance : (extendScalarsDerivedOfFlat f hf).IsTriangulated :=
  haveI := preservesFiniteLimits_extendScalars_of_flat hf
  inferInstanceAs ((extendScalars.{u, u, u} f.hom).mapDerivedCategory.IsTriangulated)

/-- Derived extension of scalars along a flat ring map is computed termwise on complexes. -/
noncomputable def extendScalarsDerivedOfFlatFactors :
    DerivedCategory.Q ⋙ extendScalarsDerivedOfFlat f hf ≅
      (extendScalars.{u, u, u} f.hom).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  haveI := preservesFiniteLimits_extendScalars_of_flat hf
  (extendScalars.{u, u, u} f.hom).mapDerivedCategoryFactors

/-- Derived extension of scalars along a flat ring map commutes with cohomology:
`Hⁿ(K ⊗_R S) ≅ Hⁿ(K) ⊗_R S`. -/
noncomputable def extendScalarsDerivedOfFlatHomologyIso
    (K : DerivedCategory (ModuleCat.{u} R)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} S) n).obj
        ((extendScalarsDerivedOfFlat f hf).obj K) ≅
      (extendScalars f.hom).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj K) :=
  mapDerivedCategoryHomologyIso (extendScalars.{u, u, u} f.hom) inferInstance
    (preservesFiniteLimits_extendScalars_of_flat hf) inferInstance K n

end ModuleCat
