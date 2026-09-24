/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomology
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyHomotopy
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyLinear
import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# Linear degree-zero class-to-derived comparison

For a K-projective source in an `R`-linear abelian category, the existing
additive comparison factors through the canonical class-to-homotopy
equivalence and is `R`-linear. The class module instance is scoped; this is a
comparison of Hom-sets, not an internal derived-Hom construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped CochainComplex.HomComplex

namespace CochainComplex.HomComplex.CohomologyClass

universe u v w

noncomputable section

variable {R : Type u} [CommRing R]
  {C : Type v} [Category.{w} C] [Abelian C] [Linear R C] [HasDerivedCategory C]
  (K L : CochainComplex C ℤ) [K.IsKProjective]

/-- The existing derived comparison is the canonical class-to-homotopy
equivalence followed by `Qh` on morphisms. -/
theorem derivedCategoryHomAddEquiv_apply_eq (x : CohomologyClass K L 0) :
    derivedCategoryHomAddEquiv K L x =
      DerivedCategory.Qh.map (cohomologyClassHomotopyAddEquiv K L x) := by
  rfl

/-- The degree-zero class-to-derived-Hom equivalence is linear for the scoped
class-module action. Only the source is required to be K-projective. -/
def derivedCategoryHomLinearEquiv :
    CohomologyClass K L 0 ≃ₗ[R]
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj K) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj L)) :=
  { (derivedCategoryHomAddEquiv K L) with
    map_smul' := by
      intro r x
      obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
      rw [← cohomologyClass_mk_smul K L 0 r z]
      change derivedCategoryHomAddEquiv K L (CohomologyClass.mk (r • z)) =
        r • derivedCategoryHomAddEquiv K L (CohomologyClass.mk z)
      simp only [derivedCategoryHomAddEquiv_apply_eq,
        cohomologyClassHomotopyAddEquiv_mk]
      have h : (r • z).homOf = r • z.homOf := by
        ext i
        rfl
      rw [h]
      simp only [Functor.map_smul] }

end

end CochainComplex.HomComplex.CohomologyClass
