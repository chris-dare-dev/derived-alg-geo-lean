/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyClassLocalization
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyHomotopy

/-!
# Degree-zero class localization in the homotopy category

The degree-zero class-localization map commutes with the functor on homotopy
categories induced by degreewise module localization. This additive square
requires no boundedness, finite-presentation, or K-projectivity hypotheses.
It is not a derived-Hom localization or geometric base-change theorem.

The class-to-homotopy equivalence and its cocycle formula come from the neutral
`HomComplexCohomologyHomotopy` leaf; only the localization square is proved here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped ModuleCat.Algebra

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R]
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (S : Submonoid R)

private abbrev localizedComplex (E : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj E

private def localizedCocycle (z : Cocycle P Q 0) :
    Cocycle (localizedComplex S P) (localizedComplex S Q) 0 :=
  Cocycle.mk ((cochainLocalizedMap P Q 0 S) z.1) 1 rfl (by
    rw [← cochainLocalizedMap_delta P Q 0 S 1 z.1, Cocycle.δ_eq_zero, map_zero])

private theorem localizedCocycle_homOf (z : Cocycle P Q 0) :
    (localizedCocycle P Q S z).homOf =
      ((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).map
        z.homOf := by
  ext i
  rfl

private theorem cohomologyClassLocalizedMap_mk_aux (z : Cocycle P Q 0) :
    (cohomologyClassLocalizedMap P Q S) (CohomologyClass.mk z) =
      CohomologyClass.mk (localizedCocycle P Q S z) := by
  rfl

/-- The localization square on a cocycle representative. By
`cohomologyClassHomotopyAddEquiv_mk`, the source morphism is the homotopy class
of `z.homOf`, and the target is the class of its degreewise localization. -/
theorem cohomologyClassLocalizedMap_homotopy_mk (z : Cocycle P Q 0) :
    cohomologyClassHomotopyAddEquiv
      (localizedComplex S P) (localizedComplex S Q)
      ((cohomologyClassLocalizedMap P Q S) (CohomologyClass.mk z)) =
    ((ModuleCat.localizedModuleFunctor.{u} S).mapHomotopyCategory (.up ℤ)).map
      (cohomologyClassHomotopyAddEquiv P Q (CohomologyClass.mk z)) := by
  rw [cohomologyClassLocalizedMap_mk_aux,
    cohomologyClassHomotopyAddEquiv_mk, cohomologyClassHomotopyAddEquiv_mk,
    Functor.mapHomotopyCategory_map, localizedCocycle_homOf]

/-- Degree-zero class localization commutes, as an additive map, with
degreewise localization on homotopy-category morphisms. No finiteness or
K-projectivity assumptions are involved. -/
theorem cohomologyClassLocalizedMap_homotopy_naturality :
    (cohomologyClassHomotopyAddEquiv
      (localizedComplex S P) (localizedComplex S Q)).toAddMonoidHom.comp
      (cohomologyClassLocalizedMap P Q S).toAddMonoidHom =
    (Functor.mapAddHom
      ((ModuleCat.localizedModuleFunctor.{u} S).mapHomotopyCategory (.up ℤ))).comp
      (cohomologyClassHomotopyAddEquiv P Q).toAddMonoidHom := by
  ext x
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective x
  exact cohomologyClassLocalizedMap_homotopy_mk P Q S z

end

end CochainComplex.HomComplex
