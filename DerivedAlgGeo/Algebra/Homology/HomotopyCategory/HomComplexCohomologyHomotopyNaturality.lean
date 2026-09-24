/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyClassLocalization

/-!
# Degree-zero Hom-complex classes and localization in the homotopy category

Mathlib identifies `CohomologyClass K L 0` with morphisms from `K` to `L⟦0⟧`
in the homotopy category. Composing with `shiftFunctorZero` removes that shift.
On representatives this equivalence sends a cocycle `z` to the homotopy class
of `Cocycle.homOf z`.

The degree-zero class-localization map commutes with the functor on homotopy
categories induced by degreewise module localization. This additive square
requires no boundedness, finite-presentation, or K-projectivity hypotheses.
It is not a derived-Hom localization or geometric base-change theorem.

The earlier `CohomologyClass.derivedCategoryHomAddEquiv` internally spells out
the same class-to-homotopy, zero-shift factor before applying `Qh`. A downstream
factorization is definitionally equal; this module deliberately does not import
the derived-category comparison. A later refactor can extract the shared factor
to a neutral HomotopyCategory leaf before both consumers import it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory
open scoped ModuleCat.Algebra

namespace CochainComplex.HomComplex

universe u v

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (K L : CochainComplex C ℤ)

/-- Degree-zero Hom-complex cohomology classes as morphisms of the homotopy
category, using the canonical zero-shift isomorphism. -/
def cohomologyClassHomotopyAddEquiv :
    CohomologyClass K L 0 ≃+
      ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj L) := by
  let e : (HomotopyCategory.quotient C (.up ℤ)).obj (L⟦(0 : ℤ)⟧) ≅
      (HomotopyCategory.quotient C (.up ℤ)).obj L :=
    (HomotopyCategory.quotient C (.up ℤ)).mapIso
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).app L)
  let e₁ : ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj (L⟦(0 : ℤ)⟧)) ≃+
      ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj L) :=
    { toFun := fun f => f ≫ e.hom
      invFun := fun g => g ≫ e.inv
      left_inv := by intro f; simp
      right_inv := by intro g; simp
      map_add' := by intro f g; simp [Preadditive.add_comp] }
  exact CohomologyClass.homAddEquiv.trans e₁

private theorem cocycle_equivHomShift_symm_comp_shiftZero (z : Cocycle K L 0) :
    Cocycle.equivHomShift.symm z ≫
      (shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app L =
      Cocycle.homOf z := by
  ext i
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
    Cochain.rightShift_v, CochainComplex.shiftFunctorZero_hom_app_f]
  -- The remaining inverse/forward `XIsoOfEq` composite contains dependent casts.
  -- Ordinary `rw` fails at instances transparency; `erw` closes it.
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The class of a degree-zero cocycle corresponds to the homotopy class of its
associated chain map. -/
@[simp] theorem cohomologyClassHomotopyAddEquiv_mk (z : Cocycle K L 0) :
    cohomologyClassHomotopyAddEquiv K L (CohomologyClass.mk z) =
      (HomotopyCategory.quotient C (.up ℤ)).map z.homOf := by
  change CohomologyClass.homAddEquiv (CohomologyClass.mk z) ≫
    (HomotopyCategory.quotient C (.up ℤ)).map
      ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app L) =
    (HomotopyCategory.quotient C (.up ℤ)).map z.homOf
  rw [CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk]
  rw [← Functor.map_comp]
  rw [cocycle_equivHomShift_symm_comp_shiftZero K L z]
  rfl

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
