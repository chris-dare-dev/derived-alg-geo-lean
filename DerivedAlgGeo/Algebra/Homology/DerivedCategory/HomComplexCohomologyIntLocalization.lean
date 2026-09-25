/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLocalization
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyIntLocalization

/-!
# Canonical integer localization of derived-category Hom-sets

At `R = ℤ`, the generic derived-Hom localization map is relinearized with
the ordinary integer actions on its source and target additive Hom groups.
It is a module localization under the canonical integer class-map hypothesis.
The bounded-projective specialization proves that hypothesis and supplies
both K-projectivity instances. This does not construct internal derived Hom.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex

noncomputable section

variable (S : Submonoid ℤ)

/-- The standard derived category on integer modules, used locally. -/
private abbrev intSourceDerivedCategory : HasDerivedCategory (ModuleCat ℤ) :=
  HasDerivedCategory.standard _
/-- The standard derived category on localized integer modules, used locally. -/
private abbrev intTargetDerivedCategory : HasDerivedCategory (ModuleCat (Localization S)) :=
  HasDerivedCategory.standard _
attribute [local instance] intSourceDerivedCategory intTargetDerivedCategory

private abbrev loc (X : CochainComplex (ModuleCat ℤ) ℤ) :=
  ((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj X

/-- The generic map on derived-category morphisms, equipped with the
canonical integer-module actions rather than the scoped linear actions. -/
def derivedHomLocalizedIntMap (P Q : CochainComplex (ModuleCat ℤ) ℤ) :
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) →ₗ[ℤ]
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj P)) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj Q))) :=
  (derivedHomLocalizedMap S P Q).toAddMonoidHom.toIntLinearMap

variable (P Q : CochainComplex (ModuleCat ℤ) ℤ)
  [P.IsKProjective]
  [CochainComplex.IsKProjective
    (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj P)]

/-- The canonical integer-linear map agrees with class localization through
the canonical integer-linear class-to-derived equivalences. -/
theorem derivedHomLocalizedIntMap_class_square (x : CohomologyClass P Q 0) :
    derivedHomLocalizedIntMap S P Q
        (CohomologyClass.derivedCategoryHomIntLinearEquiv P Q x) =
      CohomologyClass.derivedCategoryHomIntLinearEquiv
        (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj Q)
        (cohomologyClassLocalizedMap P Q S x) := by
  change derivedHomLocalizedMap S P Q
      (CohomologyClass.derivedCategoryHomLinearEquiv (R := ℤ) P Q x) =
    CohomologyClass.derivedCategoryHomLinearEquiv (R := ℤ)
      (loc S P) (loc S Q) (cohomologyClassLocalizedMap P Q S x)
  exact derivedHomLocalizedMap_class_square S P Q x

/-- A canonical integer class-localization hypothesis transfers to the
canonical integer map on derived-category Hom groups. -/
theorem derivedHomLocalizedIntMap_isLocalized
    (hclass : IsLocalizedModule S
      (cohomologyClassLocalizedMap P Q S).toAddMonoidHom.toIntLinearMap) :
    IsLocalizedModule S (derivedHomLocalizedIntMap S P Q) := by
  letI := hclass
  let e₀ := CohomologyClass.derivedCategoryHomIntLinearEquiv P Q
  let e₁ := CohomologyClass.derivedCategoryHomIntLinearEquiv (loc S P) (loc S Q)
  haveI : IsLocalizedModule S
      (e₁.toLinearMap.comp
        (cohomologyClassLocalizedMap P Q S).toAddMonoidHom.toIntLinearMap) :=
    IsLocalizedModule.of_linearEquiv S _ e₁
  have hEq : (derivedHomLocalizedIntMap S P Q).comp e₀.toLinearMap =
      e₁.toLinearMap.comp
        (cohomologyClassLocalizedMap P Q S).toAddMonoidHom.toIntLinearMap := by
    apply LinearMap.ext
    intro x
    exact derivedHomLocalizedIntMap_class_square S P Q x
  haveI : IsLocalizedModule S
      ((derivedHomLocalizedIntMap S P Q).comp e₀.toLinearMap) := by
    rw [hEq]
    infer_instance
  haveI : IsLocalizedModule S
      (((derivedHomLocalizedIntMap S P Q).comp e₀.toLinearMap).comp
        e₀.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S _ e₀.symm
  convert this using 1
  apply LinearMap.ext
  intro z
  change (derivedHomLocalizedIntMap S P Q) z =
    (derivedHomLocalizedIntMap S P Q) (e₀ (e₀.symm z))
  rw [e₀.apply_symm_apply]

/-- The half-bounded finite-presentation class result gives canonical
integer localization of derived Homs when both sources are K-projective. -/
theorem derivedHomLocalizedIntMap_isLocalized_of_bounded_above_below
    (c b : ℤ) [P.IsStrictlyLE b] [Q.IsStrictlyGE c]
    [∀ i : {p : ℤ // p ∈ Finset.Icc (c - 1) b},
      Module.FinitePresentation ℤ (P.X i.1)] :
    IsLocalizedModule S (derivedHomLocalizedIntMap S P Q) :=
  derivedHomLocalizedIntMap_isLocalized S P Q
    (cohomologyClassLocalizedIntMap_isLocalized P Q S c b)

end

noncomputable section BoundedProjective

variable (S : Submonoid ℤ) (P Q : CochainComplex (ModuleCat ℤ) ℤ)

/-- The standard source derived category for the bounded integer corollary. -/
private abbrev boundedIntSourceDerivedCategory : HasDerivedCategory (ModuleCat ℤ) :=
  HasDerivedCategory.standard _
/-- The standard target derived category for the bounded integer corollary. -/
private abbrev boundedIntTargetDerivedCategory : HasDerivedCategory (ModuleCat (Localization S)) :=
  HasDerivedCategory.standard _
attribute [local instance] boundedIntSourceDerivedCategory boundedIntTargetDerivedCategory

/-- An ordinary integer-module caller can use this bounded-above result
without opening either scoped Hom-complex or `ModuleCat.Algebra` actions. -/
theorem derivedHomLocalizedIntMap_isLocalized_of_bounded_projective
    (c b : ℤ) [P.IsStrictlyLE b] [Q.IsStrictlyGE c]
    [∀ i : ℤ, Projective (P.X i)]
    [∀ i : {p : ℤ // p ∈ Finset.Icc (c - 1) b},
      Module.FinitePresentation ℤ (P.X i.1)] :
    IsLocalizedModule S (derivedHomLocalizedIntMap S P Q) := by
  letI : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  letI : CochainComplex.IsStrictlyLE
      (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj P) b :=
    inferInstance
  letI (i : ℤ) : Projective
      ((((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj P).X i) :=
    (ModuleCat.localizedModuleFunctor S).projective_obj _
  letI : CochainComplex.IsKProjective
      (((ModuleCat.localizedModuleFunctor S).mapHomologicalComplex (.up ℤ)).obj P) :=
    CochainComplex.isKProjective_of_projective _ b
  exact derivedHomLocalizedIntMap_isLocalized_of_bounded_above_below S P Q c b

end BoundedProjective

end CochainComplex.HomComplex
