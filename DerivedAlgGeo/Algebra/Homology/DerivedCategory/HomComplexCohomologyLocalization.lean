/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomologyLinear
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexCohomologyHomotopyNaturality
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# Conditional localization of derived-category Hom-sets

Degreewise module localization induces a map on derived-category morphisms.
The canonical class-to-homotopy comparison followed by `Qh` identifies this
map with degree-zero Hom-complex class localization when both the source and
its localization are K-projective. Under the separate class-localization
hypothesis, this map is a localization of `R`-modules.
Both module categories use their standard derived-category structures.

No preservation of arbitrary K-projectivity, internal derived-Hom object, or
geometric pullback comparison is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open scoped ModuleCat.Algebra CochainComplex.HomComplex

namespace CochainComplex.HomComplex

universe u

noncomputable section

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- The standard derived category on source modules, used locally. -/
private abbrev sourceDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _
/-- The standard derived category on localized modules, used locally. -/
private abbrev targetDerivedCategory : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _
attribute [local instance] sourceDerivedCategory targetDerivedCategory

private abbrev F := ModuleCat.localizedModuleFunctor.{u} S
private abbrev loc (X : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((F S).mapHomologicalComplex (.up ℤ)).obj X

/-- The canonical comparison between localizing a derived image and taking
the derived image of the degreewise localized complex. It is the component of
the existing `mapDerivedCategoryFactorsh` isomorphism. -/
def derivedLocalizationComparison (X : CochainComplex (ModuleCat.{u} R) ℤ) :
    (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategory.obj
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj X)) ≅
    DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj X)) :=
  ((F S).mapDerivedCategoryFactorsh).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj X)

/-- `R`-linearity of localization, used only to build the linear Hom map;
it is deliberately not registered as an instance for importers. -/
private abbrev localizedFunctorLinear : Functor.Linear R (F S) where
  map_smul {M N} f r := by
    apply ModuleCat.hom_ext
    ext y
    dsimp [F, ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap]
    simp only [map_smul, LinearMap.smul_apply]
    change r •
      ((IsLocalizedModule.mapExtendScalars S
        (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S)
        (Localization S)) f.hom) y =
      (algebraMap R (Localization S) r) •
        ((IsLocalizedModule.mapExtendScalars S
        (M.localizedModuleMkLinearMap S) (N.localizedModuleMkLinearMap S)
        (Localization S)) f.hom) y
    exact (IsScalarTower.algebraMap_smul (Localization S) r _).symm

/-- Degreewise localization on derived-category morphisms, conjugated by the
canonical comparison isomorphisms. This linear map is defined without any
K-projectivity hypothesis; the class comparison below needs both sources
K-projective. -/
def derivedHomLocalizedMap (P Q : CochainComplex (ModuleCat.{u} R) ℤ) :
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)) →ₗ[R]
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P)) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj Q))) where
  toFun f := (derivedLocalizationComparison S P).inv ≫
    (F S).mapDerivedCategory.map f ≫ (derivedLocalizationComparison S Q).hom
  map_add' f g := by simp
  map_smul' r f := by
    letI : Functor.Linear R (F S) := localizedFunctorLinear S
    simp

variable (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
  [P.IsKProjective]
  [CochainComplex.IsKProjective
    (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P)]

/-- The class-to-derived comparison commutes with degreewise localization.
Both source complexes must be K-projective; no boundedness is needed here. -/
theorem cohomologyClassLocalizedMap_derived_naturality
    (x : CohomologyClass P Q 0) :
    (ModuleCat.localizedModuleFunctor.{u} S).mapDerivedCategory.map
        (CohomologyClass.derivedCategoryHomAddEquiv P Q x) ≫
      (derivedLocalizationComparison S Q).hom =
    (derivedLocalizationComparison S P).hom ≫
      CohomologyClass.derivedCategoryHomAddEquiv
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj Q)
        (cohomologyClassLocalizedMap P Q S x) := by
  have hhom :
      cohomologyClassHomotopyAddEquiv (loc S P) (loc S Q)
          (cohomologyClassLocalizedMap P Q S x) =
        ((F S).mapHomotopyCategory (.up ℤ)).map
          (cohomologyClassHomotopyAddEquiv P Q x) := by
    exact congrArg (fun g => g x)
      (cohomologyClassLocalizedMap_homotopy_naturality P Q S)
  rw [CohomologyClass.derivedCategoryHomAddEquiv_apply_eq,
    CohomologyClass.derivedCategoryHomAddEquiv_apply_eq, hhom]
  simpa only [derivedLocalizationComparison, Iso.app_hom, Functor.comp_map,
    Functor.mapHomotopyCategory_map] using
      ((F S).mapDerivedCategoryFactorsh).hom.naturality
        (cohomologyClassHomotopyAddEquiv P Q x)

/-- The linear derived-Hom map agrees pointwise with class localization
through the two K-projective class-to-derived linear equivalences. -/
theorem derivedHomLocalizedMap_class_square (x : CohomologyClass P Q 0) :
    derivedHomLocalizedMap S P Q
        (CohomologyClass.derivedCategoryHomLinearEquiv (R := R) P Q x) =
      CohomologyClass.derivedCategoryHomLinearEquiv (R := R)
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P)
        (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj Q)
        (cohomologyClassLocalizedMap P Q S x) := by
  have h := cohomologyClassLocalizedMap_derived_naturality S P Q x
  change (derivedLocalizationComparison S P).inv ≫
    (F S).mapDerivedCategory.map
      (CohomologyClass.derivedCategoryHomAddEquiv P Q x) ≫
    (derivedLocalizationComparison S Q).hom =
      CohomologyClass.derivedCategoryHomAddEquiv (loc S P) (loc S Q)
        (cohomologyClassLocalizedMap P Q S x)
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- If the degree-zero class map is a localization, so is the induced
derived-category Hom map. K-projectivity of the localized source is an
explicit separate assumption. -/
theorem derivedHomLocalizedMap_isLocalized
    (hclass : IsLocalizedModule S (cohomologyClassLocalizedMap P Q S)) :
    IsLocalizedModule S (derivedHomLocalizedMap S P Q) := by
  letI := hclass
  let e₀ := CohomologyClass.derivedCategoryHomLinearEquiv (R := R) P Q
  let e₁ := CohomologyClass.derivedCategoryHomLinearEquiv (R := R)
    (loc S P) (loc S Q)
  haveI : IsLocalizedModule S
      (e₁.toLinearMap.comp (cohomologyClassLocalizedMap P Q S)) :=
    IsLocalizedModule.of_linearEquiv S _ e₁
  have hEq : (derivedHomLocalizedMap S P Q).comp e₀.toLinearMap =
      e₁.toLinearMap.comp (cohomologyClassLocalizedMap P Q S) := by
    apply LinearMap.ext
    intro x
    exact derivedHomLocalizedMap_class_square S P Q x
  haveI : IsLocalizedModule S
      ((derivedHomLocalizedMap S P Q).comp e₀.toLinearMap) := by
    rw [hEq]
    infer_instance
  haveI : IsLocalizedModule S
      (((derivedHomLocalizedMap S P Q).comp e₀.toLinearMap).comp
        e₀.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S _ e₀.symm
  convert this using 1
  apply LinearMap.ext
  intro z
  change (derivedHomLocalizedMap S P Q) z =
    (derivedHomLocalizedMap S P Q) (e₀ (e₀.symm z))
  rw [e₀.apply_symm_apply]

/-- The half-bounded finite-presentation class theorem transfers to
derived-category Hom-sets when both sources are K-projective. -/
theorem derivedHomLocalizedMap_isLocalized_of_bounded_above_below
    (c b : ℤ) [P.IsStrictlyLE b] [Q.IsStrictlyGE c]
    [∀ i : {p : ℤ // p ∈ Finset.Icc (c - 1) b},
      Module.FinitePresentation R (P.X i.1)] :
    IsLocalizedModule S (derivedHomLocalizedMap S P Q) :=
  derivedHomLocalizedMap_isLocalized S P Q
    (cohomologyClassLocalizedMap_isLocalized_of_bounded_above_below P Q S c b)

end

noncomputable section BoundedProjective

variable {R : Type u} [CommRing R] (S : Submonoid R)
  (P Q : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The standard source derived category for the bounded corollary. -/
private abbrev boundedSourceDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _
/-- The standard localized derived category for the bounded corollary. -/
private abbrev boundedTargetDerivedCategory : HasDerivedCategory (ModuleCat.{u} (Localization S)) :=
  HasDerivedCategory.standard _
attribute [local instance] boundedSourceDerivedCategory boundedTargetDerivedCategory

/-- Bounded-above termwise projectivity supplies K-projectivity of both
`P` and its degreewise localization. The finite-presentation condition is
separate and comes from the half-bounded Hom-complex localization theorem. -/
theorem derivedHomLocalizedMap_isLocalized_of_bounded_projective
    (c b : ℤ) [P.IsStrictlyLE b] [Q.IsStrictlyGE c]
    [∀ i : ℤ, Projective (P.X i)]
    [∀ i : {p : ℤ // p ∈ Finset.Icc (c - 1) b},
      Module.FinitePresentation R (P.X i.1)] :
    IsLocalizedModule S (derivedHomLocalizedMap S P Q) := by
  letI : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  letI : CochainComplex.IsStrictlyLE
      (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P) b :=
    inferInstance
  letI (i : ℤ) : Projective
      ((((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P).X i) :=
    (ModuleCat.localizedModuleFunctor.{u} S).projective_obj _
  letI : CochainComplex.IsKProjective
      (((ModuleCat.localizedModuleFunctor.{u} S).mapHomologicalComplex (.up ℤ)).obj P) :=
    CochainComplex.isKProjective_of_projective _ b
  exact derivedHomLocalizedMap_isLocalized_of_bounded_above_below S P Q c b

end BoundedProjective

end CochainComplex.HomComplex
