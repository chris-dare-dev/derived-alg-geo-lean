/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.HomComplexCohomology
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineRGammaPlusEvaluation
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexSingleModule
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Derived.AffineHypercohomology
import DerivedAlgGeo.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Affine derived Hom and bounded-below derived sections

The canonical evaluation map from morphisms out of the structure sheaf to
degree-zero bounded-below derived affine sections agrees, on injective models,
with the Hom-complex class map through degreewise affine sections. The proof
retains the incoming degree-minus-one boundaries in homology.

## Main definitions

* `AlgebraicGeometry.Cohomology.affineRGammaPlusEvalAddEquiv`
  packages the existing canonical evaluation map as an additive equivalence
  on bounded-below derived objects.
* `AlgebraicGeometry.Cohomology.affineRGammaPlusDqcHomologyZeroSectionsAddEquiv`
  composes its inverse with the existing pointwise Hom-to-H⁰ sections
  comparison for Dqc objects.

General arbitrary-pullback preservation remains separate.

## Main results

The application lemmas show that both equivalences use the specified
evaluation and pointwise Hom-to-sections maps.

## Implementation notes

The internal comparison uses the canonical cycles and homology quotient, the
right-derived unit on injective complexes, and the existing represented
Hom-complex and K-injective comparisons. No source K-projectivity or
strict-nonnegative bound is assumed.

## References

Mathlib's `HomComplexSingle.lean`, `KInjective.lean`,
`DerivabilityStructureInjectives.lean`, and `HomologySequence.lean` at pin
`520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

affine scheme, derived global sections, derived Hom, injective complexes
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CochainComplex.HomComplex
attribute [local instance] HasDerivedCategory.standard

-- The Plus, homotopy and localized single-source models unfold only under
-- reducible transparency during the canonical cycles comparison.
set_option backward.isDefEq.respectTransparency false
universe u
noncomputable section
namespace AffineRGammaPlusHomProof

variable (R : CommRingCat.{u})
private local instance : (affineΓ R).Additive :=
  Functor.additive_of_preserves_binary_products _

private abbrev U := Scheme.Modules.unit (Spec R)
private abbrev S : CochainComplex.Plus (Spec R).Modules :=
  ⟨(CochainComplex.singleFunctor (Spec R).Modules 0).obj (U R), ⟨0, inferInstance⟩⟩
private abbrev H := DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0
private abbrev G := (affineΓ R).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

-- The concrete source normalization: localized degreewise sections of a single,
-- then homology of the mapped single, then the usual single homology comparison.
private def sourceIso :
    (H R).obj ((G R).obj ((HomotopyCategory.Plus.quotient _).obj (S R))) ≅
      (affineΓ R).obj (U R) :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app _ ≪≫
    HomologicalComplex.homologyMapIso
      (((affineΓ R).mapCochainComplexSingleFunctor 0).app (U R)) 0 ≪≫
    (HomologicalComplex.homologyFunctorSingleIso (ModuleCat R) (.up ℤ) 0).app _

private theorem unitClass_normalization :
    Cohomology.affineRGammaPlusUnitClass R =
      ((H R).map ((Cohomology.affineRGammaPlusUnit R).app
        ((HomotopyCategory.Plus.quotient _).obj (S R)))).hom
        ((sourceIso R).inv.hom
          ((Scheme.Modules.unitHomTopLinearEquiv (U R)) (𝟙 (U R)))) := by
  rfl

-- This square is the actual evaluation map, no injectivity or lower bound zero.
private theorem eval_on_chain_map (K : CochainComplex.Plus (Spec R).Modules)
    (f : S R ⟶ K) :
    Cohomology.affineRGammaPlusEvalAddHom R (DerivedCategory.Plus.Q.obj K)
      (DerivedCategory.Plus.Q.map f) =
    ((H R).map ((Cohomology.affineRGammaPlusUnit R).app
      ((HomotopyCategory.Plus.quotient _).obj K))).hom
      (((H R).map ((G R).map
        ((HomotopyCategory.Plus.quotient _).map f))).hom
        ((sourceIso R).inv.hom
          ((Scheme.Modules.unitHomTopLinearEquiv (U R)) (𝟙 (U R))))) := by
  have h := congrArg
    (fun k => ((H R).map k).hom ((sourceIso R).inv.hom
      ((Scheme.Modules.unitHomTopLinearEquiv (U R)) (𝟙 (U R)))))
    ((Cohomology.affineRGammaPlusUnit R).naturality
      ((HomotopyCategory.Plus.quotient _).map f))
  change ((H R).map ((Cohomology.affineRGammaPlus R).map
    (DerivedCategory.Plus.Q.map f))).hom (Cohomology.affineRGammaPlusUnitClass R) = _
  rw [unitClass_normalization]
  simp only [Functor.map_comp, Functor.comp_map, ModuleCat.hom_comp, LinearMap.comp_apply] at h
  convert h.symm using 1 <;> rfl


-- The geometric representation needed by singleRepresentedHomologyZeroAddEquiv.
private def sectionsRepresentation :
    preadditiveCoyoneda.obj (op (U R)) ≅
      affineΓ R ⋙ forget₂ (ModuleCat R) AddCommGrpCat :=
  NatIso.ofComponents
    (fun M => (Scheme.Modules.unitHomTopLinearEquiv M).toAddEquiv.toAddCommGrpIso)
    (by
      intro M N f
      ext g
      rfl)

-- Boundary compatibility is explicit at -1 -> 0, with no zero incoming map.
-- The concrete module-valued sections comparison, including the exact forgetful
-- homology comparison. It is already an equivalence for every integer complex.
private def classToSections (K : CochainComplex (Spec R).Modules ℤ) :
    CohomologyClass (S R).obj K 0 ≃+
      (((affineΓ R).mapHomologicalComplex (.up ℤ)).obj K).homology 0 :=
  singleRepresentedModuleHomologyAddEquiv (U R) (affineΓ R)
    (sectionsRepresentation R) K 0

private def J (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules)) :
    CochainComplex.Plus (Spec R).Modules :=
  (InjectiveObject.ι _).mapCochainComplexPlus.obj L

-- Orientation: derived H⁰ --inverse derived unit--> localized degreewise
-- sections H⁰ --homologyFunctorFactors.hom--> ordinary sections-complex H⁰.
private def modelIso (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules)) :
    (H R).obj ((Cohomology.affineRGammaPlus R).obj
      (DerivedCategory.Plus.Q.obj (J R L))) ≅
    (((affineΓ R).mapHomologicalComplex (.up ℤ)).obj (J R L).obj).homology 0 := by
  haveI : IsIso ((Cohomology.affineRGammaPlusUnit R).app
      ((HomotopyCategory.Plus.quotient _).obj (J R L))) := by
    dsimp only [Cohomology.affineRGammaPlusUnit, J]
    infer_instance
  exact (asIso ((H R).map ((Cohomology.affineRGammaPlusUnit R).app
    ((HomotopyCategory.Plus.quotient _).obj (J R L))))).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app _

-- The source of the quotient includes every boundary of degree -1.
private abbrev sectionsComplex (K : CochainComplex (Spec R).Modules ℤ) :=
  ((affineΓ R).mapHomologicalComplex (.up ℤ)).obj K

-- The ordinary normalization compares the actual class map with derived
-- homology of degreewise affine sections, without an injectivity premise.
private lemma normalization (K : CochainComplex.Plus (Spec R).Modules)
    (f : S R ⟶ K) :
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app
      (((affineΓ R).mapHomologicalComplex (.up ℤ)).obj K.obj)).hom.hom
      (((H R).map ((G R).map
        ((HomotopyCategory.Plus.quotient _).map f))).hom
        ((sourceIso R).inv.hom
          ((Scheme.Modules.unitHomTopLinearEquiv (U R)) (𝟙 (U R))))) =
      classToSections R K.obj (CohomologyClass.mk (Cocycle.ofHom f.hom)) := by
  have h := ConcreteCategory.congr_hom
    (DerivedCategory.homologyFunctorFactors_hom_naturality
      (((affineΓ R).mapHomologicalComplex (.up ℤ)).map f.hom) 0)
    ((sourceIso R).inv.hom
      ((Scheme.Modules.unitHomTopLinearEquiv (U R)) (𝟙 (U R))))
  change ((DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app
      (sectionsComplex R K.obj)).hom.hom
      (((H R).map ((G R).map
        ((HomotopyCategory.Plus.quotient _).map f))).hom
        ((sourceIso R).inv.hom
          ((Scheme.Modules.unitHomTopLinearEquiv (U R)) (𝟙 (U R))))) = _ at h
  change _ = classToSections R K.obj (CohomologyClass.mk (Cocycle.ofHom f.hom))
  rw [h]
  change (HomologicalComplex.homologyMap
    (((affineΓ R).mapHomologicalComplex (.up ℤ)).map f.hom) 0).hom
    (((DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app
      (sectionsComplex R (S R).obj)).hom.hom
      (((DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app
        (sectionsComplex R (S R).obj)).inv.hom
        ((CochainComplex.HomComplex.ordinarySourceIso (U R) (affineΓ R)).inv.hom
          ((Scheme.Modules.unitHomTopLinearEquiv (U R)) (𝟙 (U R)))))) = _
  simp only [← ModuleCat.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  exact singleRepresentedModuleHomologyAddEquiv_ofHom
    (U R) (affineΓ R) (sectionsRepresentation R) K.obj f.hom

-- The exact existing affine evaluation agrees with the full quotient map on
-- every bounded-below injective model; the incoming boundary remains present.
private lemma modelIso_hom_eval_eq_classToSections
    (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules))
    (f : S R ⟶ J R L) :
    (modelIso R L).hom.hom
      (Cohomology.affineRGammaPlusEvalAddHom R
        (DerivedCategory.Plus.Q.obj (J R L)) (DerivedCategory.Plus.Q.map f)) =
      classToSections R (J R L).obj (CohomologyClass.mk (Cocycle.ofHom f.hom)) := by
  haveI : IsIso ((Cohomology.affineRGammaPlusUnit R).app
      ((HomotopyCategory.Plus.quotient _).obj (J R L))) := by
    dsimp only [Cohomology.affineRGammaPlusUnit, J]
    infer_instance
  rw [eval_on_chain_map]
  change (((asIso ((H R).map ((Cohomology.affineRGammaPlusUnit R).app
    ((HomotopyCategory.Plus.quotient _).obj (J R L))))).hom ≫
    (asIso ((H R).map ((Cohomology.affineRGammaPlusUnit R).app
      ((HomotopyCategory.Plus.quotient _).obj (J R L))))).inv) ≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app
      (sectionsComplex R (J R L).obj)).hom).hom _ = _
  rw [Iso.hom_inv_id, Category.id_comp]
  exact normalization R (J R L) f

private instance modelIsKInjective (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules)) :
    (J R L).obj.IsKInjective := by
  change CochainComplex.IsKInjective
    (((InjectiveObject.ι (Spec R).Modules).mapHomologicalComplex (.up ℤ)).obj L.obj)
  infer_instance

private def plusHomToUnbounded (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules)) :
    ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj (U R) ⟶
      DerivedCategory.Plus.Q.obj (J R L)) ≃+
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj (S R).obj) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj (J R L).obj)) :=
  Functor.mapAddEquiv DerivedCategory.Plus.ι _ _

private def modelHomClassEquiv (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules)) :
    ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj (U R) ⟶
      DerivedCategory.Plus.Q.obj (J R L)) ≃+ CohomologyClass (S R).obj (J R L).obj 0 :=
  (plusHomToUnbounded R L).trans
    (CohomologyClass.derivedCategoryHomAddEquivOfKInjective (S R).obj (J R L).obj).symm

private lemma modelHomClassEquiv_map (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules))
    (f : S R ⟶ J R L) :
    modelHomClassEquiv R L (DerivedCategory.Plus.Q.map f) =
      CohomologyClass.mk (Cocycle.ofHom f.hom) := by
  apply (CohomologyClass.derivedCategoryHomAddEquivOfKInjective
    (S R).obj (J R L).obj).injective
  simp only [modelHomClassEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  change DerivedCategory.Q.map f.hom =
    DerivedCategory.Qh.map (cohomologyClassHomotopyAddEquiv (S R).obj (J R L).obj
      (CohomologyClass.mk (Cocycle.ofHom f.hom)))
  rw [cohomologyClassHomotopyAddEquiv_mk, Cocycle.homOf_ofHom_eq_self]
  rfl


private lemma model_chain_map_surjective
    (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules)) :
    Function.Surjective (fun f : S R ⟶ J R L => DerivedCategory.Plus.Q.map f) := by
  intro g
  obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective (modelHomClassEquiv R L g)
  refine ⟨ObjectProperty.homMk z.homOf, ?_⟩
  apply (modelHomClassEquiv R L).injective
  rw [modelHomClassEquiv_map]
  simpa only [ObjectProperty.homMk_hom, Cocycle.ofHom_homOf_eq_self] using hz

private lemma model_same_map_all
    (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules))
    (g : (DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj (U R) ⟶
      DerivedCategory.Plus.Q.obj (J R L)) :
    (modelIso R L).hom.hom
      (Cohomology.affineRGammaPlusEvalAddHom R
        (DerivedCategory.Plus.Q.obj (J R L)) g) =
    classToSections R (J R L).obj (modelHomClassEquiv R L g) := by
  obtain ⟨f, rfl⟩ := model_chain_map_surjective R L g
  rw [modelHomClassEquiv_map]
  exact modelIso_hom_eval_eq_classToSections R L f

private lemma eval_bijective_on_injective_model
    (L : CochainComplex.Plus (InjectiveObject (Spec R).Modules)) :
    Function.Bijective (Cohomology.affineRGammaPlusEvalAddHom R
      (DerivedCategory.Plus.Q.obj (J R L))) := by
  have h : (fun g => (modelIso R L).hom.hom
      (Cohomology.affineRGammaPlusEvalAddHom R
        (DerivedCategory.Plus.Q.obj (J R L)) g)) =
      (fun g => classToSections R (J R L).obj (modelHomClassEquiv R L g)) :=
    funext (model_same_map_all R L)
  have hbij : Function.Bijective
      (fun g => (modelIso R L).hom.hom
        (Cohomology.affineRGammaPlusEvalAddHom R
          (DerivedCategory.Plus.Q.obj (J R L)) g)) := by
    rw [h]
    exact (classToSections R (J R L).obj).bijective.comp
      (modelHomClassEquiv R L).bijective
  exact (Function.Bijective.of_comp_iff'
    (ConcreteCategory.bijective_of_isIso (modelIso R L).hom) _).1 hbij

private lemma eval_bijective_of_isGE (M : DerivedCategory.Plus (Spec R).Modules)
    (a : ℤ) [M.IsGE a] :
    Function.Bijective (Cohomology.affineRGammaPlusEvalAddHom R M) := by
  obtain ⟨L, _, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso M a
  have hmodel := eval_bijective_on_injective_model R L
  constructor
  · intro f g h
    have h' : f ≫ e.inv = g ≫ e.inv := hmodel.injective (by
      change Cohomology.affineRGammaPlusEval R _ (f ≫ e.inv) =
        Cohomology.affineRGammaPlusEval R _ (g ≫ e.inv)
      rw [Cohomology.affineRGammaPlusEval_naturality,
        Cohomology.affineRGammaPlusEval_naturality]
      exact congrArg _ h)
    exact (cancel_mono e.inv).1 h'
  · intro y
    obtain ⟨f, hf⟩ := hmodel.surjective
      ((((Cohomology.affineRGammaPlus R) ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).map e.inv).hom y)
    refine ⟨f ≫ e.hom, ?_⟩
    change Cohomology.affineRGammaPlusEval R _ (f ≫ e.hom) = _
    rw [Cohomology.affineRGammaPlusEval_naturality]
    rw [show Cohomology.affineRGammaPlusEval R _ f = _ from hf]
    change (((Cohomology.affineRGammaPlus R) ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).map e.inv ≫
      ((Cohomology.affineRGammaPlus R) ⋙
      DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).map e.hom).hom y = y
    rw [← Functor.map_comp, e.inv_hom_id, CategoryTheory.Functor.map_id]
    rfl

private lemma eval_bijective (M : DerivedCategory.Plus (Spec R).Modules) :
    Function.Bijective (Cohomology.affineRGammaPlusEvalAddHom R M) := by
  obtain ⟨a, ha⟩ := M.property
  haveI : M.IsGE a := (M.isGE_ι_obj_iff a).1 ha
  exact eval_bijective_of_isGE R M a

end AffineRGammaPlusHomProof

namespace AlgebraicGeometry.Cohomology

/-- The canonical evaluation map identifies maps out of the structure sheaf
with degree-zero bounded-below derived affine sections. Its inverse is obtained
from injective models at an arbitrary integer lower bound; the underlying map
is exactly `AlgebraicGeometry.Cohomology.affineRGammaPlusEvalAddHom`. -/
noncomputable def affineRGammaPlusEvalAddEquiv (R : CommRingCat.{u})
    (M : DerivedCategory.Plus (Spec R).Modules) :
    (((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
      (Scheme.Modules.unit (Spec R))) ⟶ M) ≃+
    (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).obj
      ((affineRGammaPlus R).obj M) :=
  AddEquiv.ofBijective (affineRGammaPlusEvalAddHom R M)
    (AffineRGammaPlusHomProof.eval_bijective R M)

/-- Injective models establish bijectivity, while simplifying the forward map
requires no choice of resolution. -/
@[simp] theorem affineRGammaPlusEvalAddEquiv_apply (R : CommRingCat.{u})
    (M : DerivedCategory.Plus (Spec R).Modules)
    (f : ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
      (Scheme.Modules.unit (Spec R))) ⟶ M) :
    affineRGammaPlusEvalAddEquiv R M f = affineRGammaPlusEval R M f := rfl

/-- This identity reuses additive evaluation lemmas without unfolding the
chosen inverse. -/
theorem affineRGammaPlusEvalAddEquiv_toAddMonoidHom (R : CommRingCat.{u})
    (M : DerivedCategory.Plus (Spec R).Modules) :
    (affineRGammaPlusEvalAddEquiv R M).toAddMonoidHom =
      affineRGammaPlusEvalAddHom R M := rfl

private noncomputable def affinePlusHomToUnboundedAddEquiv (R : CommRingCat.{u})
    (M : DerivedCategory.Plus (Spec R).Modules) :
    (((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
      (Scheme.Modules.unit (Spec R))) ⟶ M) ≃+
    (((DerivedCategory.singleFunctor (Spec R).Modules 0).obj
      (Scheme.Modules.unit (Spec R))) ⟶
      (DerivedCategory.Plus.ι.obj M)) :=
  Functor.mapAddEquiv DerivedCategory.Plus.ι _ _

/-- For a bounded-below Dqc object on an affine scheme, degree-zero derived
affine sections identify pointwise with top sections of its degree-zero
cohomology sheaf. The comparison uses the inverse of the canonical evaluation
equivalence and the existing Hom-to-sections comparison; no naturality is
asserted here. An integer lower bound is supplied by `M.property`. -/
noncomputable def affineRGammaPlusDqcHomologyZeroSectionsAddEquiv
    (R : CommRingCat.{u}) (M : DerivedCategory.Plus (Spec R).Modules)
    (hM : DerivedCategory.Dqc.schemeQuasicoherentCohomology (Spec R)
      (DerivedCategory.Plus.ι.obj M)) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat R) 0).obj
      ((affineRGammaPlus R).obj M) ≃+
    Γ((DerivedCategory.Plus.homologyFunctor (Spec R).Modules 0).obj M,
      (⊤ : (Spec R).Opens)) := by
  let a : ℤ := M.property.choose
  haveI : M.IsGE a := (M.isGE_ι_obj_iff a).1 M.property.choose_spec
  exact
  (affineRGammaPlusEvalAddEquiv R M).symm.trans
    ((affinePlusHomToUnboundedAddEquiv R M).trans
      (affineHomH0SectionsAddEquiv hM a))

/-- This computation avoids unfolding the inverse: the evaluation equivalence
cancels before applying the existing Hom-to-sections comparison. -/
theorem affineRGammaPlusDqcHomologyZeroSectionsAddEquiv_apply_eval
    (R : CommRingCat.{u}) (M : DerivedCategory.Plus (Spec R).Modules)
    (hM : DerivedCategory.Dqc.schemeQuasicoherentCohomology (Spec R)
      (DerivedCategory.Plus.ι.obj M))
    (a : ℤ) [M.IsGE a]
    (f : ((DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).obj
      (Scheme.Modules.unit (Spec R))) ⟶ M) :
    affineRGammaPlusDqcHomologyZeroSectionsAddEquiv R M hM
      (affineRGammaPlusEval R M f) =
    affineHomH0SectionsAddEquiv hM a (DerivedCategory.Plus.ι.map f) := by
  change (affineHomH0SectionsAddEquiv hM a)
    (DerivedCategory.Plus.ι.mapAddHom
      ((affineRGammaPlusEvalAddEquiv R M).symm
        ((affineRGammaPlusEvalAddEquiv R M) f))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

end AlgebraicGeometry.Cohomology
