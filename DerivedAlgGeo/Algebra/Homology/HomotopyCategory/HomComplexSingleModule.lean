/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexSingleAddCommGrp
import DerivedAlgGeo.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Module-valued normalization of represented Hom-complex classes

The additive-group theorem specializes to a represented module-valued
functor. The forgetful homology comparison transports the represented source
identity to homology in the module category, retaining the incoming-boundary
quotient from the neutral theorem.

## Main definitions

* `CochainComplex.HomComplex.singleRepresentedModuleHomologyAddEquiv`
  is the all-degree module-valued comparison.
* `CochainComplex.HomComplex.ordinarySourceIso` identifies the mapped single.

## Main results

* `CochainComplex.HomComplex.singleRepresentedModuleHomologyAddEquiv_ofHom`
  computes the class of a chain map under the module-valued comparison.

## Implementation notes

The AddCommGrp comparison computes the ordinary class. The forgetful homology
iso and its cycle comparison carry the represented identity into ModuleCat.

## References

Mathlib's `ShortComplex/ModuleCat.lean` and `SingleHomology.lean` at pin
`520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

Hom-complex, module category, represented functor, homology
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex
set_option backward.isDefEq.respectTransparency false
universe u v
noncomputable section
namespace CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {R : Type v} [Ring R]
variable (X : C) (F : C ⥤ ModuleCat.{v} R) [F.PreservesZeroMorphisms]
variable (e : preadditiveCoyoneda.obj (op X) ≅ F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)
omit [F.PreservesZeroMorphisms] [HasZeroObject C] in
include X e in
private theorem representedModulePreservesZero : F.PreservesZeroMorphisms := by
  letI : (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat).Additive :=
    Functor.additive_of_iso e
  letI := Functor.additive_of_comp_faithful F
    (forget₂ (ModuleCat R) AddCommGrpCat)
  infer_instance

private abbrev S := (CochainComplex.singleFunctor C 0).obj X

/-- The represented additive equivalence for a module-valued functor, in every
integer degree. -/
private def representedModuleEquiv_ofPZM (K : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass (S X) K n ≃+
      ((F.mapHomologicalComplex (.up ℤ)).obj K).homology n :=
  (singleRepresentedHomologyAddEquiv X _ e K n).trans
    ((((F.mapHomologicalComplex (.up ℤ)).obj K).sc n).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).addCommGroupIsoToAddEquiv

private abbrev sectionsComplex (K : CochainComplex C ℤ) :=
  (F.mapHomologicalComplex (.up ℤ)).obj K

/-- The source homology iso in the module category. -/
def ordinarySourceIso : (sectionsComplex F (S X)).homology 0 ≅
    F.obj X :=
  HomologicalComplex.homologyMapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X) 0 ≪≫
    (HomologicalComplex.homologyFunctorSingleIso (ModuleCat R) (.up ℤ) 0).app _

private def ordinarySourceCycle : (sectionsComplex F (S X)).cycles 0 :=
  (HomologicalComplex.cyclesMap
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X).inv 0).hom
      ((HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0
        (F.obj X)).inv.hom
        ((e.hom.app X) (𝟙 X)))

private lemma ordinarySourceCycle_π :
    ((sectionsComplex F (S X)).homologyπ 0).hom (ordinarySourceCycle X F e) =
      (ordinarySourceIso X F).inv.hom
        ((e.hom.app X) (𝟙 X)) := by
  change ((HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0
      (F.obj X)).inv ≫
    HomologicalComplex.cyclesMap
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X).inv 0 ≫
    (sectionsComplex F (S X)).homologyπ 0).hom _ = _
  erw [← HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ_assoc]
  rfl

private lemma ordinarySourceCycle_i :
    ((sectionsComplex F (S X)).iCycles 0).hom (ordinarySourceCycle X F e) =
      (F.map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv).hom
          ((e.hom.app X) (𝟙 X)) := by
  change ((HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0
      (F.obj X)).inv ≫
    HomologicalComplex.cyclesMap
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X).inv 0 ≫
    (sectionsComplex F (S X)).iCycles 0).hom _ = _
  erw [HomologicalComplex.cyclesMap_i,
    HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc]
  change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (F.obj X)).inv ≫
    ((HomologicalComplex.singleMapHomologicalComplex
      F (.up ℤ) 0).inv.app X).f 0).hom _ = _
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    CategoryTheory.Iso.inv_hom_id_assoc]
  rfl

private lemma source_cycle_comparison :
    (((sectionsComplex F (S X)).sc 0).mapCyclesIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).hom
        (CochainComplex.HomComplex.addCommGrpSourceCycle X
          (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) e) =
      ordinarySourceCycle X F e := by
  apply (ModuleCat.mono_iff_injective ((sectionsComplex F (S X)).iCycles 0)).1
    inferInstance
  change ((((sectionsComplex F (S X)).sc 0).mapCyclesIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).hom ≫
    (forget₂ (ModuleCat R) AddCommGrpCat).map
      ((sectionsComplex F (S X)).iCycles 0)) _ = _
  erw [ShortComplex.mapCyclesIso_hom_iCycles]
  change ((CochainComplex.HomComplex.addCommGrpSectionsComplex
    (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) (S X)).iCycles 0).hom
      (CochainComplex.HomComplex.addCommGrpSourceCycle X
        (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) e) = _
  rw [CochainComplex.HomComplex.addCommGrpSourceCycle_i, ordinarySourceCycle_i]
  rfl

private lemma source_unit_comparison :
    (((sectionsComplex F (S X)).sc 0).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).hom
        ((CochainComplex.HomComplex.ordinaryAddCommGrpSourceIso X
          (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)).inv.hom
            ((e.hom.app X) (𝟙 X))) =
      (ordinarySourceIso X F).inv.hom ((e.hom.app X) (𝟙 X)) := by
  rw [← CochainComplex.HomComplex.addCommGrpSourceCycle_π,
    ← ordinarySourceCycle_π]
  change ((((sectionsComplex F (S X)).sc 0).map
      (forget₂ (ModuleCat R) AddCommGrpCat)).homologyπ ≫
    (((sectionsComplex F (S X)).sc 0).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).hom) _ = _
  rw [CategoryTheory.ShortComplex.homologyπ_mapHomologyIso_hom]
  change ((sectionsComplex F (S X)).homologyπ 0).hom
    ((((sectionsComplex F (S X)).sc 0).mapCyclesIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).hom
        (CochainComplex.HomComplex.addCommGrpSourceCycle X
          (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) e)) = _
  rw [source_cycle_comparison]

/-- Module-valued normalization of a chain-map class, derived from the
additive-group-valued theorem and its source-unit comparison. -/
private theorem representedModuleNormalization_ofPZM (K : CochainComplex C ℤ)
    (f : S X ⟶ K) :
    (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map f) 0).hom
        ((ordinarySourceIso X F).inv.hom
          ((e.hom.app X) (𝟙 X))) =
      representedModuleEquiv_ofPZM X F e K 0 (CohomologyClass.mk (Cocycle.ofHom f)) := by
  have h := congrArg
    ((((sectionsComplex F K).sc 0).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).hom)
    (CochainComplex.HomComplex.singleRepresentedAddCommGrpHomologyAddEquiv_ofHom X
      (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) e K f)
  change (ShortComplex.homologyMap
    ((forget₂ (ModuleCat R) AddCommGrpCat).mapShortComplex.map
      ((HomologicalComplex.shortComplexFunctor (ModuleCat R) (.up ℤ) 0).map
        ((F.mapHomologicalComplex (.up ℤ)).map f))) ≫
    (((sectionsComplex F K).sc 0).mapHomologyIso
      (forget₂ (ModuleCat R) AddCommGrpCat)).hom) _ = _ at h
  rw [ShortComplex.mapHomologyIso_hom_naturality] at h
  change (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map f) 0).hom
      ((((sectionsComplex F (S X)).sc 0).mapHomologyIso
        (forget₂ (ModuleCat R) AddCommGrpCat)).hom
        ((CochainComplex.HomComplex.ordinaryAddCommGrpSourceIso X
          (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)).inv.hom
            ((e.hom.app X) (𝟙 X)))) = _ at h
  rw [source_unit_comparison] at h
  exact h


omit [F.PreservesZeroMorphisms] in
/-- The represented module-valued homology equivalence with zero preservation
constructed from its representation. -/
def singleRepresentedModuleHomologyAddEquiv (K : CochainComplex C ℤ) (n : ℤ) :
    letI := representedModulePreservesZero X F e
    CohomologyClass (S X) K n ≃+
      ((F.mapHomologicalComplex (.up ℤ)).obj K).homology n := by
  letI := representedModulePreservesZero X F e
  exact representedModuleEquiv_ofPZM X F e K n

omit [F.PreservesZeroMorphisms] in
/-- Module-valued chain-map normalization, derived from its representation and
the additive-group-valued ordinary theorem. -/
theorem singleRepresentedModuleHomologyAddEquiv_ofHom (K : CochainComplex C ℤ)
    (f : S X ⟶ K) :
    letI := representedModulePreservesZero X F e
    (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) 0).hom
      ((ordinarySourceIso X F).inv.hom ((e.hom.app X) (𝟙 X))) =
        singleRepresentedModuleHomologyAddEquiv X F e K 0
          (CohomologyClass.mk (Cocycle.ofHom f)) := by
  letI := representedModulePreservesZero X F e
  exact representedModuleNormalization_ofPZM X F e K f

end CochainComplex.HomComplex
