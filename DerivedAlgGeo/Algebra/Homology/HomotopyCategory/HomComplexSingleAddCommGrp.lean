/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Represented Hom-complex classes in additive groups

For arbitrary integer-indexed cochain complexes, a represented zero-preserving
additive-group-valued functor sends Hom-complex classes out of a degree-zero
single to the full homology of its degreewise image. The chain-map formula
uses the represented identity, and incoming boundaries are included.

## Main definitions

* `CochainComplex.HomComplex.representedAddCommGrpEquiv_ofPZM`
  gives the all-degree additive equivalence.
* `CochainComplex.HomComplex.ordinaryAddCommGrpSourceIso`
  identifies homology of the degreewise image of the single.

## Main results

* `CochainComplex.HomComplex.representedAddCommGrpNormalization_ofPZM`
  computes a chain-map class.
* `CochainComplex.HomComplex.singleRepresentedAddCommGrp_boundary_killed`
  records the incoming-boundary quotient.

## Implementation notes

The proof transports cycles through the existing represented Hom-complex iso,
then applies the canonical homology quotient. The source cycle represents the
identity and is computed using the mapped-single comparison.

## References

Mathlib's `HomComplexSingle.lean`, `Homology/Additive.lean`, and
`SingleHomology.lean` at pin `520045ab14e26149ee970e2e617ca04b09bde5d6`.

## Tags

Hom-complex, represented functor, additive group, homology
-/

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex
set_option backward.isDefEq.respectTransparency false
universe u v
noncomputable section
namespace CochainComplex.HomComplex
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable (X : C) (F : C ⥤ AddCommGrpCat.{v}) [F.PreservesZeroMorphisms]
variable (e : preadditiveCoyoneda.obj (op X) ≅ F)
private abbrev S := (CochainComplex.singleFunctor C 0).obj X

/-- Hom-complex classes out of a single are the homology of the represented
additive-group-valued functor in every integer degree. -/
private def representedAddCommGrpEquiv_ofPZM (K : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass (S X) K n ≃+
      ((F.mapHomologicalComplex (.up ℤ)).obj K).homology n :=
  singleRepresentedHomologyAddEquiv X F e K n

/-- The complex obtained by applying the represented additive-group functor
degreewise. -/
abbrev addCommGrpSectionsComplex (K : CochainComplex C ℤ) :=
  (F.mapHomologicalComplex (.up ℤ)).obj K

private def representedCycle (K : CochainComplex C ℤ)
    (x : Cocycle (S X) K 0) : (addCommGrpSectionsComplex F K).cycles 0 :=
  HomologicalComplex.cyclesMap
    (singleRepresentedIso X F e K).hom 0
    ((leftHomologyData (S X) K 0).cyclesIso.inv x)

private lemma representedAddCommGrpEquiv_ofPZM_mk (K : CochainComplex C ℤ)
    (x : Cocycle (S X) K 0) :
    representedAddCommGrpEquiv_ofPZM X F e K 0 (CohomologyClass.mk x) =
      ((addCommGrpSectionsComplex F K).homologyπ 0).hom
        (representedCycle X F e K x) := by
  have hx := ConcreteCategory.congr_hom
    ((leftHomologyData (S X) K 0).π_comp_homologyIso_inv) x
  change (homologyAddEquiv (S X) K 0).symm (CohomologyClass.mk x) =
    (CochainComplex.HomComplex (S X) K).homologyπ 0
      ((leftHomologyData (S X) K 0).cyclesIso.inv x) at hx
  unfold representedAddCommGrpEquiv_ofPZM singleRepresentedHomologyAddEquiv
  simp only [AddEquiv.trans_apply]
  rw [hx]
  change ((leftHomologyData (S X) K 0).cyclesIso.inv ≫
    (CochainComplex.HomComplex (S X) K).homologyπ 0 ≫
    HomologicalComplex.homologyMap
      (singleRepresentedIso X F e K).hom 0) x = _
  rw [HomologicalComplex.homologyπ_naturality]
  rfl

private lemma representedCycle_i (K : CochainComplex C ℤ)
    (x : Cocycle (S X) K 0) :
    ((addCommGrpSectionsComplex F K).iCycles 0).hom (representedCycle X F e K x) =
      (singleRepresentedIso X _ e K).hom.f 0
        (x : Cochain (S X) K 0) := by
  change ((leftHomologyData (S X) K 0).cyclesIso.inv ≫
    HomologicalComplex.cyclesMap
      (singleRepresentedIso X F e K).hom 0 ≫
    ((F.mapHomologicalComplex (.up ℤ)).obj K).iCycles 0) x = _
  rw [HomologicalComplex.cyclesMap_i]
  change (((leftHomologyData (S X) K 0).cyclesIso.inv ≫
    ((CochainComplex.HomComplex (S X) K).sc 0).iCycles) ≫
    (singleRepresentedIso X _ e K).hom.f 0) x = _
  erw [ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles]
  rfl


/-- Homology of the represented image of the degree-zero single is its value
on the source object. -/
def ordinaryAddCommGrpSourceIso : (addCommGrpSectionsComplex F (S X)).homology 0 ≅
    F.obj X :=
  HomologicalComplex.homologyMapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X) 0 ≪≫
    (HomologicalComplex.homologyFunctorSingleIso (AddCommGrpCat) (.up ℤ) 0).app _

/-- The cycle corresponding to the represented identity on the source. -/
def addCommGrpSourceCycle : (addCommGrpSectionsComplex F (S X)).cycles 0 :=
  (HomologicalComplex.cyclesMap
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X).inv 0).hom
      ((HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0
        (F.obj X)).inv.hom
        ((e.hom.app X) (𝟙 X)))

/-- The source identity cycle maps to the inverse image of the represented
identity under the canonical source homology iso. -/
lemma addCommGrpSourceCycle_π :
    ((addCommGrpSectionsComplex F (S X)).homologyπ 0).hom (addCommGrpSourceCycle X F e) =
      (ordinaryAddCommGrpSourceIso X F).inv.hom
        ((e.hom.app X) (𝟙 X)) := by
  change ((HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0
      (F.obj X)).inv ≫
    HomologicalComplex.cyclesMap
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X).inv 0 ≫
    (addCommGrpSectionsComplex F (S X)).homologyπ 0).hom _ = _
  erw [← HomologicalComplex.homologyπ_naturality,
    HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ_assoc]
  rfl

/-- The source identity cycle agrees with its degree-zero component. -/
lemma addCommGrpSourceCycle_i :
    ((addCommGrpSectionsComplex F (S X)).iCycles 0).hom (addCommGrpSourceCycle X F e) =
      (F.map
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv).hom
          ((e.hom.app X) (𝟙 X)) := by
  change ((HomologicalComplex.singleObjCyclesSelfIso (.up ℤ) 0
      (F.obj X)).inv ≫
    HomologicalComplex.cyclesMap
      ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app X).inv 0 ≫
    (addCommGrpSectionsComplex F (S X)).iCycles 0).hom _ = _
  erw [HomologicalComplex.cyclesMap_i,
    HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc]
  change ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (F.obj X)).inv ≫
    ((HomologicalComplex.singleMapHomologicalComplex
      F (.up ℤ) 0).inv.app X).f 0).hom _ = _
  rw [HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    CategoryTheory.Iso.inv_hom_id_assoc]
  rfl

private lemma representedCycle_ofHom (K : CochainComplex C ℤ)
    (f : S X ⟶ K) :
    representedCycle X F e K (Cocycle.ofHom f) =
      (HomologicalComplex.cyclesMap
        ((F.mapHomologicalComplex (.up ℤ)).map f) 0).hom
          (addCommGrpSourceCycle X F e) := by
  apply (AddCommGrpCat.mono_iff_injective ((addCommGrpSectionsComplex F K).iCycles 0)).1
    inferInstance
  rw [representedCycle_i]
  change _ = ((HomologicalComplex.cyclesMap
    ((F.mapHomologicalComplex (.up ℤ)).map f) 0) ≫
    (addCommGrpSectionsComplex F K).iCycles 0).hom _
  rw [HomologicalComplex.cyclesMap_i]
  change _ = (F.map (f.f 0)).hom
    (((addCommGrpSectionsComplex F (S X)).iCycles 0).hom (addCommGrpSourceCycle X F e))
  rw [addCommGrpSourceCycle_i]
  change (e.hom.app (K.X 0))
    (Cochain.fromSingleEquiv (zero_add 0) (Cochain.ofHom f)) = _
  have h := ConcreteCategory.congr_hom (e.hom.naturality
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫ f.f 0)) (𝟙 X)
  change (e.hom.app (K.X 0))
      ((𝟙 X) ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫ f.f 0) =
    (F.map ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫ f.f 0)).hom
      ((e.hom.app X) (𝟙 X)) at h
  rw [Category.id_comp, Functor.map_comp] at h
  change (e.hom.app (K.X 0))
    ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).inv ≫
      (Cochain.ofHom f).v 0 0 (add_zero 0)) = _
  rw [Cochain.ofHom_v]
  exact h


/-- A chain map out of the degree-zero single evaluates the represented
identity to its full Hom-complex homology class. -/
private theorem representedAddCommGrpNormalization_ofPZM (K : CochainComplex C ℤ)
    (f : S X ⟶ K) :
    (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map f) 0).hom
        ((ordinaryAddCommGrpSourceIso X F).inv.hom
          ((e.hom.app X) (𝟙 X))) =
      representedAddCommGrpEquiv_ofPZM X F e K 0
        (CohomologyClass.mk (Cocycle.ofHom f)) := by
  rw [representedAddCommGrpEquiv_ofPZM_mk,
    representedCycle_ofHom, ← addCommGrpSourceCycle_π]
  change ((addCommGrpSectionsComplex F (S X)).homologyπ 0 ≫
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℤ)).map f) 0).hom _ = _
  rw [HomologicalComplex.homologyπ_naturality]
  rfl


omit [F.PreservesZeroMorphisms] in
/-- The represented additive-group homology equivalence, with zero preservation
constructed from the representation rather than supplied by the caller. -/
def singleRepresentedAddCommGrpHomologyAddEquiv (K : CochainComplex C ℤ) (n : ℤ) :
    letI := Functor.preservesZeroMorphisms_of_iso e
    CohomologyClass (S X) K n ≃+
      ((F.mapHomologicalComplex (.up ℤ)).obj K).homology n := by
  letI := Functor.preservesZeroMorphisms_of_iso e
  exact representedAddCommGrpEquiv_ofPZM X F e K n

omit [F.PreservesZeroMorphisms] in
/-- Normalization of a represented chain-map class with zero preservation
constructed from the representation. -/
theorem singleRepresentedAddCommGrpHomologyAddEquiv_ofHom (K : CochainComplex C ℤ)
    (f : S X ⟶ K) :
    letI := Functor.preservesZeroMorphisms_of_iso e
    (HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map f) 0).hom
      ((ordinaryAddCommGrpSourceIso X F).inv.hom ((e.hom.app X) (𝟙 X))) =
        singleRepresentedAddCommGrpHomologyAddEquiv X F e K 0
          (CohomologyClass.mk (Cocycle.ofHom f)) := by
  letI := Functor.preservesZeroMorphisms_of_iso e
  exact representedAddCommGrpNormalization_ofPZM X F e K f

/-- A degree-`n - 1` cochain maps to the incoming differential under the
represented Hom-complex comparison. -/
theorem singleRepresentedAddCommGrp_incoming_boundary (K : CochainComplex C ℤ) (n : ℤ)
    (b : X ⟶ K.X (n - 1)) :
    (singleRepresentedIso X _ e K).hom.f n
        (δ (n - 1) n (Cochain.fromSingleMk b (zero_add (n - 1)))) =
      ((F).map (K.d (n - 1) n))
        ((e.hom.app (K.X (n - 1))) b) := by
  rw [Cochain.δ_fromSingleMk b (zero_add (n - 1)) n n (zero_add n)]
  change (e.hom.app (K.X n))
    (Cochain.fromSingleEquiv (zero_add n)
      (Cochain.fromSingleMk (b ≫ K.d (n - 1) n) (zero_add n))) = _
  rw [Cochain.fromSingleEquiv_fromSingleMk]
  exact ConcreteCategory.congr_hom (e.hom.naturality (K.d (n - 1) n)) b

/-- The canonical incoming boundary, regarded as a degree-`n` cocycle. -/
def singleRepresentedAddCommGrpBoundaryCycle (K : CochainComplex C ℤ) (n : ℤ)
    (b : X ⟶ K.X (n - 1)) : Cocycle (S X) K n :=
  Cocycle.mk (δ (n - 1) n (Cochain.fromSingleMk b (zero_add (n - 1)))) (n + 1) rfl
    (δ_δ _ _ _ _)

omit [F.PreservesZeroMorphisms] in
/-- The full homology quotient kills every incoming degree-`n - 1` boundary. -/
theorem singleRepresentedAddCommGrp_boundary_killed (K : CochainComplex C ℤ) (n : ℤ)
    (b : X ⟶ K.X (n - 1)) :
    singleRepresentedAddCommGrpHomologyAddEquiv X F e K n
      (CohomologyClass.mk (singleRepresentedAddCommGrpBoundaryCycle X K n b)) = 0 := by
  have hz : CohomologyClass.mk (singleRepresentedAddCommGrpBoundaryCycle X K n b) = 0 := by
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨n - 1, by omega, Cochain.fromSingleMk b (zero_add (n - 1)), rfl⟩
  rw [hz, map_zero]

end CochainComplex.HomComplex
