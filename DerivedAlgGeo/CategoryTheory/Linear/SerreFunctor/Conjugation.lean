/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Linear.SerreFunctor.Uniqueness
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Conjugation of a Serre functor by a linear equivalence

This module keeps equivalence transport in the linear Serre core. It does not
require a shift or a triangulated structure.

## Main definitions

`SerreFunctorData.conj D Φ` is Serre duality on `Φ.inverse ⋙ D.S ⋙ Φ.functor`:
the inverse moves both Hom arguments into the category where `D.eta` applies.
`SerreFunctorData.transportIso D Φ` then uses uniqueness of Serre duality to
identify `Φ.functor ⋙ D.S` with `D.S ⋙ Φ.functor`.

## Main results

`SerreFunctorData.transportIso_refl` identifies its specialization to the
identity equivalence with the canonical functor unitors.
`SerreFunctorData.conj_eta_trans` and
`SerreFunctorData.conj_trans_uniqueIso_hom_app_eq_id` give the duality and canonical
comparison laws for a composite linear equivalence.
-/

universe w v u

namespace CategoryTheory.SerreFunctor

open CategoryTheory

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C]

namespace SerreFunctorData

/-- A linear equivalence induces a linear equivalence on each Hom space. -/
private noncomputable def homEquivOfFullyFaithful (F : C ⥤ C)
    [F.Additive] [F.Linear k] (hF : F.FullyFaithful) (A B : C) :
    (A ⟶ B) ≃ₗ[k] (F.obj A ⟶ F.obj B) where
  toFun := F.map
  map_add' := by intro _ _; exact F.map_add
  map_smul' := by intro r f; exact F.map_smul r f
  invFun := hF.preimage
  left_inv := hF.preimage_map
  right_inv := hF.map_preimage

/-- The Hom-space equivalence induced by a linear autoequivalence and its counit. -/
private noncomputable def homEquivCounit (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k] (B X : C) :
    (Φ.inverse.obj B ⟶ X) ≃ₗ[k] (B ⟶ Φ.functor.obj X) :=
  (homEquivOfFullyFaithful Φ.functor Φ.fullyFaithfulFunctor _ _).trans
    (Linear.homCongr k (Φ.counitIso.app B) (Iso.refl _))

/-- The Serre duality equivalence transported by a linear autoequivalence. -/
private noncomputable def etaConj (D : SerreFunctorData k C) (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k] (A B : C) :
    Module.Dual k (A ⟶ B) ≃ₗ[k]
      (B ⟶ (Φ.inverse ⋙ D.S ⋙ Φ.functor).obj A) := by
  letI : Φ.inverse.Additive := inferInstance
  letI : Φ.inverse.Linear k := CategoryTheory.Equivalence.inverseLinear k Φ
  let e := homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse A B
  exact (e.symm.dualMap).trans
    ((D.eta (Φ.inverse.obj A) (Φ.inverse.obj B)).trans
      (homEquivCounit Φ B (D.S.obj (Φ.inverse.obj A))))

private theorem dualConj_naturality_left (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k] {A A' B : C}
    (f : A ⟶ A') (phi : Module.Dual k (A ⟶ B)) :
    (homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse A' B).symm.dualMap
        (phi.comp (Linear.leftComp k B f)) =
      ((homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse A B).symm.dualMap
        phi).comp (Linear.leftComp k (Φ.inverse.obj B) (Φ.inverse.map f)) := by
  letI : Φ.inverse.Additive := inferInstance
  letI : Φ.inverse.Linear k := CategoryTheory.Equivalence.inverseLinear k Φ
  ext h
  simp [homEquivOfFullyFaithful, LinearEquiv.dualMap_apply,
    Linear.leftComp, Φ.fullyFaithfulInverse.preimage_comp]

private theorem dualConj_naturality_right (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k] {A B B' : C}
    (g : B' ⟶ B) (phi : Module.Dual k (A ⟶ B)) :
    (homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse A B').symm.dualMap
        (phi.comp (Linear.rightComp k A g)) =
      ((homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse A B).symm.dualMap
        phi).comp (Linear.rightComp k (Φ.inverse.obj A) (Φ.inverse.map g)) := by
  letI : Φ.inverse.Additive := inferInstance
  letI : Φ.inverse.Linear k := CategoryTheory.Equivalence.inverseLinear k Φ
  ext h
  simp [homEquivOfFullyFaithful, LinearEquiv.dualMap_apply,
    Linear.rightComp, Φ.fullyFaithfulInverse.preimage_comp]

private theorem homEquivCounit_naturality_left (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k] (B : C) {X Y : C}
    (h : Φ.inverse.obj B ⟶ X) (q : X ⟶ Y) :
    homEquivCounit (k := k) Φ B Y (h ≫ q) =
      homEquivCounit (k := k) Φ B X h ≫ Φ.functor.map q := by
  simp [homEquivCounit, homEquivOfFullyFaithful, Linear.homCongr_apply, Category.assoc]

private theorem homEquivCounit_naturality_right (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k] {B B' X : C}
    (g : B' ⟶ B) (h : Φ.inverse.obj B ⟶ X) :
    homEquivCounit (k := k) Φ B' X (Φ.inverse.map g ≫ h) =
      g ≫ homEquivCounit (k := k) Φ B X h := by
  simp only [homEquivCounit, LinearEquiv.trans_apply, Linear.homCongr_apply,
    homEquivOfFullyFaithful, Iso.refl_hom, Category.comp_id]
  change (Φ.counitIso.app B').inv ≫ Φ.functor.map (Φ.inverse.map g ≫ h) =
    g ≫ (Φ.counitIso.app B).inv ≫ Φ.functor.map h
  have hnat : (Φ.counitIso.app B').inv ≫ Φ.functor.map (Φ.inverse.map g) =
      g ≫ (Φ.counitIso.app B).inv := by
    have hn := (Φ.counitIso.inv.naturality g).symm
    change (Φ.counitIso.app B').inv ≫ Φ.functor.map (Φ.inverse.map g) =
      g ≫ (Φ.counitIso.app B).inv at hn
    exact hn
  calc
    (Φ.counitIso.app B').inv ≫ Φ.functor.map (Φ.inverse.map g ≫ h) =
        ((Φ.counitIso.app B').inv ≫ Φ.functor.map (Φ.inverse.map g)) ≫
          Φ.functor.map h := by simp only [Functor.map_comp, Category.assoc]; rfl
    _ = (g ≫ (Φ.counitIso.app B).inv) ≫ Φ.functor.map h := by rw [hnat]; rfl
    _ = g ≫ (Φ.counitIso.app B).inv ≫ Φ.functor.map h := Category.assoc _ _ _

/-- Conjugation by a linear autoequivalence preserves Serre duality. -/
noncomputable def conj (D : SerreFunctorData k C) (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k] : SerreFunctorData k C := by
  letI : Φ.inverse.Additive := inferInstance
  letI : Φ.inverse.Linear k := CategoryTheory.Equivalence.inverseLinear k Φ
  refine {
    S := Φ.inverse ⋙ D.S ⋙ Φ.functor
    eta := etaConj D Φ
    naturality_left := ?_
    naturality_right := ?_ }
  · intro A A' B f phi
    dsimp [etaConj]
    rw [dualConj_naturality_left Φ f phi, D.naturality_left]
    change homEquivCounit (k := k) Φ B (D.S.obj (Φ.inverse.obj A'))
        ((D.eta (Φ.inverse.obj A) (Φ.inverse.obj B)
          ((homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse A B).symm.dualMap
            phi)) ≫ D.S.map (Φ.inverse.map f)) =
      homEquivCounit (k := k) Φ B (D.S.obj (Φ.inverse.obj A))
          (D.eta (Φ.inverse.obj A) (Φ.inverse.obj B)
            ((homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse A B).symm.dualMap
              phi)) ≫ Φ.functor.map (D.S.map (Φ.inverse.map f))
    simpa only [Functor.comp_map, Functor.comp_obj] using
      (homEquivCounit_naturality_left (k := k) Φ B
        (D.eta (Φ.inverse.obj A) (Φ.inverse.obj B)
          ((homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse A B).symm.dualMap
            phi)) (D.S.map (Φ.inverse.map f)))
  · intro A B B' g phi
    dsimp [etaConj]
    rw [dualConj_naturality_right Φ g phi, D.naturality_right]
    exact homEquivCounit_naturality_right (k := k) Φ g _

/-- A linear autoequivalence commutes with the chosen Serre functor up to a
canonical natural isomorphism, by uniqueness of Serre duality. -/
noncomputable def transportIso (D : SerreFunctorData k C) (Φ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k] :
    Φ.functor ⋙ D.S ≅ D.S ⋙ Φ.functor :=
  Functor.isoWhiskerLeft Φ.functor (D.uniqueIso (D.conj Φ)) ≪≫
    Functor.isoWhiskerLeft Φ.functor (Functor.associator Φ.inverse D.S Φ.functor) ≪≫
    (Functor.associator Φ.functor Φ.inverse (D.S ⋙ Φ.functor)).symm ≪≫
    Φ.funInvIdAssoc (D.S ⋙ Φ.functor)

private local instance transFunctorAdditive (Φ Ψ : C ≌ C)
    [Φ.functor.Additive] [Ψ.functor.Additive] :
    (Φ.trans Ψ).functor.Additive := by
  change (Φ.functor ⋙ Ψ.functor).Additive
  infer_instance

private local instance transFunctorLinear (Φ Ψ : C ≌ C)
    [Φ.functor.Linear k] [Ψ.functor.Linear k] :
    (Φ.trans Ψ).functor.Linear k := by
  change (Φ.functor ⋙ Ψ.functor).Linear k
  infer_instance

omit [Preadditive C] in
private theorem preimage_inverse_trans (Φ Ψ : C ≌ C)
    (A B : C) (h : (Φ.trans Ψ).inverse.obj A ⟶ (Φ.trans Ψ).inverse.obj B) :
    (Φ.trans Ψ).fullyFaithfulInverse.preimage h =
      Ψ.fullyFaithfulInverse.preimage (Φ.fullyFaithfulInverse.preimage h) := by
  apply (Φ.trans Ψ).fullyFaithfulInverse.map_injective
  rw [(Φ.trans Ψ).fullyFaithfulInverse.map_preimage]
  change h = Φ.inverse.map (Ψ.inverse.map
    (Ψ.fullyFaithfulInverse.preimage (Φ.fullyFaithfulInverse.preimage h)))
  rw [Ψ.fullyFaithfulInverse.map_preimage, Φ.fullyFaithfulInverse.map_preimage]

omit [Preadditive C] in
private theorem counit_inv_trans (Φ Ψ : C ≌ C) (B : C) :
    (Φ.trans Ψ).counitIso.inv.app B =
      Ψ.counitIso.inv.app B ≫ Ψ.functor.map (Φ.counitIso.inv.app (Ψ.inverse.obj B)) := by
  simp [Equivalence.trans, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.rightUnitor_inv_app, Category.assoc]
  erw [Ψ.functor.map_id, Category.id_comp]
  erw [Ψ.functor.map_id, Category.comp_id]
  erw [Category.comp_id]
  rfl

private theorem homEquivCounit_trans (Φ Ψ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k]
    [Ψ.functor.Additive] [Ψ.functor.Linear k]
    (B X : C) (h : (Φ.trans Ψ).inverse.obj B ⟶ X) :
    homEquivCounit (k := k) (Φ.trans Ψ) B X h =
      homEquivCounit (k := k) Ψ B (Φ.functor.obj X)
        (homEquivCounit (k := k) Φ (Ψ.inverse.obj B) X h) := by
  simp only [homEquivCounit, LinearEquiv.trans_apply, Linear.homCongr_apply,
    homEquivOfFullyFaithful, Iso.refl_hom, Category.comp_id]
  change (Φ.trans Ψ).counitIso.inv.app B ≫ Ψ.functor.map (Φ.functor.map h) =
    Ψ.counitIso.inv.app B ≫ Ψ.functor.map
      (Φ.counitIso.inv.app (Ψ.inverse.obj B) ≫ Φ.functor.map h)
  rw [counit_inv_trans Φ Ψ B]
  simp only [Functor.map_comp]
  erw [Category.assoc]
  rfl

/-- Inverse Hom preimages for a composite equivalence run in reverse order;
its composite counit then identifies the two transported Serre duality maps. -/
theorem conj_eta_trans (D : SerreFunctorData k C) (Φ Ψ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k]
    [Ψ.functor.Additive] [Ψ.functor.Linear k]
    (A B : C) (φ : Module.Dual k (A ⟶ B)) :
    (D.conj (Φ.trans Ψ)).eta A B φ = ((D.conj Φ).conj Ψ).eta A B φ := by
  letI : Φ.inverse.Additive := inferInstance
  letI : Φ.inverse.Linear k := CategoryTheory.Equivalence.inverseLinear k Φ
  letI : Ψ.inverse.Additive := inferInstance
  letI : Ψ.inverse.Linear k := CategoryTheory.Equivalence.inverseLinear k Ψ
  letI : (Φ.trans Ψ).inverse.Additive := inferInstance
  letI : (Φ.trans Ψ).inverse.Linear k := CategoryTheory.Equivalence.inverseLinear k (Φ.trans Ψ)
  have hdual :
      (homEquivOfFullyFaithful (k := k) (Φ.trans Ψ).inverse
        (Φ.trans Ψ).fullyFaithfulInverse A B).symm.dualMap φ =
      (homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse
        (Ψ.inverse.obj A) (Ψ.inverse.obj B)).symm.dualMap
        ((homEquivOfFullyFaithful (k := k) Ψ.inverse Ψ.fullyFaithfulInverse
          A B).symm.dualMap φ) := by
    ext h
    simp [LinearEquiv.dualMap_apply, homEquivOfFullyFaithful, preimage_inverse_trans]
    rfl
  dsimp [conj, etaConj]
  change homEquivCounit (k := k) (Φ.trans Ψ) B (D.S.obj ((Φ.trans Ψ).inverse.obj A))
      (D.eta ((Φ.trans Ψ).inverse.obj A) ((Φ.trans Ψ).inverse.obj B)
        ((homEquivOfFullyFaithful (k := k) (Φ.trans Ψ).inverse
          (Φ.trans Ψ).fullyFaithfulInverse A B).symm.dualMap φ)) =
    homEquivCounit (k := k) Ψ B ((Φ.inverse ⋙ D.S ⋙ Φ.functor).obj (Ψ.inverse.obj A))
      (homEquivCounit (k := k) Φ (Ψ.inverse.obj B)
        (D.S.obj (Φ.inverse.obj (Ψ.inverse.obj A)))
        (D.eta (Φ.inverse.obj (Ψ.inverse.obj A)) (Φ.inverse.obj (Ψ.inverse.obj B))
          ((homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse
            (Ψ.inverse.obj A) (Ψ.inverse.obj B)).symm.dualMap
              ((homEquivOfFullyFaithful (k := k) Ψ.inverse Ψ.fullyFaithfulInverse
                A B).symm.dualMap φ))))
  rw [hdual]
  rw [homEquivCounit_trans]
  rfl

/-- Equality of the transported duality maps forces the canonical comparison
between composite and successive conjugation to be the identity on each object. -/
theorem conj_trans_uniqueIso_hom_app_eq_id
    (D : SerreFunctorData k C) (Φ Ψ : C ≌ C)
    [Φ.functor.Additive] [Φ.functor.Linear k]
    [Ψ.functor.Additive] [Ψ.functor.Linear k]
    (A : C) :
    ((D.conj (Φ.trans Ψ)).uniqueIso ((D.conj Φ).conj Ψ)).hom.app A = 𝟙 _ := by
  rw [uniqueIso_hom_app, uniqueIsoApp_hom_eq]
  rw [compareEquiv_apply]
  rw [← conj_eta_trans D Φ Ψ A ((D.conj (Φ.trans Ψ)).S.obj A)]
  exact LinearEquiv.apply_symm_apply _ _

private theorem eta_conj_refl (D : SerreFunctorData k C) (A B : C)
    (φ : Module.Dual k (A ⟶ B)) :
    (letI : (Equivalence.refl : C ≌ C).functor.Additive := by
       change (𝟭 C).Additive
       infer_instance
     letI : (Equivalence.refl : C ≌ C).functor.Linear k := by
       change (𝟭 C).Linear k
       infer_instance
     (D.conj (Equivalence.refl : C ≌ C)).eta A B φ = D.eta A B φ) := by
  letI : (Equivalence.refl : C ≌ C).functor.Additive := by
    change (𝟭 C).Additive
    infer_instance
  letI : (Equivalence.refl : C ≌ C).functor.Linear k := by
    change (𝟭 C).Linear k
    infer_instance
  let Φ : C ≌ C := Equivalence.refl
  letI : Φ.inverse.Additive := inferInstance
  letI : Φ.inverse.Linear k := CategoryTheory.Equivalence.inverseLinear k Φ
  have hpre (f : A ⟶ B) : Φ.fullyFaithfulInverse.preimage f = f := by
    have h := Φ.fullyFaithfulInverse.map_preimage f
    change (𝟭 C).map (Φ.fullyFaithfulInverse.preimage f) = f at h
    simpa only [Functor.id_map, Functor.id_obj] using h
  have hdual :
      (homEquivOfFullyFaithful Φ.inverse Φ.fullyFaithfulInverse A B).symm.dualMap φ = φ := by
    ext f
    simp [LinearEquiv.dualMap_apply, homEquivOfFullyFaithful, hpre]
    rfl
  change homEquivCounit Φ B (D.S.obj A)
      (D.eta A B
        ((homEquivOfFullyFaithful Φ.inverse Φ.fullyFaithfulInverse A B).symm.dualMap φ)) =
        D.eta A B φ
  rw [hdual]
  dsimp [homEquivCounit, homEquivOfFullyFaithful, Φ]
  change (𝟙 B ≫ (D.eta A B) φ) ≫ 𝟙 (D.S.obj A) = (D.eta A B) φ
  simp

private theorem uniqueIso_conj_refl_hom_app (D : SerreFunctorData k C) (A : C) :
    (letI : (Equivalence.refl : C ≌ C).functor.Additive := by
       change (𝟭 C).Additive
       infer_instance
     letI : (Equivalence.refl : C ≌ C).functor.Linear k := by
       change (𝟭 C).Linear k
       infer_instance
     (D.uniqueIso (D.conj (Equivalence.refl : C ≌ C))).hom.app A = 𝟙 _) := by
  letI : (Equivalence.refl : C ≌ C).functor.Additive := by
    change (𝟭 C).Additive
    infer_instance
  letI : (Equivalence.refl : C ≌ C).functor.Linear k := by
    change (𝟭 C).Linear k
    infer_instance
  rw [uniqueIso_hom_app, uniqueIsoApp_hom_eq, compareEquiv_apply]
  rw [eta_conj_refl D A (D.S.obj A)]
  exact LinearEquiv.apply_symm_apply _ _

/-- Reflexive η compatibility and Serre uniqueness normalize transport by
the identity equivalence to the functor unitors. This states no shift coherence. -/
theorem transportIso_refl (D : SerreFunctorData k C) :
    (letI : (Equivalence.refl : C ≌ C).functor.Additive := by
       change (𝟭 C).Additive
       infer_instance
     letI : (Equivalence.refl : C ≌ C).functor.Linear k := by
       change (𝟭 C).Linear k
       infer_instance
     D.transportIso (Equivalence.refl : C ≌ C) =
       Functor.leftUnitor D.S ≪≫ (Functor.rightUnitor D.S).symm) := by
  letI : (Equivalence.refl : C ≌ C).functor.Additive := by
    change (𝟭 C).Additive
    infer_instance
  letI : (Equivalence.refl : C ≌ C).functor.Linear k := by
    change (𝟭 C).Linear k
    infer_instance
  ext A
  have h := uniqueIso_conj_refl_hom_app D A
  change (D.uniqueIsoApp (D.conj (Equivalence.refl : C ≌ C)) A).hom = 𝟙 _ at h
  simp only [transportIso, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.leftUnitor_hom_app]
  erw [uniqueIso_hom_app]
  erw [h]
  simp [Equivalence.refl, Functor.associator_inv_app]
  erw [D.S.map_id]
  erw [Category.id_comp, Category.id_comp, Category.id_comp]

section TransportFunctoriality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (D : SerreFunctorData k C) (Φ : C ≌ C)
  [Φ.functor.Additive] [Φ.functor.Linear k]

private theorem transport_component (X : C) :
    (D.transportIso Φ).inv.app X ≫
      (D.uniqueIso (D.conj Φ)).hom.app (Φ.functor.obj X) =
    Φ.functor.map (D.S.map (Φ.unitIso.hom.app X)) := by
  unfold SerreFunctorData.transportIso
  simp only [Iso.trans_inv, NatTrans.comp_app,
    Equivalence.funInvIdAssoc_inv_app, Functor.isoWhiskerLeft_inv,
    Functor.associator_inv_app, Functor.whiskerLeft_app,
    Category.assoc, D.uniqueIso_hom_app]
  rw [← D.uniqueIso_hom_app]
  simp only [Iso.inv_hom_id_app]
  simp only [Iso.symm_inv, Functor.associator_hom_app, Functor.comp_map,
    Category.id_comp]
  dsimp only [SerreFunctorData.conj, Functor.comp_obj]
  simp only [Category.comp_id]

omit [Preadditive C] [Φ.functor.Additive] in
private theorem counit_inv_eq_map_unit (X : C) :
    (Φ.counitIso.app (Φ.functor.obj X)).inv =
      Φ.functor.map (Φ.unitIso.hom.app X) := by
  have h := (Φ.counitIso.app (Φ.functor.obj X)).eq_comp_inv.mpr
    (Φ.functor_unitIso_comp X)
  simpa only [Category.id_comp] using h.symm

private theorem homEquivCounit_symm_map (X : C) (x : X ⟶ D.S.obj X) :
    (homEquivCounit (k := k) Φ (Φ.functor.obj X)
      (D.S.obj (Φ.inverse.obj (Φ.functor.obj X)))).symm
        (Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X))) =
    (Φ.unitIso.app X).inv ≫ x ≫ D.S.map (Φ.unitIso.hom.app X) := by
  apply (homEquivCounit (k := k) Φ (Φ.functor.obj X)
    (D.S.obj (Φ.inverse.obj (Φ.functor.obj X)))).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [homEquivCounit, LinearEquiv.trans_apply, Linear.homCongr_apply,
    homEquivOfFullyFaithful, Iso.refl_hom, Category.comp_id]
  rw [counit_inv_eq_map_unit Φ X]
  change Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X)) =
    Φ.functor.map (Φ.unitIso.hom.app X) ≫
      Φ.functor.map ((Φ.unitIso.app X).inv ≫ x ≫ D.S.map (Φ.unitIso.hom.app X))
  have hmor : Φ.unitIso.hom.app X ≫
      ((Φ.unitIso.app X).inv ≫ x ≫ D.S.map (Φ.unitIso.hom.app X)) =
      x ≫ D.S.map (Φ.unitIso.hom.app X) := by
    change (Φ.unitIso.app X).hom ≫
      ((Φ.unitIso.app X).inv ≫ x ≫ D.S.map (Φ.unitIso.hom.app X)) =
      x ≫ D.S.map (Φ.unitIso.hom.app X)
    simp only [Iso.hom_inv_id_assoc]
  calc
    Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X)) =
        Φ.functor.map (Φ.unitIso.hom.app X ≫
          ((Φ.unitIso.app X).inv ≫ x ≫ D.S.map (Φ.unitIso.hom.app X))) :=
      congrArg Φ.functor.map hmor.symm
    _ = Φ.functor.map (Φ.unitIso.hom.app X) ≫
          Φ.functor.map ((Φ.unitIso.app X).inv ≫ x ≫ D.S.map (Φ.unitIso.hom.app X)) :=
      Φ.functor.map_comp _ _

private theorem etaConj_eval (X : C) (x : X ⟶ D.S.obj X) :
    ((D.conj Φ).eta (Φ.functor.obj X) (Φ.functor.obj X)).symm
      (Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X)))
      (𝟙 (Φ.functor.obj X)) = D.trace X x := by
  change (etaConj D Φ (Φ.functor.obj X) (Φ.functor.obj X)).symm
    (Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X)))
    (𝟙 (Φ.functor.obj X)) = D.trace X x
  simp only [etaConj, LinearEquiv.symm_trans_apply]
  letI : Φ.inverse.Additive := inferInstance
  letI : Φ.inverse.Linear k := CategoryTheory.Equivalence.inverseLinear k Φ
  let e := homEquivOfFullyFaithful (k := k) Φ.inverse Φ.fullyFaithfulInverse
    (Φ.functor.obj X) (Φ.functor.obj X)
  let f := D.eta (Φ.inverse.obj (Φ.functor.obj X))
    (Φ.inverse.obj (Φ.functor.obj X))
  let c := homEquivCounit (k := k) Φ (Φ.functor.obj X)
    (D.S.obj (Φ.inverse.obj (Φ.functor.obj X)))
  change ((e.symm.dualMap).symm
      (f.symm (c.symm (Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X))))))
      (𝟙 (Φ.functor.obj X)) = D.trace X x
  have hh := homEquivCounit_symm_map D Φ X x
  have hstep : ((e.symm.dualMap).symm
      (f.symm (c.symm (Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X))))))
      (𝟙 (Φ.functor.obj X)) =
    ((e.symm.dualMap).symm
      (f.symm ((Φ.unitIso.app X).inv ≫ x ≫ D.S.map (Φ.unitIso.hom.app X))))
      (𝟙 (Φ.functor.obj X)) := by
    exact congrArg (fun q => ((e.symm.dualMap).symm (f.symm q)) (𝟙 _)) hh
  rw [hstep]
  simp only [LinearEquiv.dualMap_symm, LinearEquiv.symm_symm,
    LinearEquiv.dualMap_apply, e, homEquivOfFullyFaithful]
  change (f.symm ((Φ.unitIso.app X).inv ≫ x ≫ D.S.map (Φ.unitIso.hom.app X)))
      (Φ.inverse.map (𝟙 (Φ.functor.obj X))) = D.trace X x
  rw [Φ.inverse.map_id]
  change D.trace (Φ.inverse.obj (Φ.functor.obj X))
      ((Φ.unitIso.app X).inv ≫ x ≫ D.S.map (Φ.unitIso.hom.app X)) =
    D.trace X x
  have htrace := D.trace_comp (Φ.unitIso.hom.app X) ((Φ.unitIso.app X).inv ≫ x)
  have hunit : Φ.unitIso.hom.app X ≫ (Φ.unitIso.app X).inv = 𝟙 X := by
    change (Φ.unitIso.app X).hom ≫ (Φ.unitIso.app X).inv = 𝟙 X
    exact (Φ.unitIso.app X).hom_inv_id
  simpa only [Functor.comp_obj, Functor.id_obj, ← Category.assoc,
    hunit, Category.id_comp] using htrace

/-- Transport by a linear autoequivalence preserves the Serre trace. The inverse
component sends the mapped endomorphism into the Serre target at the image. -/
theorem trace_transport (X : C) (x : X ⟶ D.S.obj X) :
    D.trace (Φ.functor.obj X)
      (Φ.functor.map x ≫ (D.transportIso Φ).inv.app X) = D.trace X x := by
  let y : Φ.functor.obj X ⟶ D.S.obj (Φ.functor.obj X) :=
    Φ.functor.map x ≫ (D.transportIso Φ).inv.app X
  let ψ : Module.Dual k (Φ.functor.obj X ⟶ Φ.functor.obj X) :=
    (D.eta (Φ.functor.obj X) (Φ.functor.obj X)).symm y
  have hu := D.uniqueIso_compat (D.conj Φ) ψ
  simp only [ψ, LinearEquiv.apply_symm_apply] at hu
  dsimp only [y] at hu
  have hu' : (D.conj Φ).eta (Φ.functor.obj X) (Φ.functor.obj X) ψ =
      Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X)) := by
    rw [← hu]
    change (Φ.functor.map x ≫ (D.transportIso Φ).inv.app X) ≫
      (D.uniqueIso (D.conj Φ)).hom.app (Φ.functor.obj X) = _
    rw [Category.assoc, transport_component D Φ X, ← Φ.functor.map_comp]
  have hψ : ψ =
      ((D.conj Φ).eta (Φ.functor.obj X) (Φ.functor.obj X)).symm
        (Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X))) := by
    apply ((D.conj Φ).eta (Φ.functor.obj X) (Φ.functor.obj X)).injective
    simpa only [LinearEquiv.apply_symm_apply] using hu'
  calc
    D.trace (Φ.functor.obj X)
        (Φ.functor.map x ≫ (D.transportIso Φ).inv.app X) =
        ψ (𝟙 (Φ.functor.obj X)) := rfl
    _ = ((D.conj Φ).eta (Φ.functor.obj X) (Φ.functor.obj X)).symm
        (Φ.functor.map (x ≫ D.S.map (Φ.unitIso.hom.app X)))
        (𝟙 (Φ.functor.obj X)) := congrArg (fun q => q (𝟙 _)) hψ
    _ = D.trace X x := etaConj_eval D Φ X x

private theorem pairing_eq_trace (A B : C) (f : A ⟶ B) (h : B ⟶ D.S.obj A) :
    D.pairing A B f h = D.trace A (f ≫ h) := by
  let φ := (D.eta A B).symm h
  have hn := D.naturality_right f φ
  simp only [φ, LinearEquiv.apply_symm_apply] at hn
  change (D.eta A A) (φ.comp (Linear.rightComp k A f)) = f ≫ h at hn
  change (D.eta A B).symm h f = (D.eta A A).symm (f ≫ h) (𝟙 A)
  rw [← hn]
  simp [φ, Linear.rightComp]

/-- Transport is natural in an isomorphism of linear equivalence functors.
The comparison is detected by the nondegenerate Serre pairing and trace. -/
theorem transportIso_isoCompat (Ψ : C ≌ C)
    [Ψ.functor.Additive] [Ψ.functor.Linear k]
    (e : Φ.functor ≅ Ψ.functor) (A : C) :
    e.hom.app (D.S.obj A) ≫ (D.transportIso Ψ).inv.app A =
      (D.transportIso Φ).inv.app A ≫ D.S.map (e.hom.app A) := by
  let z (x : Ψ.functor.obj A ⟶ Φ.functor.obj (D.S.obj A)) : A ⟶ D.S.obj A :=
    Φ.fullyFaithfulFunctor.preimage (e.hom.app A ≫ x)
  have hΦ (x : Ψ.functor.obj A ⟶ Φ.functor.obj (D.S.obj A)) :
      Φ.functor.map (z x) = e.hom.app A ≫ x :=
    Φ.fullyFaithfulFunctor.map_preimage _
  have hΨ (x : Ψ.functor.obj A ⟶ Φ.functor.obj (D.S.obj A)) :
      Ψ.functor.map (z x) = x ≫ e.hom.app (D.S.obj A) := by
    rw [← cancel_epi (e.hom.app A)]
    rw [← e.hom.naturality (z x), hΦ]
    simp only [Category.assoc]
  apply (D.eta (Ψ.functor.obj A) (Φ.functor.obj (D.S.obj A))).symm.injective
  apply LinearMap.ext
  intro x
  change D.pairing (Ψ.functor.obj A) (Φ.functor.obj (D.S.obj A)) x
      (e.hom.app (D.S.obj A) ≫ (D.transportIso Ψ).inv.app A) =
    D.pairing (Ψ.functor.obj A) (Φ.functor.obj (D.S.obj A)) x
      ((D.transportIso Φ).inv.app A ≫ D.S.map (e.hom.app A))
  rw [pairing_eq_trace D, pairing_eq_trace D]
  have htrace : D.trace (Ψ.functor.obj A)
      ((x ≫ e.hom.app (D.S.obj A)) ≫ (D.transportIso Ψ).inv.app A) =
      D.trace (Ψ.functor.obj A)
      ((x ≫ (D.transportIso Φ).inv.app A) ≫ D.S.map (e.hom.app A)) := by
    calc
      D.trace (Ψ.functor.obj A)
        ((x ≫ e.hom.app (D.S.obj A)) ≫ (D.transportIso Ψ).inv.app A) =
      D.trace (Ψ.functor.obj A)
        (Ψ.functor.map (z x) ≫ (D.transportIso Ψ).inv.app A) := by
          rw [hΨ]
    _ = D.trace A (z x) := trace_transport D Ψ A (z x)
    _ = D.trace (Φ.functor.obj A)
        (Φ.functor.map (z x) ≫ (D.transportIso Φ).inv.app A) :=
          (trace_transport D Φ A (z x)).symm
    _ = D.trace (Φ.functor.obj A)
        ((e.hom.app A ≫ x) ≫ (D.transportIso Φ).inv.app A) := by rw [hΦ]
    _ = D.trace (Ψ.functor.obj A)
        ((x ≫ (D.transportIso Φ).inv.app A) ≫ D.S.map (e.hom.app A)) := by
          rw [D.trace_comp]
          rw [Category.assoc]
  simpa only [Category.assoc] using htrace

/-- Compare both transports through the Serre pairing: trace preservation
and full faithfulness determine their inverse components without expanding
composite unit and counit maps. -/
theorem transportIso_trans (Ψ : C ≌ C)
    [Ψ.functor.Additive] [Ψ.functor.Linear k]
    [(Φ.trans Ψ).functor.Additive] [(Φ.trans Ψ).functor.Linear k]
    (A : C) :
    (D.transportIso (Φ.trans Ψ)).inv.app A =
      Ψ.functor.map ((D.transportIso Φ).inv.app A) ≫
        (D.transportIso Ψ).inv.app (Φ.functor.obj A) := by
  let Q := Φ.trans Ψ
  apply (D.eta (Q.functor.obj A) (Q.functor.obj (D.S.obj A))).symm.injective
  apply LinearMap.ext
  intro x
  change D.pairing (Q.functor.obj A) (Q.functor.obj (D.S.obj A)) x
      ((D.transportIso Q).inv.app A) =
    D.pairing (Q.functor.obj A) (Q.functor.obj (D.S.obj A)) x
      (Ψ.functor.map ((D.transportIso Φ).inv.app A) ≫
        (D.transportIso Ψ).inv.app (Φ.functor.obj A))
  rw [pairing_eq_trace D, pairing_eq_trace D]
  let y := Q.fullyFaithfulFunctor.preimage x
  have hy : Q.functor.map y = x := Q.fullyFaithfulFunctor.map_preimage x
  rw [← hy]
  calc
    D.trace (Q.functor.obj A)
        (Q.functor.map y ≫ (D.transportIso Q).inv.app A) =
      D.trace A y := trace_transport D Q A y
    _ = D.trace (Φ.functor.obj A)
        (Φ.functor.map y ≫ (D.transportIso Φ).inv.app A) :=
      (trace_transport D Φ A y).symm
    _ = D.trace (Q.functor.obj A)
        (Ψ.functor.map (Φ.functor.map y ≫ (D.transportIso Φ).inv.app A) ≫
          (D.transportIso Ψ).inv.app (Φ.functor.obj A)) :=
      (trace_transport D Ψ (Φ.functor.obj A)
        (Φ.functor.map y ≫ (D.transportIso Φ).inv.app A)).symm
    _ = D.trace (Q.functor.obj A)
        (Q.functor.map y ≫ Ψ.functor.map ((D.transportIso Φ).inv.app A) ≫
          (D.transportIso Ψ).inv.app (Φ.functor.obj A)) := by
      change D.trace (Q.functor.obj A)
          (Ψ.functor.map (Φ.functor.map y ≫ (D.transportIso Φ).inv.app A) ≫
            (D.transportIso Ψ).inv.app (Φ.functor.obj A)) =
        D.trace (Q.functor.obj A)
          (Ψ.functor.map (Φ.functor.map y) ≫
            Ψ.functor.map ((D.transportIso Φ).inv.app A) ≫
            (D.transportIso Ψ).inv.app (Φ.functor.obj A))
      rw [Ψ.functor.map_comp, Category.assoc]


end TransportFunctoriality

end SerreFunctorData

end CategoryTheory.SerreFunctor
