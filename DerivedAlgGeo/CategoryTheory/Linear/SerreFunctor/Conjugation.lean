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

end SerreFunctorData

end CategoryTheory.SerreFunctor
