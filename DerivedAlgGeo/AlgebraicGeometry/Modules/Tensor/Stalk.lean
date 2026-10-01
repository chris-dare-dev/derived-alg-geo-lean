/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk
import DerivedAlgGeo.Topology.Sheaves.ModuleTensor.StalkTensor

/-!
# Scheme-module tensor and module stalks

The natural comparison between the sheaf tensor functor and tensoring modules over
the local ring at a point. It transports the existing presheaf tensor-stalk
equivalence through the canonical module-sheafification stalk isomorphism.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.tensorLeftFunctorStalkNatIso` is natural
  in the variable module sheaf. No flatness assumption is needed.

## Main results

Its components identify the stalk of sheaf tensor with tensoring the two
stalk modules over the local ring.

## Implementation notes

The repository's module colimit stalk and Mathlib's presheaf stalk have
different bundled module presentations. A private natural isomorphism compares
them before applying the presheaf tensor-stalk equivalence.

## References

This specializes `PresheafOfModules.stalkTensorEquiv` and its naturality to
the canonical scheme-module tensor functor.

## Tags

module sheaf, tensor, stalk, natural isomorphism
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory TensorProduct
open AlgebraicGeometry

universe u
noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

private def stalkPresentationEquiv (X : Scheme.{u})
    (P : _root_.PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat RingCat)) (x : X) :
    ((presheafModuleStalkFunctor X x).obj P) ≃ₗ[X.presheaf.stalk x]
      ↑(TopCat.Presheaf.stalk P.presheaf x) := by
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  refine { toFun := fun m => m
           invFun := fun m => m
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq P.presheaf m hxU
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) x hxV r]
  simp only [RingHom.id_apply]
  erw [← _root_.PresheafOfModules.germ_smul P x V hxV]
  exact _root_.PresheafOfModules.ModuleColimit.smul_eq
    (moduleStalkRingIsColimit X x) (colimit.isColimit _) _ _

private theorem stalkPresentationEquiv_naturality (X : Scheme.{u})
    {P Q : _root_.PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat RingCat)}
    (g : P ⟶ Q) (x : X) (m : (presheafModuleStalkFunctor X x).obj P) :
    stalkPresentationEquiv X Q x ((presheafModuleStalkFunctor X x).map g m) =
      _root_.PresheafOfModules.stalkMap g x (stalkPresentationEquiv X P x m) := by
  rfl

private def mathlibStalkModuleFunctor (X : Scheme.{u}) (x : X) :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
      ModuleCat.{u} (X.presheaf.stalk x) where
  obj P := ModuleCat.of _ (↑(TopCat.Presheaf.stalk P.presheaf x))
  map g := ModuleCat.ofHom (_root_.PresheafOfModules.stalkMap g x)
  map_id P := by
    ext m
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map (𝟙 P))) m = m
    simp
  map_comp g h := by
    ext m
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map (g ≫ h))) m =
      (((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((PresheafOfModules.toPresheaf _).map g)) ≫
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf _).map h))) m
    simp

private def stalkPresentationNatIso (X : Scheme.{u}) (x : X) :
    presheafModuleStalkFunctor X x ≅ mathlibStalkModuleFunctor X x :=
  NatIso.ofComponents
    (fun P => (stalkPresentationEquiv X P x).toModuleIso)
    (fun {P Q} g => by
      apply ModuleCat.hom_ext
      ext m
      exact stalkPresentationEquiv_naturality X g x m)

private local instance (X : Scheme.{u}) :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  _root_.PresheafOfModules.monoidalCategory (R := X.presheaf)

private def presheafTensorStalkNatIso (X : Scheme.{u})
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) (x : X) :
    tensorLeft P ⋙ mathlibStalkModuleFunctor X x ≅
      mathlibStalkModuleFunctor X x ⋙
        tensorLeft ((mathlibStalkModuleFunctor X x).obj P) :=
  NatIso.ofComponents
    (fun Q => (_root_.PresheafOfModules.stalkTensorEquiv P Q x).symm.toModuleIso)
    (fun {Q S} g => by
      apply ModuleCat.hom_ext
      ext m
      obtain ⟨t, rfl⟩ :=
        (_root_.PresheafOfModules.stalkTensorEquiv P Q x).surjective m
      simp only [Functor.comp_map, ModuleCat.hom_comp, LinearMap.coe_comp,
        Function.comp_apply, LinearEquiv.toModuleIso_hom]
      dsimp [mathlibStalkModuleFunctor]
      simp only [curriedTensor_obj_map, ModuleCat.hom_whiskerLeft, ModuleCat.hom_ofHom]
      erw [LinearEquiv.symm_apply_apply]
      change (_root_.PresheafOfModules.stalkTensorEquiv P S x).symm
          (_root_.PresheafOfModules.stalkMapAdd (P ◁ g) x
            (_root_.PresheafOfModules.stalkTensorEquiv P Q x t)) =
        LinearMap.lTensor _ (_root_.PresheafOfModules.stalkMap g x) t
      apply (_root_.PresheafOfModules.stalkTensorEquiv P S x).injective
      simpa using _root_.PresheafOfModules.stalkMapAdd_whiskerLeft P g x t)

private def presheafTensorNativeStalkNatIso (X : Scheme.{u})
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) (x : X) :
    tensorLeft P ⋙ presheafModuleStalkFunctor X x ≅
      presheafModuleStalkFunctor X x ⋙
        tensorLeft ((presheafModuleStalkFunctor X x).obj P) := by
  let U := presheafModuleStalkFunctor X x
  let F := mathlibStalkModuleFunctor X x
  let e := stalkPresentationNatIso X x
  let T := tensorLeft P
  let W := tensorLeft (F.obj P)
  let a : W ≅ tensorLeft (U.obj P) :=
    (curriedTensor (ModuleCat.{u} (X.presheaf.stalk x))).mapIso (e.app P).symm
  exact Functor.isoWhiskerLeft T e ≪≫
    presheafTensorStalkNatIso X P x ≪≫
    Functor.isoWhiskerRight e.symm W ≪≫
    Functor.isoWhiskerLeft U a

/-- Tensoring a scheme-module sheaf commutes naturally with taking a module stalk.
The target tensors the two stalk modules over the local ring at `x`. -/
def tensorLeftFunctorStalkNatIso (X : Scheme.{u}) (L : X.Modules) (x : X) :
    tensorLeftFunctor L ⋙ moduleStalkFunctor X x ≅
      moduleStalkFunctor X x ⋙
        tensorLeft ((moduleStalkFunctor X x).obj L) := by
  let S := toPresheafOfModules X
  let P := S.obj L
  let T := tensorLeft P
  let A := _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let V := moduleStalkFunctor X x
  let U := presheafModuleStalkFunctor X x
  let e := presheafModuleStalkSheafificationIso X x
  exact Functor.associator (S ⋙ T) A V ≪≫
    Functor.isoWhiskerLeft (S ⋙ T) e.symm ≪≫
    Functor.associator S T U ≪≫
    Functor.isoWhiskerLeft S (presheafTensorNativeStalkNatIso X P x) ≪≫
    (Functor.associator S U (tensorLeft (U.obj P))).symm

end AlgebraicGeometry.Scheme.Modules
