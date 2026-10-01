/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Flat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Colimits
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.QuasiIso

/-!
# Exact tensoring by a flat scheme-module sheaf

A module sheaf flat over the identity makes ordinary tensoring exact in either
slot. The results here show that each partial tensor functor preserves homology
and its termwise action preserves quasi-isomorphisms of complexes of any shape.
These results treat a flat sheaf fixed in degree zero; K-flatness of a complex
of flat sheaves and arbitrary derived pullback remain separate.

## Proof ingredients

`PresheafOfModules.stalkTensorEquiv` and
`PresheafOfModules.stalkMapAdd_whiskerLeft` transfer
`Module.Flat.lTensor_preserves_injective_linearMap` to sheaf stalks. Joint
stalk reflection then gives mono preservation. Tensor colimits supply
cokernels, so `Functor.preservesHomology_of_preservesMonos_and_cokernels`
gives homology preservation. A private natural tensor-commutativity isomorphism
handles the right slot. `HomologicalComplex.quasiIso_map_of_preservesHomology`
gives the arbitrary-shape quasi-isomorphism corollaries.

## Main results

* `AlgebraicGeometry.Scheme.Modules.tensorLeftFunctor_preservesHomology_of_isFlatOverId`
* `AlgebraicGeometry.Scheme.Modules.tensorRight_preservesHomology_of_isFlatOverId`
* `AlgebraicGeometry.Scheme.Modules.quasiIso_map_tensorLeftFunctor_of_isFlatOverId`
* `AlgebraicGeometry.Scheme.Modules.quasiIso_map_tensorRight_of_isFlatOverId`
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
universe u v
noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

private local instance (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  _root_.PresheafOfModules.monoidalCategory (R := X.presheaf)

private local instance (X : Scheme.{u}) : SymmetricCategory X.PresheafOfModules :=
  _root_.PresheafOfModules.symmetricCategory (R := X.presheaf)

private def flatTensorStalkComparison (X : Scheme.{u}) (P : _root_.PresheafOfModules.{u}
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

private lemma flatTensorStalk_injective (X : Scheme.{u})
    (M P Q : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (g : P ⟶ Q) (x : X)
    [Module.Flat (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x)]
    (hg : Function.Injective (_root_.PresheafOfModules.stalkMap g x)) :
    Function.Injective (_root_.PresheafOfModules.stalkMapAdd (M ◁ g) x) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (_root_.PresheafOfModules.stalkTensorEquiv M P x).surjective a
  obtain ⟨b, rfl⟩ := (_root_.PresheafOfModules.stalkTensorEquiv M P x).surjective b
  rw [_root_.PresheafOfModules.stalkMapAdd_whiskerLeft,
    _root_.PresheafOfModules.stalkMapAdd_whiskerLeft] at hab
  have hab' := (_root_.PresheafOfModules.stalkTensorEquiv M Q x).injective hab
  have hab'' := Module.Flat.lTensor_preserves_injective_linearMap
    (_root_.PresheafOfModules.stalkMap g x) hg hab'
  exact congrArg (_root_.PresheafOfModules.stalkTensorEquiv M P x) hab''

private lemma mono_tensorLeft_of_isFlatOverId (X : Scheme.{u}) (L : X.Modules)
    (hL : IsFlatOver (𝟙 X) L) {M N : X.Modules} (f : M ⟶ N) [Mono f] :
    Mono ((tensorLeftFunctor L).map f) := by
  letI (x : X) : PreservesFiniteLimits (moduleStalkFunctor X x) :=
    moduleStalkFunctor_preservesFiniteLimits X x
  letI (x : X) : Mono ((moduleStalkFunctor X x).map ((tensorLeftFunctor L).map f)) := by
    let LP : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := L.val
    let MP : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := M.val
    let NP : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat) := N.val
    let g : MP ⟶ NP := f.val
    haveI : Module.Flat (X.presheaf.stalk x) ((moduleStalkFunctor X x).obj L) :=
      (isFlatOverId_iff_stalkwiseFlat X L).mp hL x
    haveI : Module.Flat (X.presheaf.stalk x) ((presheafModuleStalkFunctor X x).obj LP) := by
      change Module.Flat (X.presheaf.stalk x) ((moduleStalkFunctor X x).obj L)
      infer_instance
    haveI : Module.Flat (X.presheaf.stalk x) ↑(TopCat.Presheaf.stalk LP.presheaf x) :=
      Module.Flat.of_linearEquiv (flatTensorStalkComparison X LP x).symm
    have hf : Function.Injective (_root_.PresheafOfModules.stalkMap g x) :=
      (ModuleCat.mono_iff_injective ((moduleStalkFunctor X x).map f)).mp inferInstance
    have hg : Function.Injective (_root_.PresheafOfModules.stalkMapAdd (LP ◁ g) x) :=
      flatTensorStalk_injective X LP MP NP g x hf
    let e := presheafModuleStalkSheafificationIso X x
    haveI : Mono ((presheafModuleStalkFunctor X x).map (LP ◁ g)) :=
      (ModuleCat.mono_iff_injective _).mpr hg
    change Mono ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙
      moduleStalkFunctor X x).map (LP ◁ g))
    apply (mono_comp_iff_of_isIso (e.hom.app (LP ⊗ MP)) _).mp
    rw [← e.hom.naturality (LP ◁ g)]
    infer_instance
  exact (moduleStalkFunctors_jointlyReflectIsomorphisms X).jointlyReflectMonomorphisms.mono _

/-- Stalkwise flatness preserves injectivity through the tensor-stalk comparison.
Joint stalk reflection gives mono preservation; tensor colimits supply cokernels. -/
theorem tensorLeftFunctor_preservesHomology_of_isFlatOverId (X : Scheme.{u}) (L : X.Modules)
    (hL : IsFlatOver (𝟙 X) L) : (tensorLeftFunctor L).PreservesHomology := by
  letI : (tensorLeftFunctor L).PreservesMonomorphisms :=
    ⟨fun f _ => mono_tensorLeft_of_isFlatOverId X L hL f⟩
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels (tensorLeftFunctor L)

private def flatTensorLeftRightIso (X : Scheme.{u}) (L : X.Modules) :
    tensorLeftFunctor L ≅ tensorRight L :=
  NatIso.ofComponents (fun M => tensorCommIso L M) (fun {M N} f => by
    change Scheme.Modules.tensorHom (𝟙 L) f ≫ (tensorCommIso L N).hom =
      (tensorCommIso L M).hom ≫ Scheme.Modules.tensorHom f (𝟙 L)
    unfold Scheme.Modules.tensorHom tensorCommIso
    simp only [Functor.mapIso_hom]
    rw [← Functor.map_comp, ← Functor.map_comp, BraidedCategory.braiding_naturality])

local instance tensorRightFiniteColimits (X : Scheme.{u}) (L : X.Modules) :
    PreservesFiniteColimits (tensorRight L) :=
  preservesFiniteColimits_of_natIso (flatTensorLeftRightIso X L)

local instance tensorRightAdditive (X : Scheme.{u}) (L : X.Modules) :
    (tensorRight L).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight L)
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Tensor symmetry transports the left-slot mono result to the right slot;
colimit preservation supplies the cokernel condition. -/
theorem tensorRight_preservesHomology_of_isFlatOverId (X : Scheme.{u}) (L : X.Modules)
    (hL : IsFlatOver (𝟙 X) L) : (tensorRight L).PreservesHomology := by
  letI : (tensorLeftFunctor L).PreservesMonomorphisms :=
    ⟨fun f _ => mono_tensorLeft_of_isFlatOverId X L hL f⟩
  letI : (tensorRight L).PreservesMonomorphisms :=
    Functor.preservesMonomorphisms.of_iso (flatTensorLeftRightIso X L)
  letI : PreservesFiniteColimits (tensorRight L) :=
    preservesFiniteColimits_of_natIso (flatTensorLeftRightIso X L)
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight L)
  letI : (tensorRight L).Additive := Functor.additive_of_preservesBinaryBiproducts _
  exact Functor.preservesHomology_of_preservesMonos_and_cokernels (tensorRight L)

/-- Homology preservation of left tensor gives the termwise complex result for any
shape. The fixed flat sheaf is a degree-zero factor, not a K-flat complex. -/
theorem quasiIso_map_tensorLeftFunctor_of_isFlatOverId (X : Scheme.{u}) (L : X.Modules)
    (hL : IsFlatOver (𝟙 X) L)
    {ι : Type v} {c : ComplexShape ι} {K K' : HomologicalComplex X.Modules c}
    (f : K ⟶ K') [QuasiIso f] :
    QuasiIso (((tensorLeftFunctor L).mapHomologicalComplex c).map f) := by
  letI := tensorLeftFunctor_preservesHomology_of_isFlatOverId X L hL
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f (tensorLeftFunctor L)

/-- Tensor symmetry supplies the right-slot homology preservation used termwise
on any complex shape, with the flat sheaf fixed as a degree-zero factor. -/
theorem quasiIso_map_tensorRight_of_isFlatOverId (X : Scheme.{u}) (L : X.Modules)
    (hL : IsFlatOver (𝟙 X) L)
    {ι : Type v} {c : ComplexShape ι} {K K' : HomologicalComplex X.Modules c}
    (f : K ⟶ K') [QuasiIso f] :
    QuasiIso (((tensorRight L).mapHomologicalComplex c).map f) := by
  letI : PreservesFiniteColimits (tensorRight L) :=
    preservesFiniteColimits_of_natIso (flatTensorLeftRightIso X L)
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorRight L)
  letI : (tensorRight L).Additive := Functor.additive_of_preservesBinaryBiproducts _
  letI := tensorRight_preservesHomology_of_isFlatOverId X L hL
  exact HomologicalComplex.quasiIso_map_of_preservesHomology f (tensorRight L)

end AlgebraicGeometry.Scheme.Modules
