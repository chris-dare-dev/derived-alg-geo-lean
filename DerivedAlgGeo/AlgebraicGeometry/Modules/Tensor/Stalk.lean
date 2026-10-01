/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Sections
import DerivedAlgGeo.Topology.Sheaves.ModuleTensor.StalkTensor

/-!
# Stalks of the sheafified tensor product

The stalk of a sheafified tensor product of module sheaves is the tensor product of the stalks,
over the local ring: `(M ⊗ N)ₓ ≅ Mₓ ⊗[𝒪ₓ] Nₓ`, with the germ of a pure tensor of sections going
to the tensor of the germs.

The module stalk functors `presheafModuleStalkFunctor`, `moduleStalkFunctor` are bundled through
Mathlib's `PresheafOfModules.colimitFunctor`, while the comparison of stalk and tensor product is
proved in `Topology/Sheaves/ModuleTensor/StalkTensor.lean` for Mathlib's own module structure on
`TopCat.Presheaf.stalk`. The two module structures on the same colimit agree
(`presheafModuleStalk_smul_eq`), which is the only place both are used.

## Main definitions

* `presheafModuleGerm_exists`, `presheafModuleGerm_smul`, `presheafModuleGerm_res`,
  `presheafModuleStalkFunctor_map_germ`: calculus of germs in the module stalk.
* `presheafModuleStalkBridge`: the identification of the two module structures.
* `presheafModuleStalkTensorEquiv`, `moduleStalkTensorEquiv`: stalk of a tensor of presheaves,
  respectively of sheaves, with their pure-tensor formulas.
-/

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u}) (x : X)

/-- **Every element of the module stalk is a germ of a section over some neighbourhood.** -/
theorem presheafModuleGerm_exists (P : X.PresheafOfModules)
    (ξ : (presheafModuleStalkFunctor X x).obj P) :
    ∃ (U : X.Opens) (hx : x ∈ U) (p : P.obj (op U)), presheafModuleGerm X x P U hx p = ξ := by
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  obtain ⟨⟨⟨U, hx⟩⟩, p, hp⟩ := PresheafOfModules.ModuleColimit.ιM_jointly_surjective
    (hcR := moduleStalkRingIsColimit X x)
    (hcM := colimit.isColimit ((_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
      X.ringCatSheaf.obj).obj P).presheaf) ξ
  exact ⟨U, hx, p, hp⟩

/-- **Germs are linear over the germ of the structure sheaf.** -/
theorem presheafModuleGerm_smul (P : X.PresheafOfModules) (U : X.Opens) (hx : x ∈ U)
    (r : Γ(X, U)) (p : P.obj (op U)) :
    (X.presheaf.germ U x hx).hom r • presheafModuleGerm X x P U hx p =
      presheafModuleGerm X x P U hx (r • p) := by
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  exact PresheafOfModules.ModuleColimit.smul_eq (hcR := moduleStalkRingIsColimit X x)
    (hcM := colimit.isColimit ((_root_.PresheafOfModules.pushforward₀ (OpenNhds.inclusion x)
      X.ringCatSheaf.obj).obj P).presheaf) (U := op ⟨U, hx⟩) r p

/-- **A germ does not change on restriction to a smaller neighbourhood.** -/
theorem presheafModuleGerm_res (P : X.PresheafOfModules) {U V : X.Opens} (h : V ≤ U)
    (hx : x ∈ V) (p : P.obj (op U)) :
    presheafModuleGerm X x P V hx (P.map (homOfLE h).op p) =
      presheafModuleGerm X x P U (h hx) p := by
  letI : InitiallySmall.{u} (OpenNhds x) := initiallySmall_of_essentiallySmall _
  have := ConcreteCategory.congr_hom ((colimit.cocone ((_root_.PresheafOfModules.pushforward₀
    (OpenNhds.inclusion x) X.ringCatSheaf.obj).obj P).presheaf).w
      (show op (⟨U, h hx⟩ : OpenNhds x) ⟶ op ⟨V, hx⟩ from (homOfLE h).op)) p
  exact this

/-- **The module structure of `presheafModuleStalkFunctor` on a presheaf stalk agrees with
Mathlib's module structure on `TopCat.Presheaf.stalk`.** Both are characterized by their
compatibility with germs. -/
theorem presheafModuleStalk_smul_eq
    (P : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (r : X.presheaf.stalk x) (ξ : (presheafModuleStalkFunctor X x).obj P) :
    (show ToType (TopCat.Presheaf.stalk P.presheaf x) from r • ξ) =
      r • (show ToType (TopCat.Presheaf.stalk P.presheaf x) from ξ) := by
  obtain ⟨U, hx, p, rfl⟩ := presheafModuleGerm_exists X x P ξ
  obtain ⟨V, hxV, r₀, rfl⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
  have hW : x ∈ U ⊓ V := ⟨hx, hxV⟩
  have e1 : (X.presheaf.germ V x hxV).hom r₀ =
      (X.presheaf.germ (U ⊓ V) x hW).hom (X.presheaf.map (homOfLE inf_le_right).op r₀) :=
    (X.presheaf.germ_res_apply (homOfLE inf_le_right) x hW r₀).symm
  have e2 : presheafModuleGerm X x P U hx p =
      presheafModuleGerm X x P (U ⊓ V) hW (P.map (homOfLE inf_le_left).op p) :=
    (presheafModuleGerm_res X x P inf_le_left hW p).symm
  rw [e1, e2]
  refine (presheafModuleGerm_smul X x P (U ⊓ V) hW _ _).trans ?_
  exact PresheafOfModules.germ_smul P x (U ⊓ V) hW _ _


/-- The two module structures on a presheaf stalk agree. -/
def presheafModuleStalkBridge
    (P : _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (presheafModuleStalkFunctor X x).obj P ≃ₗ[X.presheaf.stalk x]
      ToType (TopCat.Presheaf.stalk P.presheaf x) :=
  { AddEquiv.refl _ with map_smul' := fun r ξ => presheafModuleStalk_smul_eq X x P r ξ }

private local instance tensorStalkPresheafMonoidal : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

open TensorProduct in
/-- The stalk of a tensor product of presheaves of modules. -/
def presheafModuleStalkTensorEquiv (P Q : X.PresheafOfModules) :
    (presheafModuleStalkFunctor X x).obj P ⊗[X.presheaf.stalk x]
        (presheafModuleStalkFunctor X x).obj Q ≃ₗ[X.presheaf.stalk x]
      (presheafModuleStalkFunctor X x).obj (P ⊗ Q) :=
  (TensorProduct.congr (presheafModuleStalkBridge X x P) (presheafModuleStalkBridge X x Q)) ≪≫ₗ
    PresheafOfModules.stalkTensorEquiv P Q x ≪≫ₗ (presheafModuleStalkBridge X x (P ⊗ Q)).symm


open TensorProduct in
/-- `presheafModuleStalkTensorEquiv` computes on a pure tensor of germs over one neighbourhood. -/
theorem presheafModuleStalkTensorEquiv_germ_tmul_germ (P Q : X.PresheafOfModules) (U : X.Opens)
    (hx : x ∈ U) (p : P.obj (op U)) (q : Q.obj (op U)) :
    presheafModuleStalkTensorEquiv X x P Q
      (presheafModuleGerm X x P U hx p ⊗ₜ presheafModuleGerm X x Q U hx q) =
    presheafModuleGerm X x (P ⊗ Q) U hx (p ⊗ₜ[Γ(X, U)] q) := by
  have := PresheafOfModules.stalkTensorEquiv_germ_tmul_germ P Q x U U hx hx p q
  rw [PresheafOfModules.germTmul_self] at this
  exact this


/-- **Two germs of module sheaves at one point come from sections over one common
neighbourhood.** -/
theorem moduleStalkGerm_exists_pair (M N : X.Modules)
    (a : (moduleStalkFunctor X x).obj M) (b : (moduleStalkFunctor X x).obj N) :
    ∃ (V : X.Opens) (hV : x ∈ V) (m : Γ(M, V)) (n : Γ(N, V)),
      moduleStalkGerm X x M V hV m = a ∧ moduleStalkGerm X x N V hV n = b := by
  obtain ⟨U₁, h₁, m, rfl⟩ := presheafModuleGerm_exists X x ((toPresheafOfModules X).obj M) a
  obtain ⟨U₂, h₂, n, rfl⟩ := presheafModuleGerm_exists X x ((toPresheafOfModules X).obj N) b
  refine ⟨U₁ ⊓ U₂, ⟨h₁, h₂⟩, M.presheaf.map (homOfLE inf_le_left).op m,
    N.presheaf.map (homOfLE inf_le_right).op n, ?_, ?_⟩
  · exact presheafModuleGerm_res X x ((toPresheafOfModules X).obj M) inf_le_left ⟨h₁, h₂⟩ m
  · exact presheafModuleGerm_res X x ((toPresheafOfModules X).obj N) inf_le_right ⟨h₁, h₂⟩ n

open TensorProduct in
/-- The stalk of a sheafified tensor product of module sheaves is the tensor product of the
stalks. -/
def moduleStalkTensorEquiv (A B : X.Modules) :
    (moduleStalkFunctor X x).obj A ⊗[X.presheaf.stalk x] (moduleStalkFunctor X x).obj B
      ≃ₗ[X.presheaf.stalk x] (moduleStalkFunctor X x).obj (tensorObj A B) :=
  letI := presheafModuleStalkToSheafificationApp_isIso X x
    ((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B)
  presheafModuleStalkTensorEquiv X x ((toPresheafOfModules X).obj A)
      ((toPresheafOfModules X).obj B) ≪≫ₗ
    (asIso (presheafModuleStalkToSheafificationApp X x
      ((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B))).toLinearEquiv

open TensorProduct in
/-- `moduleStalkTensorEquiv` sends a pure tensor of germs to the germ of the pure tensor of
sections. -/
theorem moduleStalkTensorEquiv_germ_tmul_germ (A B : X.Modules) (U : X.Opens)
    (hx : x ∈ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    moduleStalkTensorEquiv X x A B
      (moduleStalkGerm X x A U hx a ⊗ₜ moduleStalkGerm X x B U hx b) =
    moduleStalkGerm X x (tensorObj A B) U hx (tmulSection A B (op U) a b) := by
  have h1 := presheafModuleStalkTensorEquiv_germ_tmul_germ X x ((toPresheafOfModules X).obj A)
    ((toPresheafOfModules X).obj B) U hx a b
  have h2 := presheafModuleStalkFunctor_map_germ X x
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B)) U hx (a ⊗ₜ[Γ(X, U)] b)
  exact (congrArg (fun z => (presheafModuleStalkToSheafificationApp X x
    ((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B)).hom z) h1).trans h2

end
end AlgebraicGeometry.Scheme.Modules
