/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Sections
import DerivedAlgGeo.Topology.Sheaves.ModuleTensor.StalkTensor

/-!
# Stalks of the sheafified tensor product

The stalk of a sheafified tensor product of module sheaves at a point is the tensor product of the
stalks over the local ring, and the germ of a pure tensor of sections goes to the tensor of the
germs.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.presheafModuleStalkBridge`: the identification of the module
  structure of `AlgebraicGeometry.Scheme.Modules.presheafModuleStalkFunctor` on a presheaf stalk
  with Mathlib's module structure on `TopCat.Presheaf.stalk`.
* `AlgebraicGeometry.Scheme.Modules.presheafModuleStalkTensorEquiv`: the stalk of a tensor product
  of presheaves of modules as a tensor product of stalks.
* `AlgebraicGeometry.Scheme.Modules.moduleStalkTensorEquiv`: the same for the sheafified tensor
  product of module sheaves.

## Main results

* `AlgebraicGeometry.Scheme.Modules.presheafModuleGerm_exists`,
  `AlgebraicGeometry.Scheme.Modules.presheafModuleGerm_smul`,
  `AlgebraicGeometry.Scheme.Modules.presheafModuleGerm_res` and
  `AlgebraicGeometry.Scheme.Modules.moduleStalkGerm_exists_pair`: every stalk element is a germ,
  germs are linear over the germs of the structure sheaf, germs are unchanged by restriction, and
  two stalk elements are germs of sections over one common neighbourhood.
* `AlgebraicGeometry.Scheme.Modules.presheafModuleStalk_smul_eq`: the two module structures on a
  presheaf stalk agree.
* `AlgebraicGeometry.Scheme.Modules.presheafModuleStalkTensorEquiv_germ_tmul_germ` and
  `AlgebraicGeometry.Scheme.Modules.moduleStalkTensorEquiv_germ_tmul_germ`: the formulas on pure
  tensors of germs.

## Implementation notes

The module stalk functors are bundled through `PresheafOfModules.colimitFunctor`, while the
comparison of a stalk of a tensor product with a tensor product of stalks is proved in
`DerivedAlgGeo/Topology/Sheaves/ModuleTensor/StalkTensor.lean` for Mathlib's module structure on
`TopCat.Presheaf.stalk`. Both structures are characterized by their compatibility with germs, which
is what `AlgebraicGeometry.Scheme.Modules.presheafModuleStalk_smul_eq` records; it is the only place
both are used. The sheaf version composes the presheaf equivalence with the isomorphism on stalks
induced by the sheafification unit.

## References

* The Stacks Project, Tag 01CB (Lemma 17.16.1, the stalk of a tensor product of modules on a ringed
  space), Tag 01CD (Lemma 17.16.4, pullback of a tensor product of modules on ringed spaces) and Tag
  01E8 (Lemma 20.54.2, the projection formula for a finite locally free module). The statements were
  not obtained verbatim: only summaries of those pages were fetched, so these tags give the
  literature context and are not quoted.

## Tags

stalk, germ, tensor product, sheaf of modules, local ring
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

/-- **The module structure of `AlgebraicGeometry.Scheme.Modules.presheafModuleStalkFunctor` on a
presheaf stalk agrees with Mathlib's module structure on `TopCat.Presheaf.stalk`.** Both are
characterized by their compatibility with germs. -/
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
/-- `AlgebraicGeometry.Scheme.Modules.presheafModuleStalkTensorEquiv` computes on a pure tensor of
germs over one neighbourhood. -/
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
/-- `AlgebraicGeometry.Scheme.Modules.moduleStalkTensorEquiv` sends a pure tensor of germs to the
germ of the pure tensor of sections. -/
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
