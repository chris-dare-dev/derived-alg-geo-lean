/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk
import DerivedAlgGeo.Topology.Sheaves.ModuleTensor.StalkTensor

/-!
# Tensor products and stalks of scheme-module sheaves

For a fixed sheaf of modules, taking a stalk commutes with the ordinary
sheafified tensor product, naturally in the second sheaf. The fixed factor
need not be flat or locally free.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.fixedLeftTensorStalkIso` is the natural
  isomorphism from the tensor of stalks to the stalk of the sheaf tensor.

## Main results

The natural isomorphism applies to every scheme, point and fixed module sheaf.
It provides the ordinary tensor/stalk comparison used by the later derived
pullback acyclicity argument.

## Implementation notes

The objectwise comparison passes from bundled module stalks to germ stalks,
uses the presheaf tensor/stalk equivalence, then returns through module
sheafification. Naturality in the right input follows from the two existing
natural comparisons and the pure-tensor naturality theorem.

## References

`PresheafOfModules.stalkTensorEquiv` and
`PresheafOfModules.stalkTensorEquiv_naturality` supply the presheaf comparison;
`AlgebraicGeometry.Scheme.Modules.presheafModuleStalkSheafificationIso` supplies
the sheafification comparison.

## Tags

module sheaf, tensor product, stalk, natural isomorphism
-/

open CategoryTheory MonoidalCategory TopologicalSpace
open AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable (X : Scheme.{u}) (x : X) (L : X.Modules)

private local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModules.monoidalCategory (R := X.presheaf)

private noncomputable def stalkTensorLinearEquiv (M : X.Modules) :
    TensorProduct (X.presheaf.stalk x)
      ↑((moduleStalkFunctor X x).obj L) ↑((moduleStalkFunctor X x).obj M) ≃ₗ[X.presheaf.stalk x]
      ↑((presheafModuleStalkFunctor X x).obj
        ((toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M)) := by
  let P := (toPresheafOfModules X).obj L
  let Q := (toPresheafOfModules X).obj M
  let A := P ⊗ Q
  let e := _root_.PresheafOfModules.stalkTensorEquiv (R := X.presheaf) P Q x
  let eP := _root_.PresheafOfModules.commStalkLinearEquiv X X.presheaf x P
  let eQ := _root_.PresheafOfModules.commStalkLinearEquiv X X.presheaf x Q
  let eA := _root_.PresheafOfModules.commStalkLinearEquiv X X.presheaf x A
  letI : RingHomInvPair (RingHom.id (X.presheaf.stalk x))
      (RingHom.id (X.presheaf.stalk x)) := RingHomInvPair.ids
  exact ((TensorProduct.congr (σ₂₁ := RingHom.id _) eP eQ).trans e).trans eA.symm

private noncomputable def component (M : X.Modules) :
    ((moduleStalkFunctor X x).obj L) ⊗ ((moduleStalkFunctor X x).obj M) ≅
      ((moduleStalkFunctor X x).obj (tensorObj L M)) :=
  (stalkTensorLinearEquiv X x L M).toModuleIso ≪≫
    (presheafModuleStalkSheafificationIso X x).app
      ((toPresheafOfModules X).obj L ⊗ (toPresheafOfModules X).obj M)

private theorem stalkTensorLinearEquiv_natural {M N : X.Modules} (f : M ⟶ N) :
    (tensorLeft (C := ModuleCat.{u} (X.presheaf.stalk x))
      ((moduleStalkFunctor X x).obj L)).map ((moduleStalkFunctor X x).map f) ≫
        (stalkTensorLinearEquiv X x L N).toModuleIso.hom =
      (stalkTensorLinearEquiv X x L M).toModuleIso.hom ≫
        (presheafModuleStalkFunctor X x).map
          (((toPresheafOfModules X).obj L) ◁ ((toPresheafOfModules X).map f)) := by
  ext t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro a b
    let P := (toPresheafOfModules X).obj L
    let Q := (toPresheafOfModules X).obj M
    let Q' := (toPresheafOfModules X).obj N
    let g := (toPresheafOfModules X).map f
    change (stalkTensorLinearEquiv X x L N)
        (a ⊗ₜ ((moduleStalkFunctor X x).map f) b) =
      ((presheafModuleStalkFunctor X x).map (P ◁ g))
        ((stalkTensorLinearEquiv X x L M) (a ⊗ₜ b))
    let eP := _root_.PresheafOfModules.commStalkLinearEquiv X X.presheaf x P
    let eQ := _root_.PresheafOfModules.commStalkLinearEquiv X X.presheaf x Q
    have h := _root_.PresheafOfModules.stalkTensorEquiv_naturality
      (R := X.presheaf) (𝟙 P) g x (eP a ⊗ₜ eQ b)
    change _root_.PresheafOfModules.stalkTensorEquiv (R := X.presheaf) P Q' x
        (eP a ⊗ₜ _root_.PresheafOfModules.stalkMap (R := X.presheaf) g x (eQ b)) =
      _root_.PresheafOfModules.stalkMapAdd (R := X.presheaf) (P ◁ g) x
        (_root_.PresheafOfModules.stalkTensorEquiv (R := X.presheaf) P Q x
          (eP a ⊗ₜ eQ b))
    have hid : _root_.PresheafOfModules.stalkMap (R := X.presheaf) (𝟙 P) x =
        LinearMap.id := by
      ext ξ
      obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf ξ
      change _root_.PresheafOfModules.stalkMapAdd (𝟙 P) x
          (TopCat.Presheaf.germ P.presheaf U x hxU m) = _
      rw [_root_.PresheafOfModules.stalkMapAdd_germ]
      simp
    have hwhisker : (𝟙 P) ⊗ₘ g = P ◁ g := by
      rfl
    simpa only [TensorProduct.map_tmul, hid, LinearMap.id_apply, hwhisker] using h.symm
  · intro a b ha hb
    simp only [map_add, ha, hb]

/-- For a fixed scheme-module sheaf, the stalk of its tensor with another sheaf
is the tensor of the stalks. The comparison is natural in the other sheaf. -/
noncomputable def fixedLeftTensorStalkIso :
    moduleStalkFunctor X x ⋙
        tensorLeft (C := ModuleCat.{u} (X.presheaf.stalk x))
          ((moduleStalkFunctor X x).obj L) ≅
      tensorLeft (C := X.Modules) L ⋙ moduleStalkFunctor X x := by
  refine NatIso.ofComponents (fun M => component X x L M) ?_
  intro M N f
  let P := (toPresheafOfModules X).obj L
  let Q := (toPresheafOfModules X).obj M
  let Q' := (toPresheafOfModules X).obj N
  let g := (toPresheafOfModules X).map f
  let cQ := (presheafModuleStalkSheafificationIso X x).app (P ⊗ Q)
  let cQ' := (presheafModuleStalkSheafificationIso X x).app (P ⊗ Q')
  have hn := stalkTensorLinearEquiv_natural X x L f
  have hc := (presheafModuleStalkSheafificationIso X x).hom.naturality (P ◁ g)
  change (presheafModuleStalkFunctor X x).map (P ◁ g) ≫ cQ'.hom =
      cQ.hom ≫ (moduleStalkFunctor X x).map
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (P ◁ g)) at hc
  change (tensorLeft (C := ModuleCat.{u} (X.presheaf.stalk x))
      ((moduleStalkFunctor X x).obj L)).map ((moduleStalkFunctor X x).map f) ≫
        ((stalkTensorLinearEquiv X x L N).toModuleIso.hom ≫ cQ'.hom) =
      ((stalkTensorLinearEquiv X x L M).toModuleIso.hom ≫ cQ.hom) ≫
        (moduleStalkFunctor X x).map
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (P ◁ g))
  calc
    _ = ((stalkTensorLinearEquiv X x L M).toModuleIso.hom ≫
        (presheafModuleStalkFunctor X x).map (P ◁ g)) ≫ cQ'.hom := by
          rw [← Category.assoc, hn]
    _ = _ := by rw [Category.assoc, hc, ← Category.assoc]

end
end AlgebraicGeometry.Scheme.Modules
