/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Invertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Stalk
import DerivedAlgGeo.Topology.Category.TopCat.Opens.Final
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Pullback of scheme modules is strong monoidal

For a morphism of schemes `f : X ⟶ Y`, pullback of module sheaves is strong monoidal for the
sheafified tensor product: `f^*(M ⊗ N) ≅ f^*M ⊗ f^*N` and `f^*𝒪_Y ≅ 𝒪_X`, coherently.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal`: pushforward is lax monoidal. Over
  an open `V ⊆ Y`, sections of `f_*M` and `f_*N` are sections over `f⁻¹V`; they are multiplied
  there and the result is sheafified. The unit is the ring map `𝒪_Y ⟶ f_*𝒪_X`.
* `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal`: pullback is strong monoidal.
* `AlgebraicGeometry.Scheme.Modules.pullbackTensorIso` and
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`: its two comparison isomorphisms.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackMonoidal_toOplaxMonoidal`: the oplax part of
  `pullbackMonoidal` is `Adjunction.leftAdjointOplaxMonoidal` of the pullback-pushforward
  adjunction, so `pullback f` carries one monoidal structure.

## Implementation notes

The strong structure upgrades the oplax one with `Functor.Monoidal.ofOplaxMonoidal`. The unit
comparison is Mathlib's `SheafOfModules.pullbackObjUnitToUnit`, an isomorphism because inverse
image of opens is a final functor. The tensor comparison is checked on stalks. At `x ∈ X` the
stalk of `f^*P` is `𝒪_{X,x} ⊗ P_{f x}` (`pullbackStalkIso`), and a germ of the adjunction unit
applied to a section `s` is `1 ⊗ s`. Stalks commute with the tensor product
(`fixedLeftTensorStalkIso`). On these identifications the stalk of the tensor comparison is the
comparison `𝒪_{X,x} ⊗ (M ⊗ N) ≅ (𝒪_{X,x} ⊗ M) ⊗ (𝒪_{X,x} ⊗ N)` of extension of scalars, which
holds for any ring map. No flatness is used.

## References

* Stacks Project, Tag 01CD (pullback of a tensor product) and Tag 01CB (stalks of a tensor
  product).

## Tags

module sheaf, pullback, pushforward, tensor product, monoidal functor, stalk
-/

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal TensorProduct
  Opposite

set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

noncomputable section

private local instance {X : Scheme.{u}} : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

/-- Presheaf pushforward along the ring map of `f`. -/
private abbrev pushforwardPresheaf : X.PresheafOfModules ⥤ Y.PresheafOfModules :=
  PresheafOfModules.pushforward.{u} f.toRingCatSheafHom.hom

set_option maxHeartbeats 800000 in
/-- Section-level multiplication makes presheaf pushforward lax monoidal. -/
@[instance_reducible]
private def pushforwardPresheafLaxMonoidal : (pushforwardPresheaf f).LaxMonoidal where
  ε := (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val
  μ P Q :=
    { app V := μ (ModuleCat.restrictScalars (f.app V.unop).hom) (P.obj _) (Q.obj _)
      naturality {V W} i := by
        exact ModuleCat.MonoidalCategory.tensor_ext (R := Y.presheaf.obj V) (fun p q ↦ by
          rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
          erw [ModuleCat.restrictScalars_μ_tmul]
          erw [ModuleCat.restrictScalars_μ_tmul]
          rfl) }
  μ_natural_left {P P'} g Q := by
    ext1 V
    exact μ_natural_left (ModuleCat.restrictScalars (f.app V.unop).hom) (g.app _) (Q.obj _)
  μ_natural_right {Q Q'} P g := by
    ext1 V
    exact μ_natural_right (ModuleCat.restrictScalars (f.app V.unop).hom) (P.obj _) (g.app _)
  associativity P Q R := by
    ext1 V
    exact Functor.LaxMonoidal.associativity (ModuleCat.restrictScalars (f.app V.unop).hom)
      (P.obj _) (Q.obj _) (R.obj _)
  left_unitality P := by
    ext1 V
    have hε : (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val.app V =
        ε (ModuleCat.restrictScalars (f.app V.unop).hom) := by
      ext
      erw [ModuleCat.restrictScalars_η]
      rfl
    have h := left_unitality (ModuleCat.restrictScalars (f.app V.unop).hom) (P.obj _)
    rw [← hε] at h
    exact h
  right_unitality P := by
    ext1 V
    have hε : (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val.app V =
        ε (ModuleCat.restrictScalars (f.app V.unop).hom) := by
      ext
      erw [ModuleCat.restrictScalars_η]
      rfl
    have h := right_unitality (ModuleCat.restrictScalars (f.app V.unop).hom) (P.obj _)
    rw [← hε] at h
    exact h

attribute [local instance] pushforwardPresheafLaxMonoidal

/-- Module sheafification on a scheme. -/
private abbrev associatedSheaf (X : Scheme.{u}) : X.PresheafOfModules ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The module sheafification adjunction on a scheme. -/
private abbrev sheafificationAdj (X : Scheme.{u}) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)

/-- Multiply sections of the pushforwards, then sheafify. -/
private def pushforwardμ (M N : X.Modules) :
    (pushforward f).obj M ⊗ (pushforward f).obj N ⟶ (pushforward f).obj (M ⊗ N) :=
  ((sheafificationAdj Y).homEquiv _ _).symm
    (μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj M) ((toPresheafOfModules X).obj N) ≫
      (pushforwardPresheaf f).map ((sheafificationAdj X).unit.app _))

private lemma unit_comp_pushforwardμ (M N : X.Modules) :
    (sheafificationAdj Y).unit.app _ ≫ (toPresheafOfModules Y).map (pushforwardμ f M N) =
      μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj M) ((toPresheafOfModules X).obj N) ≫
        (pushforwardPresheaf f).map ((sheafificationAdj X).unit.app _) := by
  change ((sheafificationAdj Y).homEquiv _ _) (pushforwardμ f M N) = _
  exact Equiv.apply_symm_apply _ _

private lemma associatedSheaf_hom_ext {P : Y.PresheafOfModules} {G : Y.Modules}
    {g h : (associatedSheaf Y).obj P ⟶ G}
    (H : (sheafificationAdj Y).unit.app P ≫ (toPresheafOfModules Y).map g =
      (sheafificationAdj Y).unit.app P ≫ (toPresheafOfModules Y).map h) : g = h := by
  apply ((sheafificationAdj Y).homEquiv _ _).injective
  exact H

private lemma unit_comp_tensorHom {Z : Scheme.{u}} {A A' B B' : Z.Modules} (a : A ⟶ A')
    (b : B ⟶ B') :
    (sheafificationAdj Z).unit.app _ ≫ (toPresheafOfModules Z).map (a ⊗ₘ b) =
      ((toPresheafOfModules Z).map a ⊗ₘ (toPresheafOfModules Z).map b) ≫
        (sheafificationAdj Z).unit.app _ :=
  ((sheafificationAdj Z).unit.naturality _).symm

private lemma unit_comp_whiskerRight {Z : Scheme.{u}} {A A' : Z.Modules} (a : A ⟶ A')
    (B : Z.Modules) :
    (sheafificationAdj Z).unit.app _ ≫ (toPresheafOfModules Z).map (a ▷ B) =
      ((toPresheafOfModules Z).map a ▷ (toPresheafOfModules Z).obj B) ≫
        (sheafificationAdj Z).unit.app _ := by
  have h := unit_comp_tensorHom a (𝟙 B)
  rw [(toPresheafOfModules Z).map_id, MonoidalCategory.tensorHom_id] at h
  exact h

private lemma unit_comp_whiskerLeft {Z : Scheme.{u}} (A : Z.Modules) {B B' : Z.Modules}
    (b : B ⟶ B') :
    (sheafificationAdj Z).unit.app _ ≫ (toPresheafOfModules Z).map (A ◁ b) =
      ((toPresheafOfModules Z).obj A ◁ (toPresheafOfModules Z).map b) ≫
        (sheafificationAdj Z).unit.app _ := by
  have h := unit_comp_tensorHom (𝟙 A) b
  rw [(toPresheafOfModules Z).map_id, MonoidalCategory.id_tensorHom] at h
  exact h

private lemma toPresheaf_map_pushforward_map {M M' : X.Modules} (k : M ⟶ M') :
    (toPresheafOfModules Y).map ((pushforward f).map k) =
      (pushforwardPresheaf f).map ((toPresheafOfModules X).map k) := rfl

private lemma pushforwardμ_natural_left {M M' : X.Modules} (g : M ⟶ M') (N : X.Modules) :
    (pushforward f).map g ▷ (pushforward f).obj N ≫ pushforwardμ f M' N =
      pushforwardμ f M N ≫ (pushforward f).map (g ▷ N) := by
  apply associatedSheaf_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    unit_comp_whiskerRight, unit_comp_pushforwardμ, Category.assoc, unit_comp_pushforwardμ,
    Category.assoc]
  have h := μ_natural_left (pushforwardPresheaf f) ((toPresheafOfModules X).map g)
      ((toPresheafOfModules X).obj N)
  have h2 := unit_comp_whiskerRight g N
  rw [toPresheaf_map_pushforward_map f (g ▷ N), ← Functor.map_comp, h2, Functor.map_comp,
    ← reassoc_of% h]
  rfl

private lemma pushforwardμ_natural_right (M : X.Modules) {N N' : X.Modules} (g : N ⟶ N') :
    (pushforward f).obj M ◁ (pushforward f).map g ≫ pushforwardμ f M N' =
      pushforwardμ f M N ≫ (pushforward f).map (M ◁ g) := by
  apply associatedSheaf_hom_ext
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc,
    unit_comp_whiskerLeft, unit_comp_pushforwardμ, Category.assoc, unit_comp_pushforwardμ,
    Category.assoc]
  have h := μ_natural_right (pushforwardPresheaf f) ((toPresheafOfModules X).obj M)
      ((toPresheafOfModules X).map g)
  have h2 := unit_comp_whiskerLeft M g
  rw [toPresheaf_map_pushforward_map f (M ◁ g), ← Functor.map_comp, h2, Functor.map_comp,
    ← reassoc_of% h]
  rfl

/-- The associator of scheme modules, seen through the sheafification unit. -/
private lemma unit_comp_associator {Z : Scheme.{u}} (M N K : Z.Modules) :
    ((sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj M ⊗
        (toPresheafOfModules Z).obj N) ▷
        (toPresheafOfModules Z).obj K) ≫
      (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj (M ⊗ N) ⊗
          (toPresheafOfModules Z).obj K) ≫
      (toPresheafOfModules Z).map (α_ M N K).hom =
    (α_ ((toPresheafOfModules Z).obj M) ((toPresheafOfModules Z).obj N)
        ((toPresheafOfModules Z).obj K)).hom ≫
      ((toPresheafOfModules Z).obj M ◁
        (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj N ⊗
            (toPresheafOfModules Z).obj K)) ≫
      (sheafificationAdj Z).unit.app
        ((toPresheafOfModules Z).obj M ⊗ (toPresheafOfModules Z).obj (N ⊗ K)) := by
  have h := tensorSheafificationComparisonRight_comp_tensorAssocIso M N K
  have h' := congrArg
    (fun k => (sheafificationAdj Z).unit.app _ ≫ (toPresheafOfModules Z).map k) h
  simp only [Functor.map_comp] at h'
  have hR : (sheafificationAdj Z).unit.app _ ≫ (toPresheafOfModules Z).map
      (tensorSheafificationComparisonRight
        ((toPresheafOfModules Z).obj M ⊗ (toPresheafOfModules Z).obj N) K) =
      ((sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj M ⊗
          (toPresheafOfModules Z).obj N) ▷
        (toPresheafOfModules Z).obj K) ≫ (sheafificationAdj Z).unit.app _ :=
    ((sheafificationAdj Z).unit.naturality _).symm
  have hL : (sheafificationAdj Z).unit.app _ ≫ (toPresheafOfModules Z).map
      (tensorSheafificationComparisonLeft M
        ((toPresheafOfModules Z).obj N ⊗ (toPresheafOfModules Z).obj K)) =
      ((toPresheafOfModules Z).obj M ◁
        (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj N ⊗
            (toPresheafOfModules Z).obj K)) ≫
      (sheafificationAdj Z).unit.app _ :=
    ((sheafificationAdj Z).unit.naturality _).symm
  have hA : (sheafificationAdj Z).unit.app _ ≫
      (toPresheafOfModules Z).map ((associatedSheaf Z).map
      (α_ ((toPresheafOfModules Z).obj M) ((toPresheafOfModules Z).obj N)
        ((toPresheafOfModules Z).obj K)).hom) =
      (α_ ((toPresheafOfModules Z).obj M) ((toPresheafOfModules Z).obj N)
        ((toPresheafOfModules Z).obj K)).hom ≫ (sheafificationAdj Z).unit.app _ :=
    ((sheafificationAdj Z).unit.naturality _).symm
  rw [reassoc_of% hR, reassoc_of% hA, hL] at h'
  exact h'

private lemma pushforwardμ_associativity (M N K : X.Modules) :
    pushforwardμ f M N ▷ (pushforward f).obj K ≫ pushforwardμ f (M ⊗ N) K ≫
        (pushforward f).map (α_ M N K).hom =
      (α_ ((pushforward f).obj M) ((pushforward f).obj N) ((pushforward f).obj K)).hom ≫
        (pushforward f).obj M ◁ pushforwardμ f N K ≫ pushforwardμ f M (N ⊗ K) := by
  have hα := tensorSheafificationComparisonRight_comp_tensorAssocIso ((pushforward f).obj M)
      ((pushforward f).obj N) ((pushforward f).obj K)
  rw [← cancel_epi (tensorSheafificationComparisonRight
    ((toPresheafOfModules Y).obj ((pushforward f).obj M) ⊗
      (toPresheafOfModules Y).obj ((pushforward f).obj N)) ((pushforward f).obj K))]
  apply associatedSheaf_hom_ext
  have hcR : (sheafificationAdj Y).unit.app _ ≫ (toPresheafOfModules Y).map
      (tensorSheafificationComparisonRight
        ((toPresheafOfModules Y).obj ((pushforward f).obj M) ⊗
          (toPresheafOfModules Y).obj ((pushforward f).obj N)) ((pushforward f).obj K)) =
      ((sheafificationAdj Y).unit.app ((toPresheafOfModules Y).obj ((pushforward f).obj M) ⊗
          (toPresheafOfModules Y).obj ((pushforward f).obj N)) ▷
          (toPresheafOfModules Y).obj ((pushforward f).obj K)) ≫
        (sheafificationAdj Y).unit.app ((toPresheafOfModules Y).obj
          ((pushforward f).obj M ⊗ (pushforward f).obj N) ⊗
          (toPresheafOfModules Y).obj ((pushforward f).obj K)) :=
    ((sheafificationAdj Y).unit.naturality _).symm
  have hnatL : (pushforwardPresheaf f).map ((sheafificationAdj X).unit.app
      ((toPresheafOfModules X).obj M ⊗
        (toPresheafOfModules X).obj N)) ▷ (toPresheafOfModules Y).obj ((pushforward f).obj K) ≫
      μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj (M ⊗ N))
          ((toPresheafOfModules X).obj K) =
      μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)
          ((toPresheafOfModules X).obj K) ≫
        (pushforwardPresheaf f).map ((sheafificationAdj X).unit.app
          ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N) ▷
            (toPresheafOfModules X).obj K) :=
    μ_natural_left (pushforwardPresheaf f) _ _
  have hassoc : μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj M)
      ((toPresheafOfModules X).obj N) ▷
        (toPresheafOfModules Y).obj ((pushforward f).obj K) ≫
      μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)
          ((toPresheafOfModules X).obj K) ≫
      (pushforwardPresheaf f).map (α_ ((toPresheafOfModules X).obj M)
          ((toPresheafOfModules X).obj N)
          ((toPresheafOfModules X).obj K)).hom =
      (α_ ((toPresheafOfModules Y).obj ((pushforward f).obj M))
          ((toPresheafOfModules Y).obj ((pushforward f).obj N))
          ((toPresheafOfModules Y).obj ((pushforward f).obj K))).hom ≫
        ((toPresheafOfModules Y).obj ((pushforward f).obj M) ◁
          μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj N)
              ((toPresheafOfModules X).obj K)) ≫
        μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj M)
          ((toPresheafOfModules X).obj N ⊗ (toPresheafOfModules X).obj K) :=
    Functor.LaxMonoidal.associativity (pushforwardPresheaf f) _ _ _
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, reassoc_of% hcR,
    reassoc_of% (unit_comp_whiskerRight (pushforwardμ f M N) ((pushforward f).obj K)),
    reassoc_of% (unit_comp_pushforwardμ f (M ⊗ N) K), ← comp_whiskerRight_assoc,
    unit_comp_pushforwardμ, comp_whiskerRight_assoc, reassoc_of% hnatL,
    toPresheaf_map_pushforward_map f (α_ M N K).hom, ← Functor.map_comp, ← Functor.map_comp,
    unit_comp_associator, Functor.map_comp, Functor.map_comp, reassoc_of% hassoc]
  have hα' : tensorSheafificationComparisonRight
        ((toPresheafOfModules Y).obj ((pushforward f).obj M) ⊗
          (toPresheafOfModules Y).obj ((pushforward f).obj N)) ((pushforward f).obj K) ≫
      (α_ ((pushforward f).obj M) ((pushforward f).obj N) ((pushforward f).obj K)).hom =
      (associatedSheaf Y).map (α_ ((toPresheafOfModules Y).obj ((pushforward f).obj M))
          ((toPresheafOfModules Y).obj ((pushforward f).obj N))
          ((toPresheafOfModules Y).obj ((pushforward f).obj K))).hom ≫
        tensorSheafificationComparisonLeft ((pushforward f).obj M)
          ((toPresheafOfModules Y).obj ((pushforward f).obj N) ⊗
            (toPresheafOfModules Y).obj ((pushforward f).obj K)) := hα
  have hA : (sheafificationAdj Y).unit.app _ ≫
      (toPresheafOfModules Y).map ((associatedSheaf Y).map
      (α_ ((toPresheafOfModules Y).obj ((pushforward f).obj M))
          ((toPresheafOfModules Y).obj ((pushforward f).obj N))
          ((toPresheafOfModules Y).obj ((pushforward f).obj K))).hom) =
      (α_ ((toPresheafOfModules Y).obj ((pushforward f).obj M))
          ((toPresheafOfModules Y).obj ((pushforward f).obj N))
          ((toPresheafOfModules Y).obj ((pushforward f).obj K))).hom ≫
        (sheafificationAdj Y).unit.app ((toPresheafOfModules Y).obj ((pushforward f).obj M) ⊗
          ((toPresheafOfModules Y).obj ((pushforward f).obj N) ⊗
            (toPresheafOfModules Y).obj ((pushforward f).obj K))) :=
    ((sheafificationAdj Y).unit.naturality _).symm
  have hcL : (sheafificationAdj Y).unit.app ((toPresheafOfModules Y).obj ((pushforward f).obj M) ⊗
          ((toPresheafOfModules Y).obj ((pushforward f).obj N) ⊗
            (toPresheafOfModules Y).obj ((pushforward f).obj K))) ≫
      (toPresheafOfModules Y).map (tensorSheafificationComparisonLeft ((pushforward f).obj M)
          ((toPresheafOfModules Y).obj ((pushforward f).obj N) ⊗
            (toPresheafOfModules Y).obj ((pushforward f).obj K))) =
      ((toPresheafOfModules Y).obj ((pushforward f).obj M) ◁
        (sheafificationAdj Y).unit.app ((toPresheafOfModules Y).obj ((pushforward f).obj N) ⊗
            (toPresheafOfModules Y).obj ((pushforward f).obj K))) ≫
        (sheafificationAdj Y).unit.app ((toPresheafOfModules Y).obj ((pushforward f).obj M) ⊗
          (toPresheafOfModules Y).obj ((pushforward f).obj N ⊗ (pushforward f).obj K)) :=
    ((sheafificationAdj Y).unit.naturality _).symm
  have hnatR : (toPresheafOfModules Y).obj ((pushforward f).obj M) ◁
        (pushforwardPresheaf f).map ((sheafificationAdj X).unit.app
          ((toPresheafOfModules X).obj N ⊗ (toPresheafOfModules X).obj K)) ≫
      μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj M)
          ((toPresheafOfModules X).obj (N ⊗ K)) =
      μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj M)
          ((toPresheafOfModules X).obj N ⊗ (toPresheafOfModules X).obj K) ≫
        (pushforwardPresheaf f).map ((toPresheafOfModules X).obj M ◁
          (sheafificationAdj X).unit.app
            ((toPresheafOfModules X).obj N ⊗ (toPresheafOfModules X).obj K)) :=
    μ_natural_right (pushforwardPresheaf f) _ _
  rw [reassoc_of% hα', Functor.map_comp, Functor.map_comp, Functor.map_comp, reassoc_of% hA,
    reassoc_of% hcL,
    reassoc_of% (unit_comp_whiskerLeft ((pushforward f).obj M) (pushforwardμ f N K)),
    unit_comp_pushforwardμ f M (N ⊗ K), ← MonoidalCategory.whiskerLeft_comp_assoc,
    unit_comp_pushforwardμ f N K, MonoidalCategory.whiskerLeft_comp_assoc, reassoc_of% hnatR]

private lemma unit_comp_leftUnitor {Z : Scheme.{u}} (M : Z.Modules) :
    (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj (𝟙_ Z.Modules) ⊗
        (toPresheafOfModules Z).obj M) ≫ (toPresheafOfModules Z).map (λ_ M).hom =
      (λ_ ((toPresheafOfModules Z).obj M)).hom := by
  have h0 : (λ_ M).hom = (associatedSheaf Z).map (λ_ ((toPresheafOfModules Z).obj M)).hom ≫
      (sheafificationAdj Z).counit.app M := rfl
  have h1 : (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj (𝟙_ Z.Modules) ⊗
        (toPresheafOfModules Z).obj M) ≫
      (toPresheafOfModules Z).map
        ((associatedSheaf Z).map (λ_ ((toPresheafOfModules Z).obj M)).hom) =
      (λ_ ((toPresheafOfModules Z).obj M)).hom ≫
        (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj M) :=
    ((sheafificationAdj Z).unit.naturality (λ_ ((toPresheafOfModules Z).obj M)).hom).symm
  have h2 : (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj M) ≫
      (toPresheafOfModules Z).map ((sheafificationAdj Z).counit.app M) = 𝟙 _ :=
    (sheafificationAdj Z).right_triangle_components M
  rw [h0, Functor.map_comp, reassoc_of% h1, h2]
  exact Category.comp_id _

private lemma unit_comp_rightUnitor {Z : Scheme.{u}} (M : Z.Modules) :
    (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj M ⊗
        (toPresheafOfModules Z).obj (𝟙_ Z.Modules)) ≫ (toPresheafOfModules Z).map (ρ_ M).hom =
      (ρ_ ((toPresheafOfModules Z).obj M)).hom := by
  have h0 : (ρ_ M).hom = (associatedSheaf Z).map (ρ_ ((toPresheafOfModules Z).obj M)).hom ≫
      (sheafificationAdj Z).counit.app M := rfl
  have h1 : (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj M ⊗
        (toPresheafOfModules Z).obj (𝟙_ Z.Modules)) ≫
      (toPresheafOfModules Z).map
        ((associatedSheaf Z).map (ρ_ ((toPresheafOfModules Z).obj M)).hom) =
      (ρ_ ((toPresheafOfModules Z).obj M)).hom ≫
        (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj M) :=
    ((sheafificationAdj Z).unit.naturality (ρ_ ((toPresheafOfModules Z).obj M)).hom).symm
  have h2 : (sheafificationAdj Z).unit.app ((toPresheafOfModules Z).obj M) ≫
      (toPresheafOfModules Z).map ((sheafificationAdj Z).counit.app M) = 𝟙 _ :=
    (sheafificationAdj Z).right_triangle_components M
  rw [h0, Functor.map_comp, reassoc_of% h1, h2]
  exact Category.comp_id _

/-- The ring map `𝒪_Y ⟶ f_*𝒪_X`, as a map of module sheaves. -/
private abbrev pushforwardε : 𝟙_ Y.Modules ⟶ (pushforward f).obj (𝟙_ X.Modules) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

private lemma pushforwardμ_left_unitality (M : X.Modules) :
    (λ_ ((pushforward f).obj M)).hom =
      pushforwardε f ▷ (pushforward f).obj M ≫
        pushforwardμ f (𝟙_ X.Modules) M ≫ (pushforward f).map (λ_ M).hom := by
  apply associatedSheaf_hom_ext
  rw [unit_comp_leftUnitor, Functor.map_comp, Functor.map_comp,
    reassoc_of% (unit_comp_whiskerRight (pushforwardε f) ((pushforward f).obj M))]
  have h5 : (sheafificationAdj Y).unit.app
        ((toPresheafOfModules Y).obj ((pushforward f).obj (𝟙_ X.Modules)) ⊗
          (toPresheafOfModules Y).obj ((pushforward f).obj M)) ≫
      (toPresheafOfModules Y).map (pushforwardμ f (𝟙_ X.Modules) M) ≫
        (toPresheafOfModules Y).map ((pushforward f).map (λ_ M).hom) =
      μ (pushforwardPresheaf f) (𝟙_ X.PresheafOfModules) ((toPresheafOfModules X).obj M) ≫
        (pushforwardPresheaf f).map (λ_ ((toPresheafOfModules X).obj M)).hom := by
    rw [reassoc_of% (unit_comp_pushforwardμ f (𝟙_ X.Modules) M), toPresheaf_map_pushforward_map,
      ← Functor.map_comp, unit_comp_leftUnitor]
    rfl
  exact (left_unitality (pushforwardPresheaf f) _).trans (congrArg (fun k => _ ≫ k) h5.symm)

private lemma pushforwardμ_right_unitality (M : X.Modules) :
    (ρ_ ((pushforward f).obj M)).hom =
      (pushforward f).obj M ◁ pushforwardε f ≫
        pushforwardμ f M (𝟙_ X.Modules) ≫ (pushforward f).map (ρ_ M).hom := by
  apply associatedSheaf_hom_ext
  rw [unit_comp_rightUnitor, Functor.map_comp, Functor.map_comp,
    reassoc_of% (unit_comp_whiskerLeft ((pushforward f).obj M) (pushforwardε f))]
  have h5 : (sheafificationAdj Y).unit.app ((toPresheafOfModules Y).obj ((pushforward f).obj M) ⊗
        (toPresheafOfModules Y).obj ((pushforward f).obj (𝟙_ X.Modules))) ≫
      (toPresheafOfModules Y).map (pushforwardμ f M (𝟙_ X.Modules)) ≫
        (toPresheafOfModules Y).map ((pushforward f).map (ρ_ M).hom) =
      μ (pushforwardPresheaf f) ((toPresheafOfModules X).obj M) (𝟙_ X.PresheafOfModules) ≫
        (pushforwardPresheaf f).map (ρ_ ((toPresheafOfModules X).obj M)).hom := by
    rw [reassoc_of% (unit_comp_pushforwardμ f M (𝟙_ X.Modules)), toPresheaf_map_pushforward_map,
      ← Functor.map_comp, unit_comp_rightUnitor]
    rfl
  exact (right_unitality (pushforwardPresheaf f) _).trans (congrArg (fun k => _ ≫ k) h5.symm)

/-- Pushforward of module sheaves is lax monoidal: sections over `f⁻¹V` multiply, and the
result is sheafified. The unit is the ring map `𝒪_Y ⟶ f_*𝒪_X`. -/
instance pushforwardLaxMonoidal : (pushforward f).LaxMonoidal where
  ε := pushforwardε f
  μ := pushforwardμ f
  μ_natural_left := pushforwardμ_natural_left f
  μ_natural_right M g := pushforwardμ_natural_right f M g
  associativity := pushforwardμ_associativity f
  left_unitality := pushforwardμ_left_unitality f
  right_unitality := pushforwardμ_right_unitality f

/-- The tensor product of two morphisms on a pure tensor of sections. -/
private lemma tensorHom_app_tmulSection {Z : Scheme.{u}} {A A' B B' : Z.Modules} (g : A ⟶ A')
    (h : B ⟶ B') (U : Z.Opens) (a : Γ(A, U)) (b : Γ(B, U)) :
    (g ⊗ₘ h).app U (tmulSection A B (op U) a b) =
      tmulSection A' B' (op U) (g.app U a) (h.app U b) :=
  congrArg (fun k => (k.app (op U)).hom (a ⊗ₜ b)) (unit_comp_tensorHom g h)

/-- The tensorator of pushforward on a pure tensor of sections. -/
private lemma pushforwardμ_app_tmulSection (M N : X.Modules) (V : Y.Opens)
    (a : Γ(M, f ⁻¹ᵁ V)) (b : Γ(N, f ⁻¹ᵁ V)) :
    (pushforwardμ f M N).app V
        (tmulSection ((pushforward f).obj M) ((pushforward f).obj N) (op V) a b) =
      tmulSection M N (op (f ⁻¹ᵁ V)) a b := by
  have h := congrArg (fun k => (k.app (op V)).hom (a ⊗ₜ b)) (unit_comp_pushforwardμ f M N)
  refine h.trans ?_
  change ((sheafificationAdj X).unit.app
      ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)).app (op (f ⁻¹ᵁ V))
    ((μ (ModuleCat.restrictScalars (f.app V).hom) _ _).hom (a ⊗ₜ b)) = _
  exact congrArg (((sheafificationAdj X).unit.app
      ((toPresheafOfModules X).obj M ⊗ (toPresheafOfModules X).obj N)).app
        (op (f ⁻¹ᵁ V))).hom
    (ModuleCat.restrictScalars_μ_tmul (f.app V).hom _ _ a b)

/-- The oplax tensorator of pullback, on the unit applied to a pure tensor of sections. -/
private lemma δ_app_unit_tmulSection (M N : Y.Modules) (V : Y.Opens) (m : Γ(M, V))
    (n : Γ(N, V)) :
    letI := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
    (δ (pullback f) M N).app (f ⁻¹ᵁ V)
        (((pullbackPushforwardAdjunction f).unit.app (M ⊗ N)).app V
          (tmulSection M N (op V) m n)) =
      tmulSection ((pullback f).obj M) ((pullback f).obj N) (op (f ⁻¹ᵁ V))
        (((pullbackPushforwardAdjunction f).unit.app M).app V m)
        (((pullbackPushforwardAdjunction f).unit.app N).app V n) := by
  let := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
  have h := congrArg (fun k => k.app V (tmulSection M N (op V) m n))
    (Adjunction.unit_app_tensor_comp_map_δ (pullbackPushforwardAdjunction f) M N)
  refine h.trans ?_
  change (pushforwardμ f _ _).app V (((pullbackPushforwardAdjunction f).unit.app M ⊗ₘ
    (pullbackPushforwardAdjunction f).unit.app N).app V (tmulSection M N (op V) m n)) = _
  exact (congrArg ((pushforwardμ f ((pullback f).obj M) ((pullback f).obj N)).app V)
    (tensorHom_app_tmulSection _ _ V m n)).trans (pushforwardμ_app_tmulSection f _ _ V _ _)

/-- Stalks commute with the tensor product on pure tensors of germs. -/
private lemma fixedLeftTensorStalkIso_hom_app_germ_tmul {Z : Scheme.{u}} (z : Z) (A B : Z.Modules)
    (U : Z.Opens) (hz : z ∈ U) (a : Γ(A, U)) (b : Γ(B, U)) :
    (fixedLeftTensorStalkIso Z z A).hom.app B
        ((TopCat.Presheaf.germ A.presheaf U z hz a : (moduleStalkFunctor Z z).obj A) ⊗ₜ
          (TopCat.Presheaf.germ B.presheaf U z hz b : (moduleStalkFunctor Z z).obj B)) =
      TopCat.Presheaf.germ (tensorObj A B).presheaf U z hz (tmulSection A B (op U) a b) := by
  change (presheafModuleStalkSheafificationIso Z z).hom.app
      ((toPresheafOfModules Z).obj A ⊗ (toPresheafOfModules Z).obj B)
    (_root_.PresheafOfModules.stalkTensorEquiv (R := Z.presheaf) ((toPresheafOfModules Z).obj A)
      ((toPresheafOfModules Z).obj B) z
      (TopCat.Presheaf.germ A.presheaf U z hz a ⊗ₜ
        TopCat.Presheaf.germ B.presheaf U z hz b)) = _
  refine (congrArg ((presheafModuleStalkSheafificationIso Z z).hom.app
      ((toPresheafOfModules Z).obj A ⊗ (toPresheafOfModules Z).obj B)).hom
    ((_root_.PresheafOfModules.stalkTensorEquiv_germ_tmul_germ (R := Z.presheaf)
      ((toPresheafOfModules Z).obj A) ((toPresheafOfModules Z).obj B) z U U hz hz a b).trans
      (_root_.PresheafOfModules.germTmul_self (R := Z.presheaf)
        ((toPresheafOfModules Z).obj A) ((toPresheafOfModules Z).obj B) z hz a b))).trans ?_
  exact presheafModuleStalkFunctor_map_germ z _ U hz _

/-- The inverse of `pullbackStalkIso` sends `1 ⊗ s` to the germ of the unit applied to `s`. -/
private lemma pullbackStalkIso_inv_app_one_tmul (x : X) (P : Y.Modules) (V : Y.Opens)
    (hV : f x ∈ V) (s : Γ(P, V)) :
    (pullbackStalkIso f x).inv.app P
        ((ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
          ((moduleStalkFunctor Y (f x)).obj P) (TopCat.Presheaf.germ P.presheaf V (f x) hV s)) =
      TopCat.Presheaf.germ ((pullback f).obj P).presheaf (f ⁻¹ᵁ V) x hV
        (((pullbackPushforwardAdjunction f).unit.app P).app V s) := by
  rw [← pullbackStalkIso_hom_app_germ_unit]
  exact ConcreteCategory.congr_hom ((pullbackStalkIso f x).hom_inv_id_app P) _

/-- The oplax tensorator of pullback is an isomorphism on every stalk. -/
private lemma isIso_stalk_δ (M N : Y.Modules) (x : X) :
    letI := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
    IsIso ((moduleStalkFunctor X x).map (δ (pullback f) M N)) := by
  let := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
  let E := ModuleCat.extendScalars (f.stalkMap x).hom
  have key : E.map ((fixedLeftTensorStalkIso Y (f x) M).hom.app N) ≫
      (pullbackStalkIso f x).inv.app (M ⊗ N) ≫
        (moduleStalkFunctor X x).map (δ (pullback f) M N) =
      δ E ((moduleStalkFunctor Y (f x)).obj M) ((moduleStalkFunctor Y (f x)).obj N) ≫
        ((pullbackStalkIso f x).inv.app M ⊗ₘ (pullbackStalkIso f x).inv.app N) ≫
        (fixedLeftTensorStalkIso X x ((pullback f).obj M)).hom.app ((pullback f).obj N) := by
    apply ((ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).homEquiv _ _).injective
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    obtain ⟨V₁, hV₁, s₁, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
    obtain ⟨V, hVV₁, hV, t, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq N.presheaf n hV₁
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVV₁) (f x) hV s₁]
    generalize M.presheaf.map (homOfLE hVV₁).op s₁ = s
    let η := (pullbackPushforwardAdjunction f).unit
    have hL : (E.map ((fixedLeftTensorStalkIso Y (f x) M).hom.app N) ≫
        (pullbackStalkIso f x).inv.app (M ⊗ N) ≫
          (moduleStalkFunctor X x).map (δ (pullback f) M N))
        ((1 : X.presheaf.stalk x) ⊗ₜ
          ((TopCat.Presheaf.germ M.presheaf V (f x) hV s :
              (moduleStalkFunctor Y (f x)).obj M) ⊗ₜ
            (TopCat.Presheaf.germ N.presheaf V (f x) hV t :
              (moduleStalkFunctor Y (f x)).obj N))) =
        TopCat.Presheaf.germ (tensorObj ((pullback f).obj M) ((pullback f).obj N)).presheaf
          (f ⁻¹ᵁ V) x hV (tmulSection ((pullback f).obj M) ((pullback f).obj N)
            (op (f ⁻¹ᵁ V)) ((η.app M).app V s) ((η.app N).app V t)) := by
      have e1 := fixedLeftTensorStalkIso_hom_app_germ_tmul (f x) M N V hV s t
      have e2 := pullbackStalkIso_inv_app_one_tmul f x (M ⊗ N) V hV (tmulSection M N (op V) s t)
      have e3 := moduleStalkFunctor_map_germ x (δ (pullback f) M N) (f ⁻¹ᵁ V) hV
        ((η.app (M ⊗ N)).app V (tmulSection M N (op V) s t))
      have e4 := δ_app_unit_tmulSection f M N V s t
      calc _ = (moduleStalkFunctor X x).map (δ (pullback f) M N)
            ((pullbackStalkIso f x).inv.app (M ⊗ N)
              ((ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
                ((moduleStalkFunctor Y (f x)).obj (M ⊗ N))
                ((fixedLeftTensorStalkIso Y (f x) M).hom.app N
                  ((TopCat.Presheaf.germ M.presheaf V (f x) hV s :
                    (moduleStalkFunctor Y (f x)).obj M) ⊗ₜ
                  (TopCat.Presheaf.germ N.presheaf V (f x) hV t :
                    (moduleStalkFunctor Y (f x)).obj N))))) := rfl
        _ = _ := congrArg (fun z => (moduleStalkFunctor X x).map (δ (pullback f) M N)
            ((pullbackStalkIso f x).inv.app (M ⊗ N)
              ((ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
                ((moduleStalkFunctor Y (f x)).obj (M ⊗ N)) z))) e1
        _ = _ := congrArg ((moduleStalkFunctor X x).map (δ (pullback f) M N)).hom e2
        _ = _ := e3
        _ = _ := congrArg _ e4
    have hR : (δ E ((moduleStalkFunctor Y (f x)).obj M) ((moduleStalkFunctor Y (f x)).obj N) ≫
        ((pullbackStalkIso f x).inv.app M ⊗ₘ (pullbackStalkIso f x).inv.app N) ≫
        (fixedLeftTensorStalkIso X x ((pullback f).obj M)).hom.app ((pullback f).obj N))
        ((1 : X.presheaf.stalk x) ⊗ₜ
          ((TopCat.Presheaf.germ M.presheaf V (f x) hV s :
              (moduleStalkFunctor Y (f x)).obj M) ⊗ₜ
            (TopCat.Presheaf.germ N.presheaf V (f x) hV t :
              (moduleStalkFunctor Y (f x)).obj N))) =
        TopCat.Presheaf.germ (tensorObj ((pullback f).obj M) ((pullback f).obj N)).presheaf
          (f ⁻¹ᵁ V) x hV (tmulSection ((pullback f).obj M) ((pullback f).obj N)
            (op (f ⁻¹ᵁ V)) ((η.app M).app V s) ((η.app N).app V t)) := by
      have e1 := pullbackStalkIso_inv_app_one_tmul f x M V hV s
      have e2 := pullbackStalkIso_inv_app_one_tmul f x N V hV t
      calc _ = (fixedLeftTensorStalkIso X x ((pullback f).obj M)).hom.app ((pullback f).obj N)
            ((pullbackStalkIso f x).inv.app M
              ((ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
                ((moduleStalkFunctor Y (f x)).obj M)
                (TopCat.Presheaf.germ M.presheaf V (f x) hV s)) ⊗ₜ
            (pullbackStalkIso f x).inv.app N
              ((ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom).unit.app
                ((moduleStalkFunctor Y (f x)).obj N)
                (TopCat.Presheaf.germ N.presheaf V (f x) hV t))) := rfl
        _ = _ := by rw [e1, e2]
        _ = _ := fixedLeftTensorStalkIso_hom_app_germ_tmul x _ _ (f ⁻¹ᵁ V) hV _ _
    exact hL.trans hR.symm
  have hiso : IsIso (E.map ((fixedLeftTensorStalkIso Y (f x) M).hom.app N) ≫
      (pullbackStalkIso f x).inv.app (M ⊗ N) ≫
        (moduleStalkFunctor X x).map (δ (pullback f) M N)) := by
    rw [key]
    infer_instance
  rw [← Category.assoc] at hiso
  exact IsIso.of_isIso_comp_left (E.map ((fixedLeftTensorStalkIso Y (f x) M).hom.app N) ≫
      (pullbackStalkIso f x).inv.app (M ⊗ N)) _

/-- The oplax unit of pullback is `SheafOfModules.pullbackObjUnitToUnit`. -/
private lemma isIso_pullback_η :
    letI := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
    IsIso (η (pullback f)) := by
  let := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
  change IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  infer_instance

/-- The oplax tensorator of pullback is an isomorphism, checked on stalks. -/
private lemma isIso_pullback_δ (M N : Y.Modules) :
    letI := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
    IsIso (δ (pullback f) M N) := by
  let := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
  have (x : X) := isIso_stalk_δ f M N x
  exact (moduleStalkFunctors_jointlyReflectIsomorphisms X).isIso _

/-- Pullback of module sheaves is strong monoidal (Stacks, Tag 01CD). It upgrades the oplax
structure that the pullback-pushforward adjunction induces from `pushforwardLaxMonoidal`. -/
instance pullbackMonoidal : (pullback f).Monoidal :=
  letI := (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal
  haveI := isIso_pullback_η f
  haveI := isIso_pullback_δ f
  Functor.Monoidal.ofOplaxMonoidal (pullback f)

/-- The oplax part of `pullbackMonoidal` is the one induced by the adjunction. -/
theorem pullbackMonoidal_toOplaxMonoidal :
    (pullbackMonoidal f).toOplaxMonoidal =
      (pullbackPushforwardAdjunction f).leftAdjointOplaxMonoidal :=
  rfl

/-- The tensor comparison of the strong monoidal pullback. -/
noncomputable def pullbackTensorIso (M N : Y.Modules) :
    tensorObj ((pullback f).obj M) ((pullback f).obj N) ≅
      (pullback f).obj (tensorObj M N) := by
  change (pullback f).obj M ⊗ (pullback f).obj N ≅
    (pullback f).obj (M ⊗ N)
  exact Functor.Monoidal.μIso (pullback f) M N

/-- The unit comparison of the strong monoidal pullback. -/
noncomputable def pullbackUnitIso :
    (pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  change (pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules
  exact (Functor.Monoidal.εIso (pullback f)).symm

example (M N : Y.Modules) :
    tensorObj ((pullback f).obj M) ((pullback f).obj N) ≅ (pullback f).obj (tensorObj M N) :=
  pullbackTensorIso f M N

end

end AlgebraicGeometry.Scheme.Modules
