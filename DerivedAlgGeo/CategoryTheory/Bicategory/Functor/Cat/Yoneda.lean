/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo
import Mathlib.CategoryTheory.Yoneda
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ULift

/-!
# The 2-Yoneda lemma for Cat-valued pseudofunctors

For an object `U` of a category `C`, the representable pseudofunctor
`Pseudofunctor.representable U` sends `T` to the discrete category on `T ⟶ U`, lifted by
`Pseudofunctor.ulift` into the fibre universes `Cat.{max v w₁, max v w₂}`. For every
pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max v w₁, max v w₂}`, evaluation at the universal
point `𝟙 U` is an equivalence between strong transformations `representable U ⟶ F` with their
modifications and the fibre `F(U)`.

## Main definitions

* `CategoryTheory.Pseudofunctor.representable`: the representable pseudofunctor of an object.
* `CategoryTheory.Pseudofunctor.ofObj`: the strong transformation `representable U ⟶ F` attached
  to an object `x` of `F(U)`, sending `g : T ⟶ U` to `g^* x`.
* `CategoryTheory.Pseudofunctor.yonedaEvaluation`: evaluation of a strong transformation at the
  universal point `𝟙 U`.
* `CategoryTheory.Pseudofunctor.yonedaEquivalence`: the 2-Yoneda equivalence
  `(representable U ⟶ F) ≌ F(U)`.

## Main results

* `CategoryTheory.Pseudofunctor.yonedaEquivalence`: both directions of the equivalence are
  constructed. The counit is `F.mapId`, and the unit at a strong transformation `α` is built from
  the naturality isomorphisms of `α` at the universal point.

## Implementation notes

Mathlib's `CategoryTheory.Bicategory.yoneda` is the Yoneda embedding of a bicategory `B` into the
pseudofunctors on `Bᵒᵖ`. Taking `B = LocallyDiscrete C` gives pseudofunctors on
`(LocallyDiscrete C)ᵒᵖ`, while stacks and other Cat-valued presheaves are pseudofunctors on
`LocallyDiscrete Cᵒᵖ`, and the comparison between the two bicategories is absent from Mathlib.
This module therefore states the 2-Yoneda lemma for `LocallyDiscrete Cᵒᵖ` directly, with the
representable pseudofunctor `(yoneda.obj U ⋙ typeToCat).toPseudofunctor'`.

That pseudofunctor has fibres in `Cat.{v, v}`. A strong transformation into `F` only typechecks
when both lie in one bicategory, so the representable is lifted by `Pseudofunctor.ulift`; the
lemma then covers every `F` whose fibre universes are at least `v`, such as stacks of sheaves
with fibres in `Cat.{u, u + 1}`.

The fibres of the representable are discrete. A naturality square out of them commutes for any
family of components, and the transition morphisms of the representable reach `F` only as
`eqToHom`. The coherence conditions of `ofObj` are then Mathlib's associativity and unit
equations for `Pseudofunctor.mapComp'` on a strict base.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B): the 2-Yoneda lemma,
  `Mor(C/U, S) → S_U`, `G ↦ G(id_U)`, is an equivalence.
* [Stacks Project, Tag 0GWI](https://stacks.math.columbia.edu/tag/0GWI): the 2-Yoneda lemma for
  fibred categories.

## Tags

2-Yoneda lemma, pseudofunctor, representable, strong transformation
-/

namespace CategoryTheory.Pseudofunctor

open Bicategory Opposite
open scoped Pseudofunctor.StrongTrans

universe w₁ w₂ v u

variable {C : Type u} [Category.{v} C]

/-- The representable pseudofunctor of `U`: its fibre over `T` is the discrete category on
`T ⟶ U`, lifted by `Pseudofunctor.ulift` to `Cat.{max v w₁, max v w₂}`. -/
abbrev representable (U : C) : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max v w₁, max v w₂} :=
  ((yoneda.obj U ⋙ typeToCat).toPseudofunctor').ulift.{w₁, w₂}

namespace representable

/-- The fibres of the representable pseudofunctor are discrete. -/
instance isDiscrete_obj (U : C) (a : LocallyDiscrete Cᵒᵖ) :
    IsDiscrete ((representable.{w₁, w₂} U).obj a) :=
  haveI : IsDiscrete (((yoneda.obj U ⋙ typeToCat).toPseudofunctor').obj a) := by
    change IsDiscrete (Discrete _)
    infer_instance
  ulift.isDiscrete_obj _ a

variable {U : C} {a : LocallyDiscrete Cᵒᵖ}

/-- A morphism `g : T ⟶ U`, as an object of the fibre of `representable U` over `T`. -/
def ofHom (g : a.as.unop ⟶ U) : (representable.{w₁, w₂} U).obj a :=
  (ulift.objEquivalence _ a).functor.obj (Discrete.mk g)

/-- The morphism to `U` underlying an object of a fibre of `representable U`. -/
def toHom (y : (representable.{w₁, w₂} U).obj a) : a.as.unop ⟶ U :=
  ((ulift.objEquivalence _ a).inverse.obj y).as

/-- `CategoryTheory.Pseudofunctor.representable.toHom` inverts
`CategoryTheory.Pseudofunctor.representable.ofHom`, definitionally. -/
@[simp]
lemma toHom_ofHom (g : a.as.unop ⟶ U) : toHom (ofHom.{w₁, w₂} g) = g :=
  rfl

/-- `CategoryTheory.Pseudofunctor.representable.ofHom` inverts
`CategoryTheory.Pseudofunctor.representable.toHom`, definitionally. -/
@[simp]
lemma ofHom_toHom (y : (representable.{w₁, w₂} U).obj a) : ofHom (toHom y) = y :=
  rfl

end representable

open representable

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max v w₁, max v w₂})

/-- The component of `ofObj F x` over `a`: it sends `g : T ⟶ U` to `g^* x`. -/
def ofObjApp {U : C} (x : F.obj (.mk (op U))) (a : LocallyDiscrete Cᵒᵖ) :
    (representable.{w₁, w₂} U).obj a ⥤ F.obj a :=
  (ulift.objEquivalence _ a).inverse ⋙
    Discrete.functor (fun g ↦ (F.map g.op.toLoc).toFunctor.obj x)

/-- `CategoryTheory.Pseudofunctor.ofObjApp` sends `g : T ⟶ U` to `g^* x`. -/
@[simp]
lemma ofObjApp_obj {U : C} (x : F.obj (.mk (op U))) {a : LocallyDiscrete Cᵒᵖ}
    (y : (representable.{w₁, w₂} U).obj a) :
    (ofObjApp F x a).obj y = (F.map (toHom y).op.toLoc).toFunctor.obj x :=
  rfl

/-- `CategoryTheory.Pseudofunctor.ofObjApp` sends every morphism of the discrete fibre to the
identity, written as `eqToHom`. -/
@[simp]
lemma ofObjApp_map {U : C} (x : F.obj (.mk (op U))) {a : LocallyDiscrete Cᵒᵖ}
    {y y' : (representable.{w₁, w₂} U).obj a} (φ : y ⟶ y') :
    (ofObjApp F x a).map φ = eqToHom (by rw [IsDiscrete.eq_of_hom φ]) := by
  obtain rfl := IsDiscrete.eq_of_hom φ
  obtain rfl := Subsingleton.elim φ (𝟙 _)
  exact (ofObjApp F x a).map_id y

/-- Every family of morphisms between functors out of a fibre of `representable U` is natural,
because the fibre is discrete. -/
private lemma representable_naturality {U : C} {a : LocallyDiscrete Cᵒᵖ} {E : Type*} [Category* E]
    (G H : (representable.{w₁, w₂} U).obj a ⥤ E) (e : ∀ y, G.obj y ⟶ H.obj y)
    {y y' : (representable.{w₁, w₂} U).obj a} (φ : y ⟶ y') :
    G.map φ ≫ e y' = e y ≫ H.map φ := by
  obtain rfl := IsDiscrete.eq_of_hom φ
  obtain rfl := Subsingleton.elim φ (𝟙 _)
  simp

private lemma mapComp'_comp_id_aux {U : C} (x : F.obj (.mk (op U))) {a : LocallyDiscrete Cᵒᵖ}
    (k K : (LocallyDiscrete.mk (op U)) ⟶ a) (h : k ≫ 𝟙 a = K) :
    (F.mapComp' k (𝟙 a) K h).hom.toNatTrans.app x ≫
        (F.mapId a).hom.toNatTrans.app ((F.map k).toFunctor.obj x) =
      eqToHom (by rw [← h, Bicategory.Strict.comp_id]; rfl) := by
  obtain rfl : K = k := by rw [← h, Bicategory.Strict.comp_id]
  rw [mapComp'_comp_id_hom_app]
  simp

private lemma mapComp'_assoc_aux {U : C} (x : F.obj (.mk (op U)))
    {a b c : LocallyDiscrete Cᵒᵖ} (k : LocallyDiscrete.mk (op U) ⟶ a) (f : a ⟶ b) (g : b ⟶ c)
    (kf : LocallyDiscrete.mk (op U) ⟶ b) (K K' : LocallyDiscrete.mk (op U) ⟶ c)
    (hkf : k ≫ f = kf) (hK : k ≫ f ≫ g = K) (hK' : kf ≫ g = K')
    (e : (F.map K).toFunctor.obj x = (F.map K').toFunctor.obj x) :
    (F.mapComp' k (f ≫ g) K hK).hom.toNatTrans.app x ≫
        (F.mapComp f g).hom.toNatTrans.app ((F.map k).toFunctor.obj x) =
      eqToHom e ≫ (F.mapComp' kf g K' hK').hom.toNatTrans.app x ≫
        (F.map g).toFunctor.map ((F.mapComp' k f kf hkf).hom.toNatTrans.app x) := by
  obtain rfl : K' = K := by rw [← hK', ← hK, ← hkf, Bicategory.Strict.assoc]
  rw [eqToHom_refl, Category.id_comp, ← F.mapComp'_eq_mapComp]
  exact F.mapComp'₀₁₃_hom_comp_whiskerLeft_mapComp'_hom_app k f g kf (f ≫ g) K' hkf rfl hK x

/-- The naturality isomorphism of `ofObj F x` along `f`: at `g : T ⟶ U` it is the compositor
`(h ≫ g)^* x ≅ h^* g^* x` of `F`, where `h : T' ⟶ T` underlies `f`. -/
def ofObjNaturality {U : C} (x : F.obj (.mk (op U))) {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b) :
    (representable.{w₁, w₂} U).map f ≫ Cat.Hom.ofFunctor (ofObjApp F x b) ≅
      Cat.Hom.ofFunctor (ofObjApp F x a) ≫ F.map f :=
  Cat.Hom.isoMk (NatIso.ofComponents
    (fun y ↦ (Cat.Hom.toNatIso
      (F.mapComp' (toHom y).op.toLoc f (f.as.unop ≫ toHom y).op.toLoc rfl)).app x)
    (fun φ ↦ by apply representable_naturality))

/-- The components of `CategoryTheory.Pseudofunctor.ofObjNaturality` are the compositors of
`F`. -/
@[simp]
lemma ofObjNaturality_hom_app {U : C} (x : F.obj (.mk (op U))) {a b : LocallyDiscrete Cᵒᵖ}
    (f : a ⟶ b) (y : (representable.{w₁, w₂} U).obj a) :
    (ofObjNaturality F x f).hom.toNatTrans.app y =
      (F.mapComp' (toHom y).op.toLoc f (f.as.unop ≫ toHom y).op.toLoc rfl).hom.toNatTrans.app x :=
  rfl

/-- The strong transformation `representable U ⟶ F` attached to `x : F(U)`. It sends
`g : T ⟶ U` to `g^* x`, and its naturality isomorphisms are the compositors
`Pseudofunctor.mapComp'` of `F`; its coherence conditions are those of `F`. -/
def ofObj {U : C} (x : F.obj (.mk (op U))) : representable.{w₁, w₂} U ⟶ F where
  app a := Cat.Hom.ofFunctor (ofObjApp F x a)
  naturality f := ofObjNaturality F x f
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl := Subsingleton.elim η (𝟙 _)
    simp
  naturality_id a := by
    ext y
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      ofObjNaturality_hom_app, ofObjApp_map, Cat.leftUnitor_hom_app,
      Cat.rightUnitor_inv_app, eqToHom_trans]
    exact mapComp'_comp_id_aux F x _ _ _
  naturality_comp f g := by
    ext y
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      ofObjNaturality_hom_app, ofObjApp_map, Cat.associator_hom_toNatTrans,
      Cat.associator_inv_toNatTrans, Functor.associator_hom_app, Functor.associator_inv_app,
      Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp, Category.comp_id]
    exact mapComp'_assoc_aux F x _ _ _ _ _ _ _ _ _ _

/-- The components of `CategoryTheory.Pseudofunctor.ofObj` are
`CategoryTheory.Pseudofunctor.ofObjApp`. -/
@[simp]
lemma ofObj_app_toFunctor {U : C} (x : F.obj (.mk (op U))) (a : LocallyDiscrete Cᵒᵖ) :
    ((ofObj.{w₁, w₂} F x).app a).toFunctor = ofObjApp F x a :=
  rfl

/-- The naturality isomorphisms of `CategoryTheory.Pseudofunctor.ofObj` are
`CategoryTheory.Pseudofunctor.ofObjNaturality`. -/
@[simp]
lemma ofObj_naturality {U : C} (x : F.obj (.mk (op U))) {a b : LocallyDiscrete Cᵒᵖ}
    (f : a ⟶ b) : (ofObj.{w₁, w₂} F x).naturality f = ofObjNaturality F x f :=
  rfl

/-- The modification `ofObj F x ⟶ ofObj F x'` induced by a morphism `φ : x ⟶ x'`. -/
def ofObjMap {U : C} {x x' : F.obj (.mk (op U))} (φ : x ⟶ x') :
    ofObj.{w₁, w₂} F x ⟶ ofObj F x' :=
  StrongTrans.Hom.of
    { app a := Cat.Hom₂.ofNatTrans
        { app y := (F.map (toHom y).op.toLoc).toFunctor.map φ
          naturality _ _ ψ := representable_naturality (ofObjApp F x a) (ofObjApp F x' a)
            (fun y ↦ (F.map (toHom y).op.toLoc).toFunctor.map φ) ψ }
      naturality f := by
        ext y
        simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app, ofObj_naturality,
          ofObjNaturality_hom_app]
        exact F.mapComp'_hom_naturality _ _ _ _ φ }

/-- The component of `CategoryTheory.Pseudofunctor.ofObjMap φ` at `g : T ⟶ U` is `g^* φ`. -/
@[simp]
lemma ofObjMap_as_app_toNatTrans_app {U : C} {x x' : F.obj (.mk (op U))} (φ : x ⟶ x')
    {a : LocallyDiscrete Cᵒᵖ} (y : (representable.{w₁, w₂} U).obj a) :
    ((ofObjMap F φ).as.app a).toNatTrans.app y = (F.map (toHom y).op.toLoc).toFunctor.map φ :=
  rfl

/-- `ofObj` as a functor from the fibre `F(U)` to the category of strong transformations
`representable U ⟶ F`. -/
@[simps]
def ofObjFunctor (U : C) : F.obj (.mk (op U)) ⥤ (representable.{w₁, w₂} U ⟶ F) where
  obj := ofObj F
  map := ofObjMap F
  map_id x := by
    ext a y
    simp
  map_comp φ ψ := by
    ext a y
    exact (F.map (toHom y).op.toLoc).toFunctor.map_comp φ ψ

/-- Evaluation of a strong transformation `representable U ⟶ F` at the universal point `𝟙 U`. -/
@[simps]
def yonedaEvaluation (U : C) : (representable.{w₁, w₂} U ⟶ F) ⥤ F.obj (.mk (op U)) where
  obj α := (α.app (.mk (op U))).toFunctor.obj (ofHom (𝟙 U))
  map Γ := (Γ.as.app (.mk (op U))).toNatTrans.app (ofHom (𝟙 U))

/-- The component over `a` of the unit of `yonedaEquivalence` at `α`. At `g : T ⟶ U` it is the
naturality isomorphism `α(g^* 𝟙) ≅ g^* α(𝟙)` of `α` at the universal point. -/
def yonedaUnitIsoApp {U : C} (α : representable.{w₁, w₂} U ⟶ F) (a : LocallyDiscrete Cᵒᵖ) :
    α.app a ≅ Cat.Hom.ofFunctor (ofObjApp F ((yonedaEvaluation F U).obj α) a) :=
  Cat.Hom.isoMk (C := (representable.{w₁, w₂} U).obj a) (D := F.obj a) (NatIso.ofComponents
    (fun y ↦ (α.app a).toFunctor.mapIso
        (eqToIso (X := y)
          (Y := ((representable.{w₁, w₂} U).map (toHom y).op.toLoc).toFunctor.obj (ofHom (𝟙 U)))
          (congrArg ofHom (Category.comp_id (toHom y))).symm) ≪≫
      (Cat.Hom.toNatIso (α.naturality (toHom y).op.toLoc)).app (ofHom (𝟙 U)))
    (fun φ ↦ by apply representable_naturality))

/-- The components of `CategoryTheory.Pseudofunctor.yonedaUnitIsoApp` are the naturality
isomorphisms of `α` at the universal point, after identifying `g ≫ 𝟙 U` with `g`. -/
@[simp]
lemma yonedaUnitIsoApp_hom_app {U : C} (α : representable.{w₁, w₂} U ⟶ F) {a : LocallyDiscrete Cᵒᵖ}
    (y : (representable.{w₁, w₂} U).obj a) :
    (yonedaUnitIsoApp F α a).hom.toNatTrans.app y =
      (α.app a).toFunctor.map (eqToHom (congrArg ofHom (Category.comp_id (toHom y))).symm) ≫
        (α.naturality (toHom y).op.toLoc).hom.toNatTrans.app (ofHom (𝟙 U)) :=
  rfl

private lemma naturality_mapComp'_aux {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max v w₁, max v w₂}}
    (α : G ⟶ F) {u a b : LocallyDiscrete Cᵒᵖ} (k : u ⟶ a) (f : a ⟶ b) (K : u ⟶ b)
    (hK : k ≫ f = K) (u₀ : G.obj u) (y : G.obj a) (εa : y ⟶ (G.map k).toFunctor.obj u₀)
    (εb : (G.map f).toFunctor.obj y ⟶ (G.map K).toFunctor.obj u₀)
    (hε : εb = (G.map f).toFunctor.map εa ≫ (G.mapComp' k f K hK).inv.toNatTrans.app u₀) :
    ((α.app b).toFunctor.map εb ≫ (α.naturality K).hom.toNatTrans.app u₀) ≫
        (F.mapComp' k f K hK).hom.toNatTrans.app ((α.app u).toFunctor.obj u₀) =
      (α.naturality f).hom.toNatTrans.app y ≫
        (F.map f).toFunctor.map
          ((α.app a).toFunctor.map εa ≫ (α.naturality k).hom.toNatTrans.app u₀) := by
  subst hK hε
  have hn := (α.naturality f).hom.toNatTrans.naturality εa
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_map] at hn
  rw [mapComp'_eq_mapComp, mapComp'_eq_mapComp, StrongTrans.naturality_comp_hom_app]
  simp only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.assoc, Functor.map_comp,
    Cat.Hom.inv_hom_id_toNatTrans_app, Category.comp_id]
  rw [← Functor.map_comp_assoc (α.app b).toFunctor ((G.mapComp k f).inv.toNatTrans.app u₀),
    Cat.Hom.inv_hom_id_toNatTrans_app, Functor.map_id, Category.id_comp, reassoc_of% hn]

private lemma modification_aux {G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{max v w₁, max v w₂}}
    {α β : G ⟶ F} (Γ : α ⟶ β) {u a : LocallyDiscrete Cᵒᵖ} (k : u ⟶ a) (u₀ : G.obj u)
    (y : G.obj a) (ε : y ⟶ (G.map k).toFunctor.obj u₀) :
    (Γ.as.app a).toNatTrans.app y ≫ (β.app a).toFunctor.map ε ≫
        (β.naturality k).hom.toNatTrans.app u₀ =
      ((α.app a).toFunctor.map ε ≫ (α.naturality k).hom.toNatTrans.app u₀) ≫
        (F.map k).toFunctor.map ((Γ.as.app u).toNatTrans.app u₀) := by
  have h := congrArg (fun η ↦ η.toNatTrans.app u₀) (Γ.as.naturality k)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h
  rw [Category.assoc, ← reassoc_of% ((Γ.as.app a).toNatTrans.naturality ε), h]

/-- The unit of `yonedaEquivalence`: every strong transformation `representable U ⟶ F` is
isomorphic to `ofObj` of its value at the universal point. -/
def yonedaUnitIso (U : C) :
    𝟭 (representable.{w₁, w₂} U ⟶ F) ≅ yonedaEvaluation F U ⋙ ofObjFunctor F U :=
  NatIso.ofComponents (fun α ↦ StrongTrans.isoMk (yonedaUnitIsoApp F α) (fun f ↦ by
      ext y
      simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
        yonedaUnitIsoApp_hom_app]
      exact naturality_mapComp'_aux F α (toHom y).op.toLoc f _ rfl (ofHom (𝟙 U)) y _ _
        (Subsingleton.elim _ _)))
    (fun Γ ↦ by
      ext a y
      exact modification_aux F Γ (toHom y).op.toLoc (ofHom (𝟙 U)) y _)

/-- The counit of `yonedaEquivalence`: the value of `ofObj F x` at the universal point is `𝟙^* x`,
isomorphic to `x` through `F.mapId`. -/
def yonedaCounitIso (U : C) :
    ofObjFunctor.{w₁, w₂} F U ⋙ yonedaEvaluation F U ≅ 𝟭 (F.obj (.mk (op U))) :=
  NatIso.ofComponents (fun x ↦ (Cat.Hom.toNatIso (F.mapId (.mk (op U)))).app x)
    (fun φ ↦ (F.mapId (.mk (op U))).hom.toNatTrans.naturality φ)

/-- **The 2-Yoneda lemma** (Stacks Project, Tags 004B and 0GWI). Evaluation at the universal
point `𝟙 U` is an equivalence between the category of strong transformations
`representable U ⟶ F`, with modifications as morphisms, and the fibre `F(U)`. Its inverse is
`ofObjFunctor`.

Mathlib's `Bicategory.yoneda` is not used: it concerns pseudofunctors on `(LocallyDiscrete C)ᵒᵖ`
rather than `LocallyDiscrete Cᵒᵖ`. -/
@[simps! functor inverse]
def yonedaEquivalence (U : C) : (representable.{w₁, w₂} U ⟶ F) ≌ F.obj (.mk (op U)) :=
  Equivalence.mk (yonedaEvaluation F U) (ofObjFunctor F U) (yonedaUnitIso F U)
    (yonedaCounitIso F U)

end CategoryTheory.Pseudofunctor
