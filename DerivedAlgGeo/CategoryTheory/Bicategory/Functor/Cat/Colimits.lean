/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Preadditive

/-!
# Componentwise colimits of strong transformations

Let `G : LocallyDiscrete B₀ ⥤ᵖ Cat` be a pseudofunctor whose fibres have colimits of shape `J`
and whose transition functors preserve them. For every pseudofunctor `F`, the category of strong
transformations `F ⟶ G` (Mathlib's `Pseudofunctor.StrongTrans.homCategory`) has colimits of
shape `J`, computed componentwise: the component over `a` of the colimit of `K : J ⥤ (F ⟶ G)`
is the colimit, in the functor category `F(a) ⥤ G(a)`, of the components of `K`.

## Main definitions

* `CategoryTheory.Pseudofunctor.StrongTrans.componentDiagram K a`: the components over `a` of a
  diagram `K` of strong transformations.
* `CategoryTheory.Pseudofunctor.StrongTrans.colimitCocone K`: the componentwise colimit cocone.

## Main results

* `CategoryTheory.Pseudofunctor.StrongTrans.isColimitColimitCocone`: it is a colimit cocone.
* `CategoryTheory.Pseudofunctor.StrongTrans.hasColimitsOfShape`: strong transformations
  `F ⟶ G` have colimits of shape `J`.

## Implementation notes

The naturality isomorphism of the colimit along `f : a ⟶ b` is
`f^* ⋙ colim_j K_j(b) ≅ colim_j (f^* ⋙ K_j(b)) ≅ colim_j (K_j(a) ⋙ f^*) ≅ colim_j K_j(a) ⋙ f^*`:
whiskering on the left commutes with colimits in functor categories, the middle isomorphism is
the naturality of the `K_j`, and the last step is preservation of colimits by `G.map f`. Every
coherence condition is checked after precomposition with the colimit injections
(`CategoryTheory.Limits.colimit_obj_ext`), where it is that of the `K_j`.

The base is locally discrete, so that the naturality of the colimit with respect to 2-morphisms
of the base is trivial.

## Tags

pseudofunctor, strong transformation, modification, colimit
-/

namespace CategoryTheory.Pseudofunctor.StrongTrans

open Bicategory Limits
open scoped StrongTrans

universe w w' v v' u u'

variable {B₀ : Type u} [Category.{v} B₀] {F G : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'}}
  {J : Type w} [Category.{w'} J]

/-- The components over `a` of a diagram of strong transformations, as a diagram of functors
`F(a) ⥤ G(a)`. -/
@[simps]
abbrev componentDiagram (K : J ⥤ (F ⟶ G)) (a : LocallyDiscrete B₀) : J ⥤ (F.obj a ⥤ G.obj a) where
  obj j := ((K.obj j).app a).toFunctor
  map φ := ((K.map φ).as.app a).toNatTrans
  map_id j := by rw [K.map_id]; rfl
  map_comp φ ψ := by rw [K.map_comp]; rfl

variable [∀ a, HasColimitsOfShape J (G.obj a)]
  [∀ ⦃a b : LocallyDiscrete B₀⦄ (f : a ⟶ b), PreservesColimitsOfShape J (G.map f).toFunctor]
  (K : J ⥤ (F ⟶ G))

/-- The naturality isomorphisms of the `K_j` along `f`, as an isomorphism of diagrams. -/
@[simps!]
def componentDiagramNaturality {a b : LocallyDiscrete B₀} (f : a ⟶ b) :
    componentDiagram K b ⋙ (Functor.whiskeringLeft _ _ _).obj (F.map f).toFunctor ≅
      componentDiagram K a ⋙ (Functor.whiskeringRight _ _ _).obj (G.map f).toFunctor :=
  NatIso.ofComponents (fun j ↦ Cat.Hom.toNatIso ((K.obj j).naturality f)) (fun φ ↦ by
    ext x
    exact congrArg (fun t ↦ t.toNatTrans.app x) ((K.map φ).as.naturality f))

/-- The naturality isomorphism of the componentwise colimit along `f`. -/
noncomputable def colimitNaturality {a b : LocallyDiscrete B₀} (f : a ⟶ b) :
    (F.map f).toFunctor ⋙ colimit (componentDiagram K b) ≅
      colimit (componentDiagram K a) ⋙ (G.map f).toFunctor :=
  (colimitCompWhiskeringLeftIsoCompColimit _ _).symm ≪≫
    HasColimit.isoOfNatIso (componentDiagramNaturality K f) ≪≫
      colimitCompWhiskeringRightIsoColimitComp _ _

/-- The naturality isomorphism of the componentwise colimit, after a colimit injection: the
naturality isomorphism of `K_j`, followed by the image of the injection. -/
@[reassoc (attr := simp)]
lemma ι_colimitNaturality_hom_app {a b : LocallyDiscrete B₀} (f : a ⟶ b) (j : J)
    (x : F.obj a) :
    (colimit.ι (componentDiagram K b) j).app ((F.map f).toFunctor.obj x) ≫
        (colimitNaturality K f).hom.app x =
      ((K.obj j).naturality f).hom.toNatTrans.app x ≫
        (G.map f).toFunctor.map ((colimit.ι (componentDiagram K a) j).app x) := by
  have h₁ := congrArg (fun t ↦ t.app x)
    (whiskerLeft_ι_colimitCompWhiskeringLeftIsoCompColimit_inv (componentDiagram K b)
      (F.map f).toFunctor j)
  have h₂ := congrArg (fun t ↦ t.app x)
    (ι_colimitCompWhiskeringRightIsoColimitComp_hom (G.map f).toFunctor
      (componentDiagram K a) j)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h₁ h₂
  simp only [colimitNaturality, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, reassoc_of% h₁]
  rw [← NatTrans.comp_app_assoc, HasColimit.ι_isoOfNatIso_hom, NatTrans.comp_app,
    Category.assoc]
  erw [h₂]
  rfl

/-- The componentwise colimit of a diagram of strong transformations. -/
noncomputable def colimitObj : F ⟶ G where
  app a := (colimit (componentDiagram K a)).toCatHom
  naturality f := Cat.Hom.isoMk (colimitNaturality K f)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id a := by
    ext x
    refine colimit_obj_ext fun j ↦ ?_
    have h := congrArg (fun t ↦ t.toNatTrans.app x) ((K.obj j).naturality_id a)
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app] at h
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.leftUnitor_hom_app, Cat.rightUnitor_inv_app, Cat.Hom.isoMk_hom,
      NatTrans.toCatHom₂_toNatTrans, Functor.toCatHom_toFunctor]
    rw [ι_colimitNaturality_hom_app_assoc]
    have hm := (G.mapId a).hom.toNatTrans.naturality ((colimit.ι (componentDiagram K a) j).app x)
    have hι := (colimit.ι (componentDiagram K a) j).naturality ((F.mapId a).hom.toNatTrans.app x)
    erw [hm, reassoc_of% h, ← reassoc_of% hι]
    simp
  naturality_comp {a b c} f g := by
    ext x
    refine colimit_obj_ext fun j ↦ ?_
    have h := congrArg (fun t ↦ t.toNatTrans.app x) ((K.obj j).naturality_comp f g)
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans, Functor.associator_hom_app,
      Functor.associator_inv_app, Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp,
      Category.comp_id] at h
    simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app,
      Cat.associator_hom_toNatTrans, Cat.associator_inv_toNatTrans, Functor.associator_hom_app,
      Functor.associator_inv_app, Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.id_comp,
      Category.comp_id, Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans,
      Functor.toCatHom_toFunctor]
    rw [ι_colimitNaturality_hom_app_assoc]
    have hm := (G.mapComp f g).hom.toNatTrans.naturality
      ((colimit.ι (componentDiagram K a) j).app x)
    have hι := (colimit.ι (componentDiagram K c) j).naturality
      ((F.mapComp f g).hom.toNatTrans.app x)
    erw [hm, reassoc_of% h, ← reassoc_of% hι, ι_colimitNaturality_hom_app_assoc]
    simp only [← Functor.map_comp, ι_colimitNaturality_hom_app]
    rw [Functor.map_comp]
    rfl

/-- The components of the componentwise colimit are the colimits of the components. -/
@[simp]
lemma colimitObj_app (a : LocallyDiscrete B₀) :
    ((colimitObj K).app a).toFunctor = colimit (componentDiagram K a) :=
  rfl

/-- The componentwise colimit cocone: its injections are the colimit injections of the
components. -/
@[simps pt]
noncomputable def colimitCocone : Cocone K where
  pt := colimitObj K
  ι :=
    { app j := homOfApp (fun a ↦ colimit.ι (componentDiagram K a) j)
        (fun _ _ f x ↦ ι_colimitNaturality_hom_app K f j x)
      naturality _ _ φ := hom_ext' fun a ↦
        (colimit.w (componentDiagram K a) φ).trans (Category.comp_id _).symm }

/-- The components of the injections of `colimitCocone K` are the colimit injections. -/
@[simp]
lemma colimitCocone_ι_app_as_app_toNatTrans (j : J) (a : LocallyDiscrete B₀) :
    (((colimitCocone K).ι.app j).as.app a).toNatTrans = colimit.ι (componentDiagram K a) j :=
  rfl

/-- The components over `a` of a cocone over `K`, as a cocone over `componentDiagram K a`. -/
@[simps]
def componentCocone {K : J ⥤ (F ⟶ G)} (s : Cocone K) (a : LocallyDiscrete B₀) :
    Cocone (componentDiagram K a) where
  pt := (s.pt.app a).toFunctor
  ι :=
    { app j := ((s.ι.app j).as.app a).toNatTrans
      naturality j j' φ := by
        exact congrArg (fun t ↦ (t.as.app a).toNatTrans) (s.ι.naturality φ) }

/-- The componentwise colimit cocone is a colimit cocone. -/
noncomputable def isColimitColimitCocone : IsColimit (colimitCocone K) where
  desc s := homOfApp (fun a ↦ colimit.desc (componentDiagram K a) (componentCocone s a))
    (fun a b f x ↦ by
      refine colimit_obj_ext fun j ↦ ?_
      have h := congrArg (fun t ↦ t.toNatTrans.app x) ((s.ι.app j).as.naturality f)
      simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.whiskerRight_app] at h
      have hb := congrArg (fun t ↦ t.app ((F.map f).toFunctor.obj x))
        (colimit.ι_desc (componentCocone s b) j)
      have ha := congrArg (fun t ↦ t.app x) (colimit.ι_desc (componentCocone s a) j)
      simp only [NatTrans.comp_app, componentCocone_ι_app] at ha hb
      erw [reassoc_of% hb, h, ι_colimitNaturality_hom_app_assoc K f j x, ← Functor.map_comp, ha])
  fac s j := hom_ext' fun a ↦ colimit.ι_desc (componentCocone s a) j
  uniq s m hm := hom_ext' fun a ↦ colimit.hom_ext fun j ↦
    (congrArg (fun t ↦ (t.as.app a).toNatTrans) (hm j)).trans
      (colimit.ι_desc (componentCocone s a) j).symm

/-- Strong transformations into a pseudofunctor whose fibres have colimits of shape `J`,
preserved by its transition functors, have colimits of shape `J`, computed componentwise.
Scoped, like the category structure `Pseudofunctor.StrongTrans.homCategory`. -/
scoped instance hasColimitsOfShape : HasColimitsOfShape J (F ⟶ G) where
  has_colimit K := ⟨⟨⟨colimitCocone K, isColimitColimitCocone K⟩⟩⟩

end CategoryTheory.Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.ulift

open Bicategory Limits

universe w₁ w₂ w w' v v' u u'

variable {B₀ : Type u} [Category.{v} B₀] (F : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'})
  (J : Type w) [Category.{w'} J]

/-- The fibres of `F.ulift` have colimits of shape `J` where those of `F` do: they are
equivalent to them. -/
instance hasColimitsOfShape_obj (X : LocallyDiscrete B₀) [HasColimitsOfShape J (F.obj X)] :
    HasColimitsOfShape J ((F.ulift.{w₁, w₂}).obj X) :=
  Adjunction.hasColimitsOfShape_of_equivalence (objEquivalence.{w₁, w₂} F X).inverse

/-- The transition functors of `F.ulift` preserve colimits of shape `J` where those of `F` do:
they are conjugate to them by equivalences. -/
instance preservesColimitsOfShape_map {X Y : LocallyDiscrete B₀} (f : X ⟶ Y)
    [PreservesColimitsOfShape J (F.map f).toFunctor] :
    PreservesColimitsOfShape J ((F.ulift.{w₁, w₂}).map f).toFunctor := by
  rw [map_toFunctor]
  infer_instance

end CategoryTheory.Pseudofunctor.ulift
