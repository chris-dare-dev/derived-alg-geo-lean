/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.FiberProduct
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentData

/-!
# Two-fibre products of stacks

Let `α : F ⟶ H` and `β : G ⟶ H` be strong transformations of pseudofunctors
`LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`. If `F` and `G` are stacks for a Grothendieck topology `J` and `H`
is a prestack, the 2-fibre product `Pseudofunctor.fiberProduct α β` is a stack; if all three are
prestacks, it is a prestack. The terminal pseudofunctor is a stack.

## Main definitions

None. The 2-fibre product, its projections and the terminal pseudofunctor are in
`DerivedAlgGeo/CategoryTheory/Bicategory/Functor/Cat/FiberProduct.lean`.

## Main results

* `Pseudofunctor.fiberProduct.faithful_toDescentData`,
  `Pseudofunctor.fiberProduct.full_toDescentData` and
  `Pseudofunctor.fiberProduct.essSurj_toDescentData`: restriction to descent data along one
  family, for the 2-fibre product, in terms of the same property for `F`, `G` and `H`.
* `Pseudofunctor.isPrestack_fiberProduct` and `Pseudofunctor.isStack_fiberProduct`.
* `Pseudofunctor.isStack_terminal`.

## Implementation notes

The argument runs one family at a time. A descent datum of the 2-fibre product is mapped to
descent data of `F` and `G` with `DescentData.map` along the two projections, and the
2-commutativity isomorphism `fiberProduct.comm` maps it to an isomorphism of their images in
`H.DescentData`. Gluing in `F` and `G` and descending that isomorphism along the fully faithful
`H.toDescentData` gives an object of the fibre product, so only descent of morphisms is used
in `H`. Descent data of the fibre product are never identified with triples of descent data.

## References

* [Stacks Project, Tag 02ZL](https://stacks.math.columbia.edu/tag/02ZL), Lemma 8.5.6
* [Stacks Project, Tag 026G](https://stacks.math.columbia.edu/tag/026G), Lemma 8.4.6

## Tags

stack, prestack, descent, 2-fibre product, categorical pullback
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory Limits CategoricalPullback
open scoped StrongTrans

variable {C : Type u} [Category.{v} C]

namespace DescentData

variable {F' : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {ι : Type t} {S : C} {X : ι → C}
  {f : ∀ i, X i ⟶ S} {D₁ D₂ : F'.DescentData f}

@[reassoc (attr := simp)]
private lemma hom_inv_id_hom (e : D₁ ≅ D₂) (i : ι) : e.hom.hom i ≫ e.inv.hom i = 𝟙 _ := by
  rw [← comp_hom, e.hom_inv_id, id_hom]

@[reassoc (attr := simp)]
private lemma inv_hom_id_hom (e : D₁ ≅ D₂) (i : ι) : e.inv.hom i ≫ e.hom.hom i = 𝟙 _ := by
  rw [← comp_hom, e.inv_hom_id, id_hom]

/-- The component at `i` of an isomorphism of descent data. -/
private def isoApp (e : D₁ ≅ D₂) (i : ι) : D₁.obj i ≅ D₂.obj i where
  hom := e.hom.hom i
  inv := e.inv.hom i

end DescentData

section FiberProduct

variable {F G H : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', max v' u'}} (α : F ⟶ H) (β : G ⟶ H)

namespace fiberProduct

section mapComp'

variable {X Y Z : LocallyDiscrete Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg)
  (x : (α.app X).toFunctor ⊡ (β.app X).toFunctor)

@[simp]
private lemma mapComp'_hom_app_fst :
    (((fiberProduct α β).mapComp' f g fg h).hom.toNatTrans.app x).fst =
      (F.mapComp' f g fg h).hom.toNatTrans.app x.fst := by
  subst h
  simp [mapComp'_eq_mapComp]

@[simp]
private lemma mapComp'_hom_app_snd :
    (((fiberProduct α β).mapComp' f g fg h).hom.toNatTrans.app x).snd =
      (G.mapComp' f g fg h).hom.toNatTrans.app x.snd := by
  subst h
  simp [mapComp'_eq_mapComp]

@[simp]
private lemma mapComp'_inv_app_fst :
    (((fiberProduct α β).mapComp' f g fg h).inv.toNatTrans.app x).fst =
      (F.mapComp' f g fg h).inv.toNatTrans.app x.fst := by
  subst h
  simp [mapComp'_eq_mapComp]

@[simp]
private lemma mapComp'_inv_app_snd :
    (((fiberProduct α β).mapComp' f g fg h).inv.toNatTrans.app x).snd =
      (G.mapComp' f g fg h).inv.toNatTrans.app x.snd := by
  subst h
  simp [mapComp'_eq_mapComp]

end mapComp'

variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Restriction to descent data of the 2-fibre product is faithful when it is so for `F` and
`G`: a morphism of the fibre product is a pair of morphisms. -/
instance faithful_toDescentData [(F.toDescentData f).Faithful] [(G.toDescentData f).Faithful] :
    ((fiberProduct α β).toDescentData f).Faithful where
  map_injective {_ _} _ _ h := CategoricalPullback.hom_ext
    ((F.toDescentData f).map_injective
      (DescentData.hom_ext fun i ↦ congr_arg (fun ψ ↦ (ψ.hom i).fst) h))
    ((G.toDescentData f).map_injective
      (DescentData.hom_ext fun i ↦ congr_arg (fun ψ ↦ (ψ.hom i).snd) h))

/-- Restriction to descent data of the 2-fibre product is full when it is so for `F` and `G`
and faithful for `H`. The two components of a morphism of descent data glue in `F` and `G`,
and the glued pair is compatible with the structure isomorphisms because it is so after
restriction, where `H.toDescentData` is faithful. -/
instance full_toDescentData [(F.toDescentData f).Full] [(G.toDescentData f).Full]
    [(H.toDescentData f).Faithful] : ((fiberProduct α β).toDescentData f).Full where
  map_surjective {x y} ψ := by
    obtain ⟨a, ha⟩ := (F.toDescentData f).map_surjective
      ((toDescentDataCompMapIso f (fst α β)).inv.app x ≫
        (DescentData.map f (fst α β)).map ψ ≫ (toDescentDataCompMapIso f (fst α β)).hom.app y)
    obtain ⟨c, hc⟩ := (G.toDescentData f).map_surjective
      ((toDescentDataCompMapIso f (snd α β)).inv.app x ≫
        (DescentData.map f (snd α β)).map ψ ≫ (toDescentDataCompMapIso f (snd α β)).hom.app y)
    replace ha i := congr_arg (fun φ ↦ φ.hom i) ha
    replace hc i := congr_arg (fun φ ↦ φ.hom i) hc
    simp at ha hc
    refine ⟨⟨a, c, (H.toDescentData f).map_injective (DescentData.hom_ext fun i ↦ ?_)⟩,
      DescentData.hom_ext fun i ↦ CategoricalPullback.hom_ext ?_ ?_⟩
    · have hw := (ψ.hom i).w
      have h₁ := (α.naturality (f i).op.toLoc).hom.toNatTrans.naturality a
      have h₂ := (β.naturality (f i).op.toLoc).inv.toNatTrans.naturality c
      dsimp at hw h₁ h₂ ⊢
      rw [ha] at h₁
      rw [hc] at h₂
      simp only [map_obj_iso_hom, Category.assoc] at hw
      rw [Functor.map_comp, Functor.map_comp,
        ← cancel_epi ((α.naturality (f i).op.toLoc).hom.toNatTrans.app x.fst),
        ← reassoc_of% h₁, ← cancel_mono ((β.naturality (f i).op.toLoc).inv.toNatTrans.app y.snd)]
      simp only [Category.assoc, h₂, hw]
    · exact ha i
    · exact hc i

/-- Descent data of the 2-fibre product are effective when those of `F` and `G` are and
`H.toDescentData` is fully faithful. A descent datum `D` maps along the projections to descent
data of `F` and `G`, glued by objects `a` and `c`; the image of `fiberProduct.comm` under
`DescentData.map` relates their restrictions in `H`, and descends to `α a ≅ β c`. -/
instance essSurj_toDescentData [(F.toDescentData f).EssSurj] [(G.toDescentData f).EssSurj]
    [(H.toDescentData f).Full] [(H.toDescentData f).Faithful] :
    ((fiberProduct α β).toDescentData f).EssSurj where
  mem_essImage D := by
    let a := (F.toDescentData f).objPreimage ((DescentData.map f (fst α β)).obj D)
    let ea := (F.toDescentData f).objObjPreimageIso ((DescentData.map f (fst α β)).obj D)
    let c := (G.toDescentData f).objPreimage ((DescentData.map f (snd α β)).obj D)
    let ec := (G.toDescentData f).objObjPreimageIso ((DescentData.map f (snd α β)).obj D)
    let E : (H.toDescentData f).obj ((α.app _).toFunctor.obj a) ≅
        (H.toDescentData f).obj ((β.app _).toFunctor.obj c) :=
      ((toDescentDataCompMapIso f α).app a).symm ≪≫ (DescentData.map f α).mapIso ea ≪≫
        (DescentData.mapComp f (fst α β) α).symm.app D ≪≫
        (DescentData.mapIso f (comm α β)).app D ≪≫
        (DescentData.mapComp f (snd α β) β).app D ≪≫ (DescentData.map f β).mapIso ec.symm ≪≫
        (toDescentDataCompMapIso f β).app c
    let x : (α.app (.mk (op S))).toFunctor ⊡ (β.app (.mk (op S))).toFunctor :=
      ⟨a, c, (H.toDescentData f).preimageIso E⟩
    refine ⟨x, ⟨DescentData.isoMk
      (fun i ↦ mkIso (DescentData.isoApp ea i) (DescentData.isoApp ec i) ?_) ?_⟩⟩
    · have he := congr_arg (fun φ ↦ φ.hom i) ((H.toDescentData f).map_preimage E.hom)
      dsimp at he
      dsimp [DescentData.isoApp]
      erw [map_obj_iso_hom]
      dsimp only [x, Functor.preimageIso_hom]
      rw [he]
      simp [E]
      erw [Category.id_comp, ← Functor.map_comp, DescentData.inv_hom_id_hom, Functor.map_id,
        Category.comp_id]
    · intro Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      refine CategoricalPullback.hom_ext ?_ ?_
      · simpa [DescentData.isoApp] using ea.hom.comm q f₁ f₂ hf₁ hf₂
      · simpa [DescentData.isoApp] using ec.hom.comm q f₁ f₂ hf₁ hf₂

end fiberProduct

variable {J : GrothendieckTopology C}

/-- The 2-fibre product of prestacks is a prestack. -/
theorem isPrestack_fiberProduct [F.IsPrestack J] [G.IsPrestack J] [H.IsPrestack J] :
    (fiberProduct α β).IsPrestack J :=
  .of_isPrestackFor fun _ R hR ↦
    have := (F.isPrestackFor' R hR).fullyFaithful.full
    have := (G.isPrestackFor' R hR).fullyFaithful.full
    have := (F.isPrestackFor' R hR).fullyFaithful.faithful
    have := (G.isPrestackFor' R hR).fullyFaithful.faithful
    have := (H.isPrestackFor' R hR).fullyFaithful.faithful
    ⟨⟨.ofFullyFaithful _⟩⟩

/-- The 2-fibre product `F ×_H G` of stacks `F` and `G` over a prestack `H` is a stack. This is
the existence of 2-fibre products of stacks
([Stacks Project, Tag 026G](https://stacks.math.columbia.edu/tag/026G)) and, for stacks in
groupoids, [Stacks Project, Tag 02ZL](https://stacks.math.columbia.edu/tag/02ZL). Both assume
that `H` is a stack; gluing objects only uses descent of morphisms in `H`.

The hypothesis that `H` is a prestack cannot be dropped. On the open sets of a topological space
with the open-cover topology, the empty family covers `∅`, so a sheaf has exactly one section
over `∅`. Let `H` be the constant pseudofunctor at the one-object groupoid `B(ℤ/2)`, whose
presheaf of morphisms is the constant presheaf `ℤ/2`; it is not separated at `∅`. Let `F = G`
be `terminal` and `α`, `β` pick the object. The 2-fibre product is the discrete category on
`ℤ/2` over every open, and its presheaf of morphisms between two distinct objects is empty over
`∅`, so it is not a prestack.

The hypotheses on `F` and `G` cannot be dropped either: for `β = 𝟙 H`, the first projection of
`F ×_H H` has components that are equivalences of categories, so the fibre product is a stack
exactly when `F` is (`Pseudofunctor.isStack_iff_of_isEquivalence`). -/
theorem isStack_fiberProduct [F.IsStack J] [G.IsStack J] [H.IsPrestack J] :
    (fiberProduct α β).IsStack J where
  toIsPrestack := isPrestack_fiberProduct α β
  essSurj_of_sieve R hR :=
    have := IsStack.essSurj_of_sieve F R hR
    have := IsStack.essSurj_of_sieve G R hR
    have := (H.isPrestackFor' R hR).fullyFaithful.full
    have := (H.isPrestackFor' R hR).fullyFaithful.faithful
    inferInstance

end FiberProduct

section Terminal

private lemma terminal_obj_eq {X : LocallyDiscrete Cᵒᵖ}
    (a b : (terminal.{v, u, v', u'} Cᵒᵖ).obj X) : a = b := by
  rcases a with ⟨⟨⟨⟩⟩⟩
  rcases b with ⟨⟨⟨⟩⟩⟩
  rfl

private instance {X : LocallyDiscrete Cᵒᵖ} (a b : (terminal.{v, u, v', u'} Cᵒᵖ).obj X) :
    Subsingleton (a ⟶ b) := by
  constructor
  rintro ⟨⟨⟨⟩⟩⟩ ⟨⟨⟨⟩⟩⟩
  rfl

/-- The fibres of `terminal` are groupoids: any two objects are equal, with a unique morphism
between them. -/
instance isGroupoid_terminal_obj (X : LocallyDiscrete Cᵒᵖ) :
    IsGroupoid ((terminal.{v, u, v', u'} Cᵒᵖ).obj X) where
  all_isIso _ := ⟨eqToHom (terminal_obj_eq _ _), Subsingleton.elim _ _, Subsingleton.elim _ _⟩

private instance {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    (D₁ D₂ : (terminal.{v, u, v', u'} Cᵒᵖ).DescentData f) : Subsingleton (D₁ ⟶ D₂) :=
  ⟨fun _ _ ↦ DescentData.hom_ext fun _ ↦ Subsingleton.elim _ _⟩

/-- Any two descent data of `terminal` are related by a unique morphism. -/
private def terminalDescentDataHom {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
    (D₁ D₂ : (terminal.{v, u, v', u'} Cᵒᵖ).DescentData f) : D₁ ⟶ D₂ where
  hom _ := eqToHom (terminal_obj_eq _ _)
  comm _ _ _ _ _ _ _ _ := Subsingleton.elim _ _

private lemma isEquivalence_terminal_toDescentData {ι : Type t} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) : ((terminal.{v, u, v', u'} Cᵒᵖ).toDescentData f).IsEquivalence where
  faithful := ⟨fun _ ↦ Subsingleton.elim _ _⟩
  full := ⟨fun _ ↦ ⟨eqToHom (terminal_obj_eq _ _), Subsingleton.elim _ _⟩⟩
  essSurj := ⟨fun _ ↦ ⟨⟨⟨⟨⟩⟩⟩, ⟨⟨terminalDescentDataHom _ _, terminalDescentDataHom _ _,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩⟩⟩

/-- The terminal pseudofunctor is a stack for every topology: its fibres and its categories of
descent data along any family have exactly one morphism between any two objects. -/
theorem isStack_terminal {J : GrothendieckTopology C} : (terminal.{v, u, v', u'} Cᵒᵖ).IsStack J :=
  .of_isStackFor fun _ _ _ ↦ ⟨isEquivalence_terminal_toDescentData _⟩

end Terminal

end CategoryTheory.Pseudofunctor
