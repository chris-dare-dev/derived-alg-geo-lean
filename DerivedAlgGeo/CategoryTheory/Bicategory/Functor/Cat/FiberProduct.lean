/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat

/-!
# Two-fibre products of Cat-valued pseudofunctors

Given strong transformations `α : F ⟶ H` and `β : G ⟶ H` between pseudofunctors
`LocallyDiscrete B₀ ⥤ᵖ Cat`, this file builds their 2-fibre product. Its fibre over `X` is
Mathlib's categorical pullback `(α.app X).toFunctor ⊡ (β.app X).toFunctor`, whose objects are
triples `(a, c, F(a) ≅ G(c))` as in Stacks Example 4.31.3.

## Main definitions

* `CategoryTheory.Pseudofunctor.fiberProduct α β`: the 2-fibre product.
* `fiberProduct.fst`, `fiberProduct.snd`: its two projections.
* `fiberProduct.comm : fst α β ≫ α ≅ snd α β ≫ β`: the 2-commutativity isomorphism.
* `fiberProduct.lift`: the lift of a 2-commutative square `(p, q, e)`, with the isomorphisms
  `fiberProduct.liftFst` and `fiberProduct.liftSnd` to `p` and `q`.
* `Pseudofunctor.diagonal α : F ⟶ fiberProduct α α`: the relative diagonal.
* `Pseudofunctor.terminal`, `Pseudofunctor.toTerminal`: the constant pseudofunctor at a terminal
  category, so that the absolute product of `F` and `G` is
  `fiberProduct (toTerminal F) (toTerminal G)` and the absolute diagonal is
  `diagonal (toTerminal F)`.

## Main results

* `fiberProduct.lift_comm`: `liftFst`, `comm` and `liftSnd` recover `e`.
* The fibres of `fiberProduct α β` are groupoids when those of `F` and `G` are.

## Implementation notes

The transition functor along `f : X ⟶ Y` whiskers the canonical square of the fibre over `X`
with the `CatCospanTransform` whose legs are `F.map f`, `H.map f`, `G.map f` and whose squares
are the naturality isomorphisms of `α` and `β` (`CatCommSqOver.transform`). Its unitor and
compositor are those of `F` and `G` in the two components, so the coherence equations of the
pseudofunctor reduce to those of `F` and `G`. The base is locally discrete, so no
2-functoriality of categorical pullbacks in 2-cells of the base is needed.

The lift is not shown to be unique up to unique isomorphism: the equivalence of hom-categories
expressing the universal property of Stacks Definition 4.31.2 is not proved here.

## References

* [Stacks, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q), Definition 4.31.2
* [Stacks, Tag 02X9](https://stacks.math.columbia.edu/tag/02X9), Lemma 4.31.4
* [Stacks, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI), Lemma 4.32.5

## Tags

2-fibre product, pseudofunctor, categorical pullback, diagonal
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u v' u'

namespace CategoryTheory.Pseudofunctor

open Bicategory Limits CategoricalPullback
open scoped StrongTrans

section FiberProduct

variable {B₀ : Type u} [Category.{v} B₀]
  {F G H : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', max v' u'}} (α : F ⟶ H) (β : G ⟶ H)

namespace fiberProduct

variable {X Y Z : LocallyDiscrete B₀}

/-- Auxiliary definition for `fiberProduct`: the transition functor along `f`. It whiskers the
canonical square of the fibre over `X` with the cospan transform `(F.map f, H.map f, G.map f)`
whose squares are the naturality isomorphisms of `α` and `β`. -/
def map (f : X ⟶ Y) :
    (α.app X).toFunctor ⊡ (β.app X).toFunctor ⥤ (α.app Y).toFunctor ⊡ (β.app Y).toFunctor :=
  (CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    (((CatCommSqOver.transform _).obj
      { left := (F.map f).toFunctor
        base := (H.map f).toFunctor
        right := (G.map f).toFunctor
        squareLeft := ⟨(Cat.Hom.toNatIso (α.naturality f)).symm⟩
        squareRight := ⟨(Cat.Hom.toNatIso (β.naturality f)).symm⟩ }).obj
      ⟨π₁ _ _, π₂ _ _, CatCommSq.iso _ _ _ _⟩)

section map

variable (f : X ⟶ Y) (x : (α.app X).toFunctor ⊡ (β.app X).toFunctor)

@[simp]
lemma map_obj_fst : ((map α β f).obj x).fst = (F.map f).toFunctor.obj x.fst := rfl

@[simp]
lemma map_obj_snd : ((map α β f).obj x).snd = (G.map f).toFunctor.obj x.snd := rfl

@[simp]
lemma map_obj_iso_hom :
    ((map α β f).obj x).iso.hom = (α.naturality f).hom.toNatTrans.app x.fst ≫
      (H.map f).toFunctor.map x.iso.hom ≫ (β.naturality f).inv.toNatTrans.app x.snd := by
  simp [map]
  rfl

@[simp]
lemma map_obj_iso_inv :
    ((map α β f).obj x).iso.inv = (β.naturality f).hom.toNatTrans.app x.snd ≫
      (H.map f).toFunctor.map x.iso.inv ≫ (α.naturality f).inv.toNatTrans.app x.fst := by
  simp [map]
  rfl

@[simp]
lemma map_map_fst {x y : (α.app X).toFunctor ⊡ (β.app X).toFunctor} (φ : x ⟶ y) :
    ((map α β f).map φ).fst = (F.map f).toFunctor.map φ.fst := rfl

@[simp]
lemma map_map_snd {x y : (α.app X).toFunctor ⊡ (β.app X).toFunctor} (φ : x ⟶ y) :
    ((map α β f).map φ).snd = (G.map f).toFunctor.map φ.snd := rfl

end map

/-- Auxiliary definition for `fiberProduct`: the unitor of the transition functors, given by
the unitors of `F` and `G` in the two components. -/
def mapId (X : LocallyDiscrete B₀) : map α β (𝟙 X) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun x => mkIso ((Cat.Hom.toNatIso (F.mapId X)).app x.fst)
      ((Cat.Hom.toNatIso (G.mapId X)).app x.snd) (by
        simp [StrongTrans.naturality_id_hom_app, StrongTrans.naturality_id_inv_app]
        rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app]
        simp))
    (fun φ => by
      ext
      exacts [(F.mapId X).hom.toNatTrans.naturality φ.fst,
        (G.mapId X).hom.toNatTrans.naturality φ.snd])

section mapId

variable (X : LocallyDiscrete B₀) (x : (α.app X).toFunctor ⊡ (β.app X).toFunctor)

@[simp]
lemma mapId_hom_app_fst : ((mapId α β X).hom.app x).fst = (F.mapId X).hom.toNatTrans.app x.fst :=
  rfl

@[simp]
lemma mapId_hom_app_snd : ((mapId α β X).hom.app x).snd = (G.mapId X).hom.toNatTrans.app x.snd :=
  rfl

@[simp]
lemma mapId_inv_app_fst : ((mapId α β X).inv.app x).fst = (F.mapId X).inv.toNatTrans.app x.fst :=
  rfl

@[simp]
lemma mapId_inv_app_snd : ((mapId α β X).inv.app x).snd = (G.mapId X).inv.toNatTrans.app x.snd :=
  rfl

end mapId

/-- Auxiliary definition for `fiberProduct`: the compositor of the transition functors, given by
the compositors of `F` and `G` in the two components. -/
def mapComp (f : X ⟶ Y) (g : Y ⟶ Z) : map α β (f ≫ g) ≅ map α β f ⋙ map α β g :=
  NatIso.ofComponents
    (fun x => mkIso ((Cat.Hom.toNatIso (F.mapComp f g)).app x.fst)
      ((Cat.Hom.toNatIso (G.mapComp f g)).app x.snd) (by
        simp [StrongTrans.naturality_comp_hom_app, StrongTrans.naturality_comp_inv_app]
        rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app]
        simp))
    (fun φ => by
      ext
      exacts [(F.mapComp f g).hom.toNatTrans.naturality φ.fst,
        (G.mapComp f g).hom.toNatTrans.naturality φ.snd])

section mapComp

variable (f : X ⟶ Y) (g : Y ⟶ Z) (x : (α.app X).toFunctor ⊡ (β.app X).toFunctor)

@[simp]
lemma mapComp_hom_app_fst :
    ((mapComp α β f g).hom.app x).fst = (F.mapComp f g).hom.toNatTrans.app x.fst :=
  rfl

@[simp]
lemma mapComp_hom_app_snd :
    ((mapComp α β f g).hom.app x).snd = (G.mapComp f g).hom.toNatTrans.app x.snd :=
  rfl

@[simp]
lemma mapComp_inv_app_fst :
    ((mapComp α β f g).inv.app x).fst = (F.mapComp f g).inv.toNatTrans.app x.fst :=
  rfl

@[simp]
lemma mapComp_inv_app_snd :
    ((mapComp α β f g).inv.app x).snd = (G.mapComp f g).inv.toNatTrans.app x.snd :=
  rfl

end mapComp

@[simp]
private lemma eqToHom_fst {A C D : Type*} [Category A] [Category C] [Category D]
    {L : A ⥤ D} {R : C ⥤ D} {x y : L ⊡ R} (h : x = y) :
    (eqToHom h).fst = eqToHom (congrArg CategoricalPullback.fst h) := by
  subst h
  rfl

@[simp]
private lemma eqToHom_snd {A C D : Type*} [Category A] [Category C] [Category D]
    {L : A ⥤ D} {R : C ⥤ D} {x y : L ⊡ R} (h : x = y) :
    (eqToHom h).snd = eqToHom (congrArg CategoricalPullback.snd h) := by
  subst h
  rfl

end fiberProduct

/-- The 2-fibre product of `α : F ⟶ H` and `β : G ⟶ H`. Its fibre over `X` is the categorical
pullback `(α.app X).toFunctor ⊡ (β.app X).toFunctor` (`fiberProduct_obj`), as the fibres of a
2-fibre product are the 2-fibre products of the fibres
([Stacks, Tag 02XI](https://stacks.math.columbia.edu/tag/02XI)); objectwise this is the 2-fibre
product in the (2,1)-category of categories
([Stacks, Tag 02X9](https://stacks.math.columbia.edu/tag/02X9)).

The pseudofunctors take values in `Cat.{v', max v' u'}`: an object of a categorical pullback
contains an isomorphism of the base, so the fibres of pseudofunctors into `Cat.{v', u'}` lie in
`Cat.{v', max v' u'}`, and the construction closes up only with that object universe. -/
def fiberProduct : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', max v' u'} :=
  pseudofunctorOfIsLocallyDiscrete
    (fun X => Cat.of ((α.app X).toFunctor ⊡ (β.app X).toFunctor))
    (fun f => (fiberProduct.map α β f).toCatHom)
    (fun X => Cat.Hom.isoMk (fiberProduct.mapId α β X))
    (fun f g => Cat.Hom.isoMk (fiberProduct.mapComp α β f g))
    (fun f g h => by
      apply Cat.Hom₂.ext
      ext x
      apply CategoricalPullback.hom_ext
      · simp
        rw [← F.map₂_associator_app]
        simp [Strict.associator_eqToIso, PrelaxFunctor.map₂_eqToHom]
      · simp
        rw [← G.map₂_associator_app]
        simp [Strict.associator_eqToIso, PrelaxFunctor.map₂_eqToHom])
    (fun f => by
      apply Cat.Hom₂.ext
      ext x
      apply CategoricalPullback.hom_ext
      · simp
        rw [← F.map₂_left_unitor_app]
        simp [Strict.leftUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom]
      · simp
        rw [← G.map₂_left_unitor_app]
        simp [Strict.leftUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom])
    (fun f => by
      apply Cat.Hom₂.ext
      ext x
      apply CategoricalPullback.hom_ext
      · simp
        rw [← F.map₂_right_unitor_app]
        simp [Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom]
      · simp
        rw [← G.map₂_right_unitor_app]
        simp [Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom])

@[simp]
lemma fiberProduct_obj (X : LocallyDiscrete B₀) :
    (fiberProduct α β).obj X = Cat.of ((α.app X).toFunctor ⊡ (β.app X).toFunctor) :=
  rfl

@[simp]
lemma fiberProduct_map {X Y : LocallyDiscrete B₀} (f : X ⟶ Y) :
    (fiberProduct α β).map f = (fiberProduct.map α β f).toCatHom :=
  rfl

@[simp]
lemma fiberProduct_mapId (X : LocallyDiscrete B₀) :
    (fiberProduct α β).mapId X = Cat.Hom.isoMk (fiberProduct.mapId α β X) :=
  rfl

@[simp]
lemma fiberProduct_mapComp {X Y Z : LocallyDiscrete B₀} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (fiberProduct α β).mapComp f g = Cat.Hom.isoMk (fiberProduct.mapComp α β f g) :=
  rfl

namespace fiberProduct

/-- Two-cells out of a fibre of the 2-fibre product agree when their components do. -/
private lemma hom₂_ext {X : LocallyDiscrete B₀} {C : Cat.{v', max v' u'}}
    {P Q : (fiberProduct α β).obj X ⟶ C} {η θ : P ⟶ Q}
    (h : ∀ x : (α.app X).toFunctor ⊡ (β.app X).toFunctor,
      η.toNatTrans.app x = θ.toNatTrans.app x) : η = θ :=
  Cat.Hom₂.ext (NatTrans.ext (funext h))

/-- The first projection of the 2-fibre product, `π₁` in each fibre. -/
@[simps]
def fst : fiberProduct α β ⟶ F where
  app X := (π₁ _ _).toCatHom
  naturality f := Iso.refl _
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id X := hom₂_ext α β fun x => by dsimp; simp
  naturality_comp f g := hom₂_ext α β fun x => by dsimp; simp

/-- The second projection of the 2-fibre product, `π₂` in each fibre. -/
@[simps]
def snd : fiberProduct α β ⟶ G where
  app X := (π₂ _ _).toCatHom
  naturality f := Iso.refl _
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id X := hom₂_ext α β fun x => by dsimp; simp
  naturality_comp f g := hom₂_ext α β fun x => by dsimp; simp

/-- The 2-commutativity isomorphism of the 2-fibre product, the canonical square of the
categorical pullback in each fibre. -/
@[simps!]
def comm : fst α β ≫ α ≅ snd α β ≫ β :=
  StrongTrans.isoMk
    (fun X => Cat.Hom.isoMk (catCommSq (α.app X).toFunctor (β.app X).toFunctor).iso)
    (fun f => hom₂_ext α β fun x => by simp)

section lift

variable {K : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', max v' u'}} (p : K ⟶ F) (q : K ⟶ G)
  (e : p ≫ α ≅ q ≫ β)

/-- Auxiliary definition for `lift`: its component over `X`, the functor `k ↦ (p k, q k, e k)`
into the categorical pullback. -/
def liftApp (X : LocallyDiscrete B₀) : K.obj X ⥤ (α.app X).toFunctor ⊡ (β.app X).toFunctor :=
  (CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
    { fst := (p.app X).toFunctor
      snd := (q.app X).toFunctor
      iso := Cat.Hom.toNatIso
        { hom := e.hom.as.app X
          inv := e.inv.as.app X
          hom_inv_id := congr($(e.hom_inv_id).as.app X)
          inv_hom_id := congr($(e.inv_hom_id).as.app X) } }

section liftApp

variable (X : LocallyDiscrete B₀) (k : K.obj X)

@[simp]
lemma liftApp_obj_fst : ((liftApp α β p q e X).obj k).fst = (p.app X).toFunctor.obj k := rfl

@[simp]
lemma liftApp_obj_snd : ((liftApp α β p q e X).obj k).snd = (q.app X).toFunctor.obj k := rfl

@[simp]
lemma liftApp_obj_iso_hom :
    ((liftApp α β p q e X).obj k).iso.hom = (e.hom.as.app X).toNatTrans.app k := rfl

@[simp]
lemma liftApp_obj_iso_inv :
    ((liftApp α β p q e X).obj k).iso.inv = (e.inv.as.app X).toNatTrans.app k := rfl

@[simp]
lemma liftApp_map_fst {k k' : K.obj X} (φ : k ⟶ k') :
    ((liftApp α β p q e X).map φ).fst = (p.app X).toFunctor.map φ := rfl

@[simp]
lemma liftApp_map_snd {k k' : K.obj X} (φ : k ⟶ k') :
    ((liftApp α β p q e X).map φ).snd = (q.app X).toFunctor.map φ := rfl

end liftApp

/-- Auxiliary definition for `lift`: its naturality isomorphisms, given by those of `p` and `q`
in the two components. -/
def liftNaturality {X Y : LocallyDiscrete B₀} (f : X ⟶ Y) :
    (K.map f).toFunctor ⋙ liftApp α β p q e Y ≅ liftApp α β p q e X ⋙ map α β f :=
  NatIso.ofComponents
    (fun k => mkIso ((Cat.Hom.toNatIso (p.naturality f)).app k)
      ((Cat.Hom.toNatIso (q.naturality f)).app k) (by
        have h := congr($(e.hom.as.naturality f).toNatTrans.app k)
        simp at h
        simp [← reassoc_of% h]))
    (fun φ => by
      apply CategoricalPullback.hom_ext
      exacts [(p.naturality f).hom.toNatTrans.naturality φ,
        (q.naturality f).hom.toNatTrans.naturality φ])

section liftNaturality

variable {X Y : LocallyDiscrete B₀} (f : X ⟶ Y) (k : K.obj X)

@[simp]
lemma liftNaturality_hom_app_fst :
    ((liftNaturality α β p q e f).hom.app k).fst = (p.naturality f).hom.toNatTrans.app k := rfl

@[simp]
lemma liftNaturality_hom_app_snd :
    ((liftNaturality α β p q e f).hom.app k).snd = (q.naturality f).hom.toNatTrans.app k := rfl

@[simp]
lemma liftNaturality_inv_app_fst :
    ((liftNaturality α β p q e f).inv.app k).fst = (p.naturality f).inv.toNatTrans.app k := rfl

@[simp]
lemma liftNaturality_inv_app_snd :
    ((liftNaturality α β p q e f).inv.app k).snd = (q.naturality f).inv.toNatTrans.app k := rfl

end liftNaturality

/-- The lift of a 2-commutative square `(p, q, e)` into the 2-fibre product, sending `k` to
`(p k, q k, e k)` in each fibre. -/
def lift : K ⟶ fiberProduct α β where
  app X := (liftApp α β p q e X).toCatHom
  naturality f := Cat.Hom.isoMk (liftNaturality α β p q e f)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id X := by
    apply Cat.Hom₂.ext
    ext k
    apply CategoricalPullback.hom_ext
    · simp [StrongTrans.naturality_id_hom_app]
    · simp [StrongTrans.naturality_id_hom_app]
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext k
    apply CategoricalPullback.hom_ext
    · simp [StrongTrans.naturality_comp_hom_app]
    · simp [StrongTrans.naturality_comp_hom_app]

@[simp]
lemma lift_app (X : LocallyDiscrete B₀) :
    (lift α β p q e).app X = (liftApp α β p q e X).toCatHom :=
  rfl

@[simp]
lemma lift_naturality {X Y : LocallyDiscrete B₀} (f : X ⟶ Y) :
    (lift α β p q e).naturality f = Cat.Hom.isoMk (liftNaturality α β p q e f) :=
  rfl

/-- The first projection of `lift` is `p`. -/
@[simps!]
def liftFst : lift α β p q e ≫ fst α β ≅ p :=
  StrongTrans.isoMk (fun _ => Iso.refl _) (fun f => by
    apply Cat.Hom₂.ext
    ext k
    simp)

/-- The second projection of `lift` is `q`. -/
@[simps!]
def liftSnd : lift α β p q e ≫ snd α β ≅ q :=
  StrongTrans.isoMk (fun _ => Iso.refl _) (fun f => by
    apply Cat.Hom₂.ext
    ext k
    simp)

/-- `liftFst`, `comm` and `liftSnd` recover the 2-commutative square `e`. -/
theorem lift_comm :
    (liftFst α β p q e).inv ▷ α ≫ (α_ _ _ _).hom ≫
      lift α β p q e ◁ (comm α β).hom ≫ (α_ _ _ _).inv ≫
        (liftSnd α β p q e).hom ▷ β = e.hom := by
  ext X k
  simp

end lift

/-- The fibres of the 2-fibre product are groupoids when those of `F` and `G` are; nothing is
required of `H`. -/
instance isGroupoid_obj [∀ X, IsGroupoid (F.obj X)] [∀ X, IsGroupoid (G.obj X)]
    (X : LocallyDiscrete B₀) : IsGroupoid ((fiberProduct α β).obj X) where
  all_isIso φ := (CategoricalPullback.isIso_iff (f := φ)).mpr
    ⟨IsGroupoid.all_isIso _, IsGroupoid.all_isIso _⟩

end fiberProduct

/-- The relative diagonal `F ⟶ F ×_H F` of `α : F ⟶ H`. -/
def diagonal : F ⟶ fiberProduct α α :=
  fiberProduct.lift α α (𝟙 F) (𝟙 F) (Iso.refl _)

end FiberProduct

section Terminal

variable (B₀ : Type u) [Category.{v} B₀]

/-- The constant pseudofunctor at the chosen terminal category of `Cat.{v', u'}`. -/
def terminal : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'} :=
  ((Functor.const B₀).obj Cat.chosenTerminal.{v', u'}).toPseudofunctor'

variable {B₀}

/-- The strong transformation from `F` to `terminal B₀`, the unique functor to the terminal
category in each fibre. -/
def toTerminal (F : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'}) : F ⟶ terminal B₀ where
  app X := Cat.chosenTerminalIsTerminal.from (F.obj X)
  naturality f := Iso.refl _
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id X := by
    apply Cat.Hom₂.ext
    ext k
    rfl
  naturality_comp f g := by
    apply Cat.Hom₂.ext
    ext k
    rfl

end Terminal

end CategoryTheory.Pseudofunctor
