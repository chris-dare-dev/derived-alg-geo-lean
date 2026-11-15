/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Groupoid
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Transport

/-!
# Universe lifts of Cat-valued pseudofunctors

A Cat-valued pseudofunctor `F` on a locally discrete bicategory has a universe lift
`F.ulift.{w₁, w₂}` whose fibre over `X` is `ULiftHom.{w₁} (ULift.{w₂} (F.obj X))`.
`ULift.{w₂}` raises the object universe and keeps the morphisms; `ULiftHom.{w₁}` raises the
morphism universe. Together they move the fibres from `Cat.{v', u'}` to
`Cat.{max v' w₁, max u' w₂}`, with the two universes raised independently.

## Main definitions

* `CategoryTheory.Pseudofunctor.ulift`: the universe lift of a pseudofunctor
  `LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'}`.
* `CategoryTheory.Pseudofunctor.ulift.objEquivalence`: the equivalence between a fibre of `F`
  and the corresponding fibre of `F.ulift`.

## Main results

* `CategoryTheory.Pseudofunctor.ulift.isGroupoid_obj` and
  `CategoryTheory.Pseudofunctor.ulift.isDiscrete_obj`: the lift has groupoid (discrete) fibres
  where `F` does.
* `CategoryTheory.Pseudofunctor.ulift.mapComp'_hom_app`: the compositors of the lift are those
  of `F`, lifted along `CategoryTheory.Pseudofunctor.ulift.objEquivalence`.

## Implementation notes

The transition functors, compositors and unitors of the lift are those of `F` transported
through Mathlib's fibrewise equivalences `ULiftHomULiftCategory.equiv`, which are
`ULift.equivalence.trans ULiftHom.equiv`, with
`Pseudofunctor.equivalenceTransportFunctor` and its coherence theorems. The compositors are
first transported for an arbitrary composite, as `Pseudofunctor.mapComp'` does, so that the
pseudofunctor equations of `LocallyDiscrete.mkPseudofunctor`, which compare different
bracketings of a composite, reduce to the transported coherence theorems.

Mathlib's `uliftCategory` is only a local instance here, as in Mathlib.
`Cat.asSmallFunctor` is not used: it raises both universes to the same level.

## References

[Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W): equivalences of fibred
categories transport the fibred structure.

## Tags

pseudofunctor, universe lift, ULift
-/

namespace CategoryTheory.Pseudofunctor

open Bicategory

noncomputable section

universe w₁ w₂ v' u' v u

attribute [local instance] uliftCategory

section

variable (C : Type u') [Category.{v'} C]

@[simp]
private lemma equiv_inverse_obj_functor_obj (X : C) :
    (ULiftHomULiftCategory.equiv.{w₁, w₂} C).inverse.obj
      ((ULiftHomULiftCategory.equiv.{w₁, w₂} C).functor.obj X) = X :=
  rfl

@[simp]
private lemma equiv_functor_obj_inverse_obj (X : ULiftHom.{w₁} (ULift.{w₂} C)) :
    (ULiftHomULiftCategory.equiv.{w₁, w₂} C).functor.obj
      ((ULiftHomULiftCategory.equiv.{w₁, w₂} C).inverse.obj X) = X :=
  rfl

@[simp]
private lemma equiv_inverse_map_functor_map {X Y : C} (f : X ⟶ Y) :
    (ULiftHomULiftCategory.equiv.{w₁, w₂} C).inverse.map
      ((ULiftHomULiftCategory.equiv.{w₁, w₂} C).functor.map f) = f :=
  rfl

@[simp]
private lemma equiv_inverse_map_id (X : C) :
    (ULiftHomULiftCategory.equiv.{w₁, w₂} C).inverse.map
      (𝟙 ((ULiftHomULiftCategory.equiv.{w₁, w₂} C).functor.obj X)) = 𝟙 X :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
private lemma equiv_unitIso_hom_app (X : C) :
    (ULiftHomULiftCategory.equiv.{w₁, w₂} C).unitIso.hom.app X = 𝟙 X := by
  simp [ULiftHomULiftCategory.equiv, ULiftHom.equiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
private lemma equiv_unitIso_inv_app (X : C) :
    (ULiftHomULiftCategory.equiv.{w₁, w₂} C).unitIso.inv.app X = 𝟙 X := by
  simp [ULiftHomULiftCategory.equiv, ULiftHom.equiv]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
@[simp]
private lemma equiv_counitIso_hom_app (X : ULiftHom.{w₁} (ULift.{w₂} C)) :
    (ULiftHomULiftCategory.equiv.{w₁, w₂} C).counitIso.hom.app X = 𝟙 X := by
  simp [ULiftHomULiftCategory.equiv, ULiftHom.equiv]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
private lemma equiv_counitIso_inv_app (X : ULiftHom.{w₁} (ULift.{w₂} C)) :
    (ULiftHomULiftCategory.equiv.{w₁, w₂} C).counitIso.inv.app X = 𝟙 X := by
  simp [ULiftHomULiftCategory.equiv, ULiftHom.equiv]
  rfl

end

variable {B₀ : Type u} [Category.{v} B₀] (F : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'})

namespace ulift

/-- The transition functor of the lift along a morphism of the base. -/
abbrev map {b b' : B₀} (f : b ⟶ b') :
    ULiftHom.{w₁} (ULift.{w₂} (F.obj ⟨b⟩)) ⥤ ULiftHom.{w₁} (ULift.{w₂} (F.obj ⟨b'⟩)) :=
  equivalenceTransportFunctor (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b⟩))
    (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b'⟩)) (F.map f.toLoc).toFunctor

/-- The unitor of the lift, transported from `F.mapId`. -/
def mapIdIso (b : B₀) :
    map.{w₁, w₂} F (𝟙 b) ≅ 𝟭 (ULiftHom.{w₁} (ULift.{w₂} (F.obj ⟨b⟩))) :=
  equivalenceTransportIdIso (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b⟩))
    (F.map (𝟙 _)).toFunctor (𝟭 _) (Cat.Hom.toNatIso (F.mapId ⟨b⟩)) (Iso.refl _)

/-- The compositor of the lift for an arbitrary composite, transported from
`Pseudofunctor.mapComp'`. -/
def mapCompIso {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg) :
    map.{w₁, w₂} F fg ≅ map.{w₁, w₂} F f ⋙ map.{w₁, w₂} F g :=
  (equivalenceTransportCompIso (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b₀⟩))
    (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b₁⟩))
    (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b₂⟩))
    (F.map f.toLoc).toFunctor (F.map g.toLoc).toFunctor (F.map fg.toLoc).toFunctor
    (Cat.Hom.toNatIso (F.mapComp' f.toLoc g.toLoc fg.toLoc (by rw [← h]; rfl))).symm).symm

set_option backward.isDefEq.respectTransparency false in
/-- The components of the transported compositor are those of `Pseudofunctor.mapComp'`. -/
theorem mapCompIso_hom_app {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg) (x : ULiftHom.{w₁} (ULift.{w₂} (F.obj ⟨b₀⟩))) :
    (mapCompIso.{w₁, w₂} F f g fg h).hom.app x =
      (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b₂⟩)).functor.map
        ((F.mapComp' f.toLoc g.toLoc fg.toLoc (by rw [← h]; rfl)).hom.toNatTrans.app
          ((ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b₀⟩)).inverse.obj x)) := by
  apply (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b₂⟩)).inverse.map_injective
  dsimp only [mapCompIso, equivalenceTransportCompIso, _root_.id]
  simp [Cat.Hom.toNatIso]

set_option backward.isDefEq.respectTransparency false in
/-- The components of the inverse transported compositor are those of
`Pseudofunctor.mapComp'`. -/
theorem mapCompIso_inv_app {b₀ b₁ b₂ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (fg : b₀ ⟶ b₂)
    (h : f ≫ g = fg) (x : ULiftHom.{w₁} (ULift.{w₂} (F.obj ⟨b₀⟩))) :
    (mapCompIso.{w₁, w₂} F f g fg h).inv.app x =
      (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b₂⟩)).functor.map
        ((F.mapComp' f.toLoc g.toLoc fg.toLoc (by rw [← h]; rfl)).inv.toNatTrans.app
          ((ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b₀⟩)).inverse.obj x)) := by
  apply (ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj ⟨b₂⟩)).inverse.map_injective
  dsimp only [mapCompIso, equivalenceTransportCompIso, _root_.id]
  simp [Cat.Hom.toNatIso]
  exact Category.id_comp _

set_option backward.isDefEq.respectTransparency false in
/-- The transported compositors satisfy the pentagon equation of
`LocallyDiscrete.mkPseudofunctor`, for any two bracketings `fgh` and `fgh'` of a triple
composite. This is `Pseudofunctor.equivalenceTransport_associativity`. -/
theorem mapCompIso_associativity {b₀ b₁ b₂ b₃ : B₀} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
    (h : b₂ ⟶ b₃) (fg : b₀ ⟶ b₂) (gh : b₁ ⟶ b₃) (fgh fgh' : b₀ ⟶ b₃)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh) (hfgh : fg ≫ h = fgh) (hfgh' : f ≫ gh = fgh')
    (e : fgh = fgh') :
    (Cat.Hom.isoMk (mapCompIso.{w₁, w₂} F fg h fgh hfgh)).hom ≫
        (Cat.Hom.isoMk (mapCompIso.{w₁, w₂} F f g fg hfg)).hom ▷ (map F h).toCatHom ≫
        (α_ (map F f).toCatHom (map F g).toCatHom (map F h).toCatHom).hom ≫
        (map F f).toCatHom ◁ (Cat.Hom.isoMk (mapCompIso.{w₁, w₂} F g h gh hgh)).inv ≫
        (Cat.Hom.isoMk (mapCompIso.{w₁, w₂} F f gh fgh' hfgh')).inv =
      eqToHom (by rw [e]) := by
  subst e
  rw [eqToHom_refl]
  apply Cat.Hom₂.ext
  refine equivalenceTransport_associativity _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_
  have := F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight f.toLoc g.toLoc h.toLoc fg.toLoc
    gh.toLoc fgh.toLoc (by rw [← hfg]; rfl) (by rw [← hgh]; rfl) (by rw [← hfgh]; rfl)
  apply NatTrans.ext
  funext x
  have hx := congrArg (fun η ↦ η.toNatTrans.app x) this
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app] at hx
  simp [Cat.Hom.toNatIso, reassoc_of% hx]

set_option backward.isDefEq.respectTransparency false in
/-- The transported unitor and compositor satisfy the left triangle equation. This is
`Pseudofunctor.equivalenceTransport_leftUnitality`. -/
theorem mapCompIso_leftUnitality {b₀ b₁ : B₀} (f f' : b₀ ⟶ b₁) (hf : 𝟙 b₀ ≫ f = f')
    (e : f' = f) :
    (Cat.Hom.isoMk (mapCompIso.{w₁, w₂} F (𝟙 b₀) f f' hf)).hom ≫
        (Cat.Hom.isoMk (mapIdIso.{w₁, w₂} F b₀)).hom ▷ (map F f).toCatHom ≫
        (λ_ (map F f).toCatHom).hom =
      eqToHom (by rw [e]) := by
  subst e
  rw [eqToHom_refl]
  apply Cat.Hom₂.ext
  refine equivalenceTransport_leftUnitality _ _ _ _ _ _ _ _ ?_
  apply NatTrans.ext
  funext x
  simp [Cat.Hom.toNatIso, mapComp'_id_comp_hom_app, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The transported unitor and compositor satisfy the right triangle equation. This is
`Pseudofunctor.equivalenceTransport_rightUnitality`. -/
theorem mapCompIso_rightUnitality {b₀ b₁ : B₀} (f f' : b₀ ⟶ b₁) (hf : f ≫ 𝟙 b₁ = f')
    (e : f' = f) :
    (Cat.Hom.isoMk (mapCompIso.{w₁, w₂} F f (𝟙 b₁) f' hf)).hom ≫
        (map F f).toCatHom ◁ (Cat.Hom.isoMk (mapIdIso.{w₁, w₂} F b₁)).hom ≫
        (ρ_ (map F f).toCatHom).hom =
      eqToHom (by rw [e]) := by
  subst e
  rw [eqToHom_refl]
  apply Cat.Hom₂.ext
  refine equivalenceTransport_rightUnitality _ _ _ _ _ _ _ _ ?_
  apply NatTrans.ext
  funext x
  simp only [Cat.Hom.toNatIso]
  simp
  rw [mapComp'_comp_id_hom_app, Cat.Hom.inv_hom_id_toNatTrans_app]
  rfl

end ulift

/-- The universe lift of a Cat-valued pseudofunctor on a locally discrete bicategory. Its fibre
over `X` is `ULiftHom.{w₁} (ULift.{w₂} (F.obj X))`, in `Cat.{max v' w₁, max u' w₂}`: `w₁`
raises the morphism universe and `w₂` the object universe, independently. -/
def ulift : LocallyDiscrete B₀ ⥤ᵖ Cat.{max v' w₁, max u' w₂} :=
  LocallyDiscrete.mkPseudofunctor
    (fun b ↦ Cat.of (ULiftHom.{w₁} (ULift.{w₂} (F.obj ⟨b⟩))))
    (fun f ↦ (ulift.map.{w₁, w₂} F f).toCatHom)
    (fun b ↦ Cat.Hom.isoMk (ulift.mapIdIso.{w₁, w₂} F b))
    (fun f g ↦ Cat.Hom.isoMk (ulift.mapCompIso.{w₁, w₂} F f g _ rfl))
    (fun f g h ↦ ulift.mapCompIso_associativity F f g h _ _ _ _ rfl rfl rfl rfl
      (Category.assoc f g h))
    (fun f ↦ ulift.mapCompIso_leftUnitality F f _ rfl (Category.id_comp f))
    (fun f ↦ ulift.mapCompIso_rightUnitality F f _ rfl (Category.comp_id f))

namespace ulift

/-- A fibre of `F` is equivalent to the corresponding fibre of `F.ulift`. -/
def objEquivalence (X : LocallyDiscrete B₀) : F.obj X ≌ (F.ulift.{w₁, w₂}).obj X :=
  ULiftHomULiftCategory.equiv.{w₁, w₂} (F.obj X)

/-- The lift has groupoid fibres where `F` does. -/
instance isGroupoid_obj (X : LocallyDiscrete B₀) [IsGroupoid (F.obj X)] :
    IsGroupoid ((F.ulift.{w₁, w₂}).obj X) :=
  isGroupoid_of_reflects_iso (objEquivalence.{w₁, w₂} F X).inverse

/-- The lift has discrete fibres where `F` does. -/
instance isDiscrete_obj (X : LocallyDiscrete B₀) [IsDiscrete (F.obj X)] :
    IsDiscrete ((F.ulift.{w₁, w₂}).obj X) where
  subsingleton _ _ :=
    ⟨fun _ _ ↦ (objEquivalence.{w₁, w₂} F X).inverse.map_injective (Subsingleton.elim _ _)⟩
  eq_of_hom φ := congrArg (objEquivalence.{w₁, w₂} F X).functor.obj
    (IsDiscrete.eq_of_hom ((objEquivalence.{w₁, w₂} F X).inverse.map φ))

/-- `CategoryTheory.Pseudofunctor.ulift.objEquivalence` is strictly invertible on objects. -/
@[simp]
lemma objEquivalence_inverse_obj_functor_obj (X : LocallyDiscrete B₀) (x : F.obj X) :
    (objEquivalence.{w₁, w₂} F X).inverse.obj ((objEquivalence.{w₁, w₂} F X).functor.obj x) =
      x :=
  rfl

/-- `CategoryTheory.Pseudofunctor.ulift.objEquivalence` is strictly invertible on objects. -/
@[simp]
lemma objEquivalence_functor_obj_inverse_obj (X : LocallyDiscrete B₀)
    (x : (F.ulift.{w₁, w₂}).obj X) :
    (objEquivalence.{w₁, w₂} F X).functor.obj ((objEquivalence.{w₁, w₂} F X).inverse.obj x) =
      x :=
  rfl

/-- `CategoryTheory.Pseudofunctor.ulift.objEquivalence` is strictly invertible on morphisms. -/
@[simp]
lemma objEquivalence_inverse_map_functor_map (X : LocallyDiscrete B₀) {x y : F.obj X}
    (φ : x ⟶ y) :
    (objEquivalence.{w₁, w₂} F X).inverse.map ((objEquivalence.{w₁, w₂} F X).functor.map φ) =
      φ :=
  rfl

/-- `CategoryTheory.Pseudofunctor.ulift.objEquivalence` is strictly invertible on morphisms. -/
@[simp]
lemma objEquivalence_functor_map_inverse_map (X : LocallyDiscrete B₀)
    {x y : (F.ulift.{w₁, w₂}).obj X} (φ : x ⟶ y) :
    (objEquivalence.{w₁, w₂} F X).functor.map ((objEquivalence.{w₁, w₂} F X).inverse.map φ) =
      φ :=
  rfl

/-- The transition functors of `F.ulift` are those of `F`, conjugated by
`CategoryTheory.Pseudofunctor.ulift.objEquivalence`. -/
lemma map_toFunctor {X Y : LocallyDiscrete B₀} (f : X ⟶ Y) :
    ((F.ulift.{w₁, w₂}).map f).toFunctor =
      (objEquivalence.{w₁, w₂} F X).inverse ⋙ (F.map f).toFunctor ⋙
        (objEquivalence.{w₁, w₂} F Y).functor :=
  rfl

/-- The transition functors of `F.ulift` on objects. -/
@[simp]
lemma map_toFunctor_obj {X Y : LocallyDiscrete B₀} (f : X ⟶ Y) (x : (F.ulift.{w₁, w₂}).obj X) :
    ((F.ulift.{w₁, w₂}).map f).toFunctor.obj x =
      (objEquivalence.{w₁, w₂} F Y).functor.obj
        ((F.map f).toFunctor.obj ((objEquivalence.{w₁, w₂} F X).inverse.obj x)) :=
  rfl

/-- The transition functors of `F.ulift` on morphisms. -/
@[simp]
lemma map_toFunctor_map {X Y : LocallyDiscrete B₀} (f : X ⟶ Y)
    {x y : (F.ulift.{w₁, w₂}).obj X} (φ : x ⟶ y) :
    ((F.ulift.{w₁, w₂}).map f).toFunctor.map φ =
      (objEquivalence.{w₁, w₂} F Y).functor.map
        ((F.map f).toFunctor.map ((objEquivalence.{w₁, w₂} F X).inverse.map φ)) :=
  rfl

/-- The compositors of `F.ulift`, for an arbitrary composite, are those of `F` lifted
along `CategoryTheory.Pseudofunctor.ulift.objEquivalence`. -/
@[simp]
lemma mapComp'_hom_app {X Y Z : LocallyDiscrete B₀} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (F.ulift.{w₁, w₂}).obj X) :
    ((F.ulift.{w₁, w₂}).mapComp' f g fg h).hom.toNatTrans.app x =
      (objEquivalence.{w₁, w₂} F Z).functor.map
        ((F.mapComp' f g fg h).hom.toNatTrans.app
          ((objEquivalence.{w₁, w₂} F X).inverse.obj x)) := by
  subst h
  rw [(F.ulift.{w₁, w₂}).mapComp'_eq_mapComp f g]
  exact mapCompIso_hom_app F f.as g.as _ rfl x

/-- The inverse compositors of `F.ulift`, for an arbitrary composite, are those of `F`
lifted along `CategoryTheory.Pseudofunctor.ulift.objEquivalence`. -/
@[simp]
lemma mapComp'_inv_app {X Y Z : LocallyDiscrete B₀} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (h : f ≫ g = fg) (x : (F.ulift.{w₁, w₂}).obj X) :
    ((F.ulift.{w₁, w₂}).mapComp' f g fg h).inv.toNatTrans.app x =
      (objEquivalence.{w₁, w₂} F Z).functor.map
        ((F.mapComp' f g fg h).inv.toNatTrans.app
          ((objEquivalence.{w₁, w₂} F X).inverse.obj x)) := by
  subst h
  rw [(F.ulift.{w₁, w₂}).mapComp'_eq_mapComp f g]
  exact mapCompIso_inv_app F f.as g.as _ rfl x

end ulift

end

end CategoryTheory.Pseudofunctor
