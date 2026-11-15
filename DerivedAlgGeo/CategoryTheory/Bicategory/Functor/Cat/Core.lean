/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Core

/-!
# The core of a Cat-valued pseudofunctor

Given a pseudofunctor `F : LocallyDiscrete B₀ ⥤ᵖ Cat`, this file builds its core
`F.core`, the pseudofunctor whose fibre over `X` is the core `Core (F.obj X)`, the maximal
groupoid of `F.obj X`. The transition functors are the cores `Functor.core` of those of `F`,
and its unitor and compositor are the cores `Iso.core` of those of `F`.

## Main definitions

* `CategoryTheory.Pseudofunctor.core F`: the core of `F`.
* `CategoryTheory.Pseudofunctor.coreι F : F.core ⟶ F`: the inclusion, `Core.inclusion` in
  each fibre.

## Main results

* The fibres of `F.core` are groupoids (`Pseudofunctor.core_obj_isGroupoid`).

## Implementation notes

The base is locally discrete, so the core needs no action on 2-cells of the base: over a base
with non-invertible 2-cells, `map₂` would not descend to cores. The construction goes through
`pseudofunctorOfIsLocallyDiscrete` directly, rather than through a `Grpd`-valued pseudofunctor
followed by a forgetful map, so the fibres are definitionally `Cat.of (Core (F.obj X))`.

The naturality isomorphisms of `coreι` are identities: `F.map f` applied to the inclusion of
the core is the inclusion applied to the core of `F.map f` (`Functor.coreCompInclusionIso`).

## References

* [Stacks, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z): the category fibred in
  groupoids associated to a fibred category.

## Tags

core, groupoid, pseudofunctor, Cat
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u v' u'

namespace CategoryTheory.Pseudofunctor

open Bicategory
open scoped StrongTrans

@[simp]
private lemma _root_.CategoryTheory.Core.eqToHom_iso_hom {C : Type*} [Category* C] {x y : Core C}
    (h : x = y) : (eqToHom h).iso.hom = eqToHom (congrArg Core.of h) := by
  subst h
  rfl

variable {B₀ : Type u} [Category.{v} B₀] (F : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'})

/-- The core of a Cat-valued pseudofunctor on a locally discrete base: its fibre over `X` is
the maximal groupoid `Core (F.obj X)` (`core_obj`), its transition functors are the cores of
those of `F`, and its unitor and compositor are the cores of those of `F`. -/
def core : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'} :=
  pseudofunctorOfIsLocallyDiscrete
    (fun X => Cat.of (Core (F.obj X)))
    (fun f => (F.map f).toFunctor.core.toCatHom)
    (fun X => Cat.Hom.isoMk (Iso.core (Cat.Hom.toNatIso (F.mapId X))))
    (fun f g => Cat.Hom.isoMk (Iso.core (Cat.Hom.toNatIso (F.mapComp f g))))
    (fun f g h => by
      apply Cat.Hom₂.ext
      ext x
      apply Core.hom_ext
      simp
      rw [← F.map₂_associator_app]
      simp [Strict.associator_eqToIso, PrelaxFunctor.map₂_eqToHom])
    (fun f => by
      apply Cat.Hom₂.ext
      ext x
      apply Core.hom_ext
      simp
      rw [← F.map₂_left_unitor_app]
      simp [Strict.leftUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom])
    (fun f => by
      apply Cat.Hom₂.ext
      ext x
      apply Core.hom_ext
      simp
      rw [← F.map₂_right_unitor_app]
      simp [Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom])

@[simp]
lemma core_obj (X : LocallyDiscrete B₀) : F.core.obj X = Cat.of (Core (F.obj X)) :=
  rfl

@[simp]
lemma core_map {X Y : LocallyDiscrete B₀} (f : X ⟶ Y) :
    F.core.map f = (F.map f).toFunctor.core.toCatHom :=
  rfl

@[simp]
lemma core_mapId (X : LocallyDiscrete B₀) :
    F.core.mapId X = Cat.Hom.isoMk (Iso.core (Cat.Hom.toNatIso (F.mapId X))) :=
  rfl

@[simp]
lemma core_mapComp {X Y Z : LocallyDiscrete B₀} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.core.mapComp f g = Cat.Hom.isoMk (Iso.core (Cat.Hom.toNatIso (F.mapComp f g))) :=
  rfl

/-- The compositors `mapComp'` of the core are the cores of those of `F`. -/
@[simp]
lemma core_mapComp'_hom_toNatTrans_app_iso_hom {X Y Z : LocallyDiscrete B₀} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) (M : Core (F.obj X)) :
    ((F.core.mapComp' f g fg h).hom.toNatTrans.app M).iso.hom =
      (F.mapComp' f g fg h).hom.toNatTrans.app M.of := by
  subst h
  simp [mapComp'_eq_mapComp]

@[simp]
lemma core_mapComp'_inv_toNatTrans_app_iso_hom {X Y Z : LocallyDiscrete B₀} (f : X ⟶ Y)
    (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg) (M : Core (F.obj X)) :
    ((F.core.mapComp' f g fg h).inv.toNatTrans.app M).iso.hom =
      (F.mapComp' f g fg h).inv.toNatTrans.app M.of := by
  subst h
  simp [mapComp'_eq_mapComp]

/-- The fibres of the core are groupoids. -/
instance core_obj_isGroupoid (X : LocallyDiscrete B₀) : IsGroupoid (F.core.obj X) :=
  inferInstanceAs (IsGroupoid (Core (F.obj X)))

/-- Two-cells out of a fibre of the core agree when their components do. -/
private lemma core_hom₂_ext {X : LocallyDiscrete B₀} {C : Cat.{v', u'}}
    {P Q : F.core.obj X ⟶ C} {η θ : P ⟶ Q}
    (h : ∀ x : Core (F.obj X), η.toNatTrans.app x = θ.toNatTrans.app x) : η = θ :=
  Cat.Hom₂.ext (NatTrans.ext (funext h))

/-- The inclusion of the core of `F` into `F`: `Core.inclusion` in each fibre, with identity
naturality isomorphisms. -/
@[simps]
def coreι : F.core ⟶ F where
  app X := (Core.inclusion (F.obj X)).toCatHom
  naturality f := Iso.refl _
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    obtain rfl : η = 𝟙 _ := Subsingleton.elim _ _
    simp
  naturality_id X := core_hom₂_ext F fun x => by dsimp; simp
  naturality_comp f g := core_hom₂_ext F fun x => by dsimp; simp

end CategoryTheory.Pseudofunctor
