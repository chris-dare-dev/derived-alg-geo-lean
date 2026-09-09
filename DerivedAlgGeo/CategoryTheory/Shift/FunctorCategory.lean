/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Shift.CommShift

/-!
# The pointwise shift on a functor category

A shift on `Y` induces one on `X ⥤ Y`, by postcomposition: `G⟦n⟧ = G ⋙ Y⟦n⟧`.
Mathlib does not carry this instance at the pinned revision, and this file adds
it.

## Why the construction is short

Every comparison the shift needs is already an identity of functors in Mathlib,
not merely an isomorphism: `whiskeringRight_obj_id` and
`whiskeringRight_obj_comp` are both `rfl`.  So the `zero` and `add` isomorphisms
are the images of `shiftFunctorZero Y` and `shiftFunctorAdd Y` under
`whiskeringRight`, with no transport, and the three coherence axioms of
`ShiftMkCore` reduce componentwise to their counterparts on `Y`.

## The evaluation functors commute with the shift on the nose

`(evaluation X Y).obj E` sends `G` to `G.obj E`, so it sends `G ⋙ Y⟦n⟧` to
`(G.obj E)⟦n⟧`: the two sides of its commutation isomorphism are equal, and
`Iso.refl` is a `CommShift` structure for it.  This is what lets a functor
`K ⥤ (X ⥤ Y)` that commutes with the shift be evaluated at a source object and
still commute with the shift, by Mathlib's composition instance alone.

## Naturality of a whole family, for free

A family of functors `F : K ⥤ (X ⥤ Y)` equipped with `F.CommShift A` carries
one isomorphism `shiftFunctor K n ⋙ F ≅ F ⋙ shiftFunctor (X ⥤ Y) n` in the
functor category, so its components at a source object are natural in that
object by construction, and the zero and addition laws are Mathlib's.

`Triangulated/ExactFunctorFamily.lean` currently stores that datum by hand, as
an evaluated `CommShift` for every source object together with a separate
naturality axiom and no zero or addition law.  This instance is what such a
family should be built on instead.  The rewiring is *not* done here, and it is
not an API-only change: `Functor.ExactBifunctor` records triangulatedness of
`F.flip.obj B` against the shift structure it chose, whereas the family needs
it for `F ⋙ evaluation K' Y B` against that choice composed with the strict
comparison below.  The two functors are definitionally equal and the two
structures agree up to identity morphisms, so the transport is true; it needs
a comparison lemma between the two `mapTriangle`s, which is a separate step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v v' w u u'

namespace CategoryTheory

open Category Functor

variable (X : Type u) [Category.{v} X] (Y : Type u') [Category.{v'} Y]
  (A : Type w) [AddMonoid A] [HasShift Y A]

/-- The pointwise shift on `X ⥤ Y`: shifting by `n` is postcomposition with
`Y⟦n⟧`.

The three coherence fields are the coherences of the shift on `Y`, applied at
`G.obj E`; the whiskering comparisons contribute nothing because they are
identities. -/
def functorCategoryShiftMkCore : ShiftMkCore (X ⥤ Y) A where
  F n := (whiskeringRight X Y Y).obj (shiftFunctor Y n)
  zero := (whiskeringRight X Y Y).mapIso (shiftFunctorZero Y A)
  add n m := (whiskeringRight X Y Y).mapIso (shiftFunctorAdd Y n m)
  assoc_hom_app m₁ m₂ m₃ G := by
    ext E
    simp only [NatTrans.comp_app, eqToHom_app]
    rw [← Category.assoc]
    have h := shiftFunctorAdd_assoc_hom_app (C := Y) m₁ m₂ m₃ (G.obj E)
    simp only [shiftFunctorAdd', Iso.trans_hom, NatTrans.comp_app, eqToIso.hom,
      eqToHom_app] at h
    exact h
  zero_add_hom_app n G := by
    ext E
    rw [NatTrans.comp_app, eqToHom_app]
    exact shiftFunctorAdd_zero_add_hom_app (C := Y) n (G.obj E)
  add_zero_hom_app n G := by
    ext E
    rw [NatTrans.comp_app, eqToHom_app]
    exact shiftFunctorAdd_add_zero_hom_app (C := Y) n (G.obj E)

/-- **A functor category inherits the shift of its target, pointwise.** -/
instance functorCategoryHasShift : HasShift (X ⥤ Y) A :=
  hasShiftMk _ _ (functorCategoryShiftMkCore X Y A)

variable {X Y A}

@[simp]
lemma functorCategory_shiftFunctor_obj (n : A) (G : X ⥤ Y) :
    (shiftFunctor (X ⥤ Y) n).obj G = G ⋙ shiftFunctor Y n :=
  rfl

-- Not `@[simp]`: `functorCategory_shiftFunctor_obj` already rewrites the
-- left-hand side, so this one is stated for `rw` and for readers.
lemma functorCategory_shiftFunctor_obj_obj (n : A) (G : X ⥤ Y) (E : X) :
    ((shiftFunctor (X ⥤ Y) n).obj G).obj E = (shiftFunctor Y n).obj (G.obj E) :=
  rfl

@[simp]
lemma functorCategory_shiftFunctor_map_app (n : A) {G G' : X ⥤ Y} (τ : G ⟶ G')
    (E : X) :
    ((shiftFunctor (X ⥤ Y) n).map τ).app E = (shiftFunctor Y n).map (τ.app E) :=
  rfl

lemma functorCategory_shiftFunctorZero_hom_app (G : X ⥤ Y) (E : X) :
    ((shiftFunctorZero (X ⥤ Y) A).hom.app G).app E =
      (shiftFunctorZero Y A).hom.app (G.obj E) := by
  rw [ShiftMkCore.shiftFunctorZero_eq (functorCategoryShiftMkCore X Y A)]
  rfl

lemma functorCategory_shiftFunctorAdd_hom_app (n m : A) (G : X ⥤ Y) (E : X) :
    ((shiftFunctorAdd (X ⥤ Y) n m).hom.app G).app E =
      (shiftFunctorAdd Y n m).hom.app (G.obj E) := by
  rw [ShiftMkCore.shiftFunctorAdd_eq (functorCategoryShiftMkCore X Y A)]
  rfl

variable (X Y A)

/-- **Evaluation commutes with the pointwise shift on the nose.**

`(G ⋙ Y⟦n⟧).obj E` and `(G.obj E)⟦n⟧` are the same object, so the commutation
isomorphism is the identity and both coherence laws reduce to the
corresponding law on `Y`. -/
instance evaluationCommShift (E : X) :
    ((evaluation X Y).obj E).CommShift A where
  commShiftIso _ := Iso.refl _
  commShiftIso_zero := by
    ext G
    -- Every object here is `G.obj E` after unfolding `evaluation`,
    -- `whiskeringRight` and the shift.  `show` fixes one spelling, which is
    -- what lets the isomorphism cancel.
    show 𝟙 ((shiftFunctor Y 0).obj (G.obj E)) =
      (shiftFunctorZero Y A).hom.app (G.obj E) ≫
        𝟙 ((𝟭 Y).obj (G.obj E)) ≫ 𝟙 ((𝟭 Y).obj (G.obj E)) ≫
          (shiftFunctorZero Y A).inv.app (G.obj E)
    rw [Category.id_comp, Category.id_comp, Iso.hom_inv_id_app]
  commShiftIso_add n m := by
    ext G
    simp only [Functor.CommShift.isoAdd_hom_app, Iso.refl_hom, NatTrans.id_app,
      evaluation_obj_map]
    show 𝟙 ((shiftFunctor Y (n + m)).obj (G.obj E)) =
      (shiftFunctorAdd Y n m).hom.app (G.obj E) ≫
        𝟙 ((shiftFunctor Y n ⋙ shiftFunctor Y m).obj (G.obj E)) ≫
          (shiftFunctor Y m).map (𝟙 ((shiftFunctor Y n).obj (G.obj E))) ≫
            (shiftFunctorAdd Y n m).inv.app (G.obj E)
    rw [Category.id_comp, Functor.map_id]
    show 𝟙 ((shiftFunctor Y (n + m)).obj (G.obj E)) =
      (shiftFunctorAdd Y n m).hom.app (G.obj E) ≫
        𝟙 ((shiftFunctor Y n ⋙ shiftFunctor Y m).obj (G.obj E)) ≫
          (shiftFunctorAdd Y n m).inv.app (G.obj E)
    rw [Category.id_comp, Iso.hom_inv_id_app]

@[simp]
lemma evaluationCommShift_iso_hom_app (E : X) (n : A) (G : X ⥤ Y) :
    ((((evaluation X Y).obj E).commShiftIso n).hom.app G) = 𝟙 _ :=
  rfl

end CategoryTheory
