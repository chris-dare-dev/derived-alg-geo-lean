/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Shift.CommShiftTwo
import DerivedAlgGeo.CategoryTheory.Shift.CommShift

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

`Triangulated/ExactFunctorFamily.lean` therefore extends this ordinary
`CommShift` instead of storing evaluated structures and their naturality by
hand.

For `F : K ⥤ X ⥤ Y` carrying Mathlib's `CommShift₂`, the two explicit
adapters below assemble the shift data in either variable into a `CommShift`
on `F` or `F.flip`.  Composing those structures with strict evaluation gives
exactly the partial structures selected by `CommShift₂`; the equality is a
theorem, not an instance, so consumers can transport data without creating a
typeclass diamond.
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

lemma functorCategory_shiftFunctorZero_inv_app (G : X ⥤ Y) (E : X) :
    ((shiftFunctorZero (X ⥤ Y) A).inv.app G).app E =
      (shiftFunctorZero Y A).inv.app (G.obj E) := by
  rw [ShiftMkCore.shiftFunctorZero_eq (functorCategoryShiftMkCore X Y A)]
  rfl

lemma functorCategory_shiftFunctorAdd_hom_app (n m : A) (G : X ⥤ Y) (E : X) :
    ((shiftFunctorAdd (X ⥤ Y) n m).hom.app G).app E =
      (shiftFunctorAdd Y n m).hom.app (G.obj E) := by
  rw [ShiftMkCore.shiftFunctorAdd_eq (functorCategoryShiftMkCore X Y A)]
  rfl

lemma functorCategory_shiftFunctorAdd_inv_app (n m : A) (G : X ⥤ Y) (E : X) :
    ((shiftFunctorAdd (X ⥤ Y) n m).inv.app G).app E =
      (shiftFunctorAdd Y n m).inv.app (G.obj E) := by
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

universe vK vX vY uK uX uY uM

namespace Functor.CommShift₂

variable {K : Type uK} {X : Type uX} {Y : Type uY}
  [Category.{vK} K] [Category.{vX} X] [Category.{vY} Y]
  {M : Type uM} [AddCommMonoid M]
  [HasShift K M] [HasShift X M] [HasShift Y M]
  {F : K ⥤ X ⥤ Y} (h : CommShift₂Setup Y M) [F.CommShift₂ h]

/-- Assemble the shift coherence in the first variable of a bifunctor into
an ordinary `CommShift` structure on its functor-valued family.

This is an explicit definition rather than an instance: a consumer may have
already selected another `CommShift` structure on `F`. -/
@[reducible]
noncomputable def firstFamilyCommShift : F.CommShift M where
  commShiftIso n :=
    NatIso.ofComponents
      (fun A => NatIso.ofComponents
        (fun E => ((F.flip.obj E).commShiftIso n).app A)
        (fun f => (NatTrans.shift_app_comm (F.flip.map f) n A).symm))
      (fun f => by
        ext E
        exact ((F.flip.obj E).commShiftIso n).hom.naturality f)
  commShiftIso_zero := by
    ext A E
    change ((F.flip.obj E).commShiftIso 0).hom.app A = _
    rw [(F.flip.obj E).commShiftIso_zero]
    simp [Functor.CommShift.isoZero_hom_app,
      functorCategory_shiftFunctorZero_inv_app]
    rfl
  commShiftIso_add n m := by
    ext A E
    change ((F.flip.obj E).commShiftIso (n + m)).hom.app A = _
    rw [(F.flip.obj E).commShiftIso_add]
    simp [Functor.CommShift.isoAdd_hom_app,
      functorCategory_shiftFunctorAdd_inv_app]
    rfl

/-- The first-family shift comparison evaluates to the partial comparison
selected by `CommShift₂`. -/
theorem firstFamilyCommShift_iso_hom_app_app (n : M) (A : K) (E : X) :
    letI : F.CommShift M := firstFamilyCommShift h
    ((F.commShiftIso n).hom.app A).app E =
      ((F.flip.obj E).commShiftIso n).hom.app A :=
  rfl

/-- Assemble the shift coherence in the second variable of a bifunctor into
an ordinary `CommShift` structure on the flipped functor-valued family. -/
@[reducible]
noncomputable def secondFamilyCommShift : F.flip.CommShift M where
  commShiftIso n :=
    NatIso.ofComponents
      (fun E => NatIso.ofComponents
        (fun A => ((F.obj A).commShiftIso n).app E)
        (fun f => (NatTrans.shift_app_comm (F.map f) n E).symm))
      (fun f => by
        ext A
        exact ((F.obj A).commShiftIso n).hom.naturality f)
  commShiftIso_zero := by
    ext E A
    change ((F.obj A).commShiftIso 0).hom.app E = _
    rw [(F.obj A).commShiftIso_zero]
    simp [Functor.CommShift.isoZero_hom_app,
      functorCategory_shiftFunctorZero_inv_app]
    rfl
  commShiftIso_add n m := by
    ext E A
    change ((F.obj A).commShiftIso (n + m)).hom.app E = _
    rw [(F.obj A).commShiftIso_add]
    simp [Functor.CommShift.isoAdd_hom_app,
      functorCategory_shiftFunctorAdd_inv_app]
    rfl

/-- The second-family shift comparison evaluates to the partial comparison
selected by `CommShift₂`. -/
theorem secondFamilyCommShift_iso_hom_app_app (n : M) (E : X) (A : K) :
    letI : F.flip.CommShift M := secondFamilyCommShift h
    ((F.flip.commShiftIso n).hom.app E).app A =
      ((F.obj A).commShiftIso n).hom.app E :=
  rfl

/-- The first-family shift structure, composed with strict evaluation. -/
@[reducible]
noncomputable def firstFamilyEvaluationCommShift (E : X) :
    (F ⋙ (evaluation X Y).obj E).CommShift M := by
  letI : F.CommShift M := firstFamilyCommShift h
  letI : ((evaluation X Y).obj E).CommShift M :=
    CategoryTheory.evaluationCommShift X Y M E
  exact Functor.CommShift.comp F ((evaluation X Y).obj E)

/-- Evaluation of the assembled first-family structure is exactly the
partial structure selected by `CommShift₂`. -/
theorem firstFamilyEvaluationCommShift_eq (E : X) :
    firstFamilyEvaluationCommShift (F := F) h E =
      Functor.CommShift₂.commShiftFlipObj (G := F) h E := by
  apply Functor.CommShift.ext
  intro n
  ext A
  change _ = ((F.flip.obj E).commShiftIso n).hom.app A
  simp only [Functor.commShiftIso_comp_hom_app, evaluation_obj_map,
    evaluationCommShift_iso_hom_app, firstFamilyCommShift_iso_hom_app_app]
  exact Category.comp_id _

/-- The second-family shift structure, composed with strict evaluation. -/
@[reducible]
noncomputable def secondFamilyEvaluationCommShift (A : K) :
    (F.flip ⋙ (evaluation K Y).obj A).CommShift M := by
  letI : F.flip.CommShift M := secondFamilyCommShift h
  letI : ((evaluation K Y).obj A).CommShift M :=
    CategoryTheory.evaluationCommShift K Y M A
  exact Functor.CommShift.comp F.flip ((evaluation K Y).obj A)

/-- Evaluation of the assembled second-family structure is exactly the
partial structure selected by `CommShift₂`. -/
theorem secondFamilyEvaluationCommShift_eq (A : K) :
    secondFamilyEvaluationCommShift (F := F) h A =
      Functor.CommShift₂.commShiftObj (G := F) h A := by
  apply Functor.CommShift.ext
  intro n
  ext E
  change _ = ((F.obj A).commShiftIso n).hom.app E
  simp only [Functor.commShiftIso_comp_hom_app, evaluation_obj_map,
    evaluationCommShift_iso_hom_app, secondFamilyCommShift_iso_hom_app_app]
  exact Category.comp_id _

end Functor.CommShift₂

end CategoryTheory
