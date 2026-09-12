/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Shift.CommShiftTwo
import Mathlib.CategoryTheory.Triangulated.Functor
import DerivedAlgGeo.CategoryTheory.Shift.FunctorCategory

/-!
# Exact families of functors

Let `F : K ⥤ (X ⥤ Y)` be a family of functors from `X` to `Y`, parametrized
by a triangulated category `K`.  The target functor category carries the
pointwise shift, so the global coherence for such a family is exactly
Mathlib's ordinary `F.CommShift ℤ`.  Its shift isomorphism is already natural
in `E : X` and already satisfies the zero and addition laws.

`Functor.ExactFamily` extends that canonical structure by pointwise
triangulatedness.  Its `mapTriangle` construction fixes a triangle in `K` and
produces the source-natural triangle in `Y`; pointwise distinguishedness is
then a theorem.  Fourier--Mukai kernel families are a principal consumer, but
no kernel vocabulary belongs here.

For an actual bifunctor, `Functor.ExactBifunctor` is the stronger canonical
root.  It uses Mathlib's `CommShift₂Int`, including the Koszul compatibility
between shifts in the two variables, and asks for triangulatedness in both
slots.  Explicit adapters assemble its partial shift comparisons into
ordinary `CommShift` structures on the two functor-valued families; they are
definitions rather than global instances, so they introduce no instance
diamond.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe vK vK' vX vY uK uK' uX uY

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Functor

variable {K : Type uK} {X : Type uX} {Y : Type uY}
  [Category.{vK} K] [Category.{vX} X] [Category.{vY} Y]

variable [HasZeroObject K] [HasShift K ℤ] [Preadditive K]
  [∀ n : ℤ, (shiftFunctor K n).Additive] [Pretriangulated K]
  [HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]

/-- An exact functor-valued family.

Exactness is checked after evaluation, but all evaluated shift structures are
the components of one source-natural family comparison. -/
structure ExactFamily (F : K ⥤ (X ⥤ Y)) extends F.CommShift ℤ where
  /-- Every evaluated functor preserves distinguished triangles. -/
  triangulated (E : X) :
    letI : F.CommShift ℤ := toCommShift
    letI : ((evaluation X Y).obj E).CommShift ℤ :=
      CategoryTheory.evaluationCommShift X Y ℤ E
    letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ :=
      Functor.CommShift.comp F ((evaluation X Y).obj E)
    (F ⋙ (evaluation X Y).obj E).IsTriangulated

namespace ExactFamily

variable {F : K ⥤ (X ⥤ Y)} (h : ExactFamily F)

/-- Evaluate an exact family at one source object, with its chosen shift
coherence exposed as a definition for local instance installation. -/
@[reducible]
noncomputable def evaluationCommShift (E : X) :
    (F ⋙ (evaluation X Y).obj E).CommShift ℤ := by
  letI : F.CommShift ℤ := h.toCommShift
  letI : ((evaluation X Y).obj E).CommShift ℤ :=
    CategoryTheory.evaluationCommShift X Y ℤ E
  exact Functor.CommShift.comp F ((evaluation X Y).obj E)

/-- The shift comparison of an exact family, after evaluation, is the
corresponding component of its global `CommShift` comparison. -/
theorem evaluationCommShift_iso_hom_app (E : X) (n : ℤ) (A : K) :
    letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ :=
      h.evaluationCommShift E
    ((F ⋙ (evaluation X Y).obj E).commShiftIso n).hom.app A =
      ((h.toCommShift.commShiftIso n).hom.app A).app E := by
  simp only [Functor.commShiftIso_comp_hom_app, evaluation_obj_map,
    CategoryTheory.evaluationCommShift_iso_hom_app]
  exact Category.comp_id _

/-- The image of a triangle under an exact family, natural in the source
object of the functors in the family. -/
noncomputable def mapTriangle (T : Triangle K) : X ⥤ Triangle Y :=
  letI : F.CommShift ℤ := h.toCommShift
  Triangle.functorMk
    (F.map T.mor₁)
    (F.map T.mor₂)
    (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁)

@[simp]
theorem mapTriangle_obj_obj₁ (T : Triangle K) (E : X) :
    ((mapTriangle h T).obj E).obj₁ = (F.obj T.obj₁).obj E :=
  rfl

@[simp]
theorem mapTriangle_obj_obj₂ (T : Triangle K) (E : X) :
    ((mapTriangle h T).obj E).obj₂ = (F.obj T.obj₂).obj E :=
  rfl

@[simp]
theorem mapTriangle_obj_obj₃ (T : Triangle K) (E : X) :
    ((mapTriangle h T).obj E).obj₃ = (F.obj T.obj₃).obj E :=
  rfl

/-- Evaluation of the source-natural image triangle agrees with Mathlib's
ordinary `mapTriangle` for the evaluated functor. -/
theorem mapTriangle_obj (T : Triangle K) (E : X) :
    (mapTriangle h T).obj E =
      letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ :=
        h.evaluationCommShift E
      (F ⋙ (evaluation X Y).obj E).mapTriangle.obj T := by
  cases T
  dsimp [mapTriangle, Functor.mapTriangle]
  rw [h.evaluationCommShift_iso_hom_app]
  rfl

/-- An exact family sends a distinguished parameter triangle to a triangle
which is distinguished at every source object. -/
theorem mapTriangle_obj_distinguished (T : Triangle K)
    (hT : T ∈ distTriang K) (E : X) :
    (mapTriangle h T).obj E ∈ distTriang Y := by
  rw [mapTriangle_obj h T E]
  letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ :=
    h.evaluationCommShift E
  letI : (F ⋙ (evaluation X Y).obj E).IsTriangulated := h.triangulated E
  exact (F ⋙ (evaluation X Y).obj E).map_distinguished T hT

/-- The object property of being a distinguished triangle in the target. -/
abbrev distinguishedTriangleProperty : ObjectProperty (Triangle Y) :=
  distTriang Y

/-- A distinguished parameter triangle gives a source-indexed family valued
in the full subcategory of distinguished target triangles. -/
noncomputable def mapDistinguishedTriangle (T : Triangle K)
    (hT : T ∈ distTriang K) :
    X ⥤ (distinguishedTriangleProperty (Y := Y)).FullSubcategory :=
  (distinguishedTriangleProperty (Y := Y)).lift
    (mapTriangle h T) (mapTriangle_obj_distinguished h T hT)

@[simp]
theorem mapDistinguishedTriangle_obj_val (T : Triangle K)
    (hT : T ∈ distTriang K) (E : X) :
    ((mapDistinguishedTriangle h T hT).obj E).obj =
      (mapTriangle h T).obj E :=
  rfl

end ExactFamily

section Bifunctor

variable {K' : Type uK'} [Category.{vK'} K']
  [HasZeroObject K'] [HasShift K' ℤ] [Preadditive K']
  [∀ n : ℤ, (shiftFunctor K' n).Additive] [Pretriangulated K']

/-- A bifunctor exact in both variables, with one coherent choice of shift
comparisons.

The `CommShift₂Int` parent is stronger than separately choosing a
`CommShift` instance in each slot: it also records naturality in the other
variable and the Koszul-sign compatibility between shifting the two inputs.
The two triangulatedness fields then say that both partial functors preserve
distinguished triangles. -/
structure ExactBifunctor (F : K ⥤ K' ⥤ Y) extends F.CommShift₂Int where
  /-- Exactness in the first variable, after fixing the second. -/
  firstTriangulated (B : K') :
    letI : (F.flip.obj B).CommShift ℤ := commShiftFlipObj B
    (F.flip.obj B).IsTriangulated
  /-- Exactness in the second variable, after fixing the first. -/
  secondTriangulated (A : K) :
    letI : (F.obj A).CommShift ℤ := commShiftObj A
    (F.obj A).IsTriangulated

namespace ExactBifunctor

variable {F : K ⥤ K' ⥤ Y} (h : ExactBifunctor F)

/-- Forget to the exact family obtained by varying the first variable.

Here `K` is the parameter category and objects of `K'` index the evaluated
partial functors `K ⥤ Y`. -/
noncomputable def firstFamily : ExactFamily F := by
  letI : F.CommShift₂Int := h.toCommShift₂
  refine
    { toCommShift := Functor.CommShift₂.firstFamilyCommShift .int
      triangulated := fun B => ?_ }
  change @Functor.IsTriangulated _ _ _ _ _ _ (F.flip.obj B)
    (Functor.CommShift₂.firstFamilyEvaluationCommShift .int B) _ _ _ _ _ _ _ _
  rw [Functor.CommShift₂.firstFamilyEvaluationCommShift_eq .int B]
  exact h.firstTriangulated B

/-- Forget to the exact family obtained by varying the second variable. -/
noncomputable def secondFamily : ExactFamily F.flip := by
  letI : F.CommShift₂Int := h.toCommShift₂
  refine
    { toCommShift := Functor.CommShift₂.secondFamilyCommShift .int
      triangulated := fun A => ?_ }
  change @Functor.IsTriangulated _ _ _ _ _ _ (F.obj A)
    (Functor.CommShift₂.secondFamilyEvaluationCommShift .int A) _ _ _ _ _ _ _ _
  rw [Functor.CommShift₂.secondFamilyEvaluationCommShift_eq .int A]
  exact h.secondTriangulated A

/-- The first-variable partial functor with the shift structure selected by
the bifunctor root. -/
@[reducible] def firstCommShift (B : K') : (F.flip.obj B).CommShift ℤ :=
  h.commShiftFlipObj B

/-- The second-variable partial functor with the shift structure selected by
the bifunctor root. -/
@[reducible] def secondCommShift (A : K) : (F.obj A).CommShift ℤ :=
  h.commShiftObj A

end ExactBifunctor

end Bifunctor

end Functor

end CategoryTheory
