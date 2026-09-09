/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Shift.CommShiftTwo
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Exact families of functors

Let `F : K ⥤ (X ⥤ Y)` be a family of functors from `X` to `Y`, parametrized
by a triangulated category `K`.  Saying separately that every evaluation

`F ⋙ evaluation X Y E : K ⥤ Y`

commutes with shifts is not enough to construct a triangle of functors
`X ⥤ Triangle Y`: the shift comparisons must also be natural in `E`.

`Functor.FamilyCommShift` records exactly that global coherence.  It stores
the ordinary `CommShift` data after every evaluation and one additional
naturality law in the family variable.  From it we construct a single
isomorphism of functor-valued families

`[n] ⋙ F ≅ F ⋙ postcompose [n]`.

`Functor.ExactFamily` adds pointwise triangulatedness.  Its `mapTriangle`
construction fixes a triangle in `K` and produces the source-natural triangle
in `Y`; pointwise distinguishedness is then a theorem.  Fourier--Mukai kernel
families are a principal consumer, but no kernel vocabulary belongs here.

For an actual bifunctor, `Functor.ExactBifunctor` is the stronger canonical
root.  It uses Mathlib's `CommShift₂Int`, including the Koszul compatibility
between shifts in the two variables, and asks for triangulatedness in both
slots.  Its two projections recover `ExactFamily` in either orientation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe vK vK' vX vY uK uK' uX uY

namespace CategoryTheory

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Functor

variable {K : Type uK} {X : Type uX} {Y : Type uY}
  [Category.{vK} K] [Category.{vX} X] [Category.{vY} Y]

/-- A shift-coherent functor-valued family.

The `CommShift` field at each `E : X` contains the zero and addition laws.
The extra equation says that its shift isomorphisms are natural in `E`, so
they are components of an isomorphism in the functor category `X ⥤ Y`. -/
structure FamilyCommShift (F : K ⥤ (X ⥤ Y))
    [HasShift K ℤ] [HasShift Y ℤ] where
  /-- Shift coherence after evaluating the family at one source object. -/
  commShift (E : X) : (F ⋙ (evaluation X Y).obj E).CommShift ℤ
  /-- The evaluated shift comparisons are natural in the source object. -/
  commShift_naturality (n : ℤ) {E E' : X} (f : E ⟶ E') (A : K) :
    letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ := commShift E
    letI : (F ⋙ (evaluation X Y).obj E').CommShift ℤ := commShift E'
    (F.obj ((shiftFunctor K n).obj A)).map f ≫
        (((F ⋙ (evaluation X Y).obj E').commShiftIso n).hom.app A) =
      ((F ⋙ (evaluation X Y).obj E).commShiftIso n).hom.app A ≫
        (shiftFunctor Y n).map ((F.obj A).map f)

namespace FamilyCommShift

variable {F : K ⥤ (X ⥤ Y)} [HasShift K ℤ] [HasShift Y ℤ]
  (h : FamilyCommShift F)

/-- Postcomposition by the `n`-shift on the target of the family. -/
def postShift (n : ℤ) : (X ⥤ Y) ⥤ (X ⥤ Y) :=
  (whiskeringRight X Y Y).obj (shiftFunctor Y n)

/-- The shift comparison at one parameter, already natural in the source
object of the functors in the family. -/
noncomputable def shiftIsoApp (n : ℤ) (A : K) :
    F.obj ((shiftFunctor K n).obj A) ≅
      F.obj A ⋙ shiftFunctor Y n :=
  NatIso.ofComponents
    (fun E => by
      letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ := h.commShift E
      exact ((F ⋙ (evaluation X Y).obj E).commShiftIso n).app A)
    (fun f => h.commShift_naturality n f A)

/-- The global shift comparison of a functor-valued family.

Its component at a parameter `A : K` is a natural isomorphism of functors
`X ⥤ Y`; its component at `E : X` is the shift comparison stored by the
evaluated functor. -/
noncomputable def shiftIso (n : ℤ) :
    shiftFunctor K n ⋙ F ≅ F ⋙ postShift (X := X) (Y := Y) n :=
  NatIso.ofComponents
    (fun A => shiftIsoApp h n A)
    (fun f => by
      ext E
      letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ := h.commShift E
      exact ((F ⋙ (evaluation X Y).obj E).commShiftIso n).hom.naturality f)

theorem shiftIso_hom_app_app (n : ℤ) (A : K) (E : X) :
    ((shiftIso h n).hom.app A).app E =
      letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ := h.commShift E
      ((F ⋙ (evaluation X Y).obj E).commShiftIso n).hom.app A :=
  rfl

theorem shiftIso_inv_app_app (n : ℤ) (A : K) (E : X) :
    ((shiftIso h n).inv.app A).app E =
      letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ := h.commShift E
      ((F ⋙ (evaluation X Y).obj E).commShiftIso n).inv.app A :=
  rfl

end FamilyCommShift

variable [HasZeroObject K] [HasShift K ℤ] [Preadditive K]
  [∀ n : ℤ, (shiftFunctor K n).Additive] [Pretriangulated K]
  [HasZeroObject Y] [HasShift Y ℤ] [Preadditive Y]
  [∀ n : ℤ, (shiftFunctor Y n).Additive] [Pretriangulated Y]

/-- An exact functor-valued family.

Exactness is checked after evaluation, but all evaluated shift structures are
the components of one source-natural family comparison. -/
structure ExactFamily (F : K ⥤ (X ⥤ Y)) extends FamilyCommShift F where
  /-- Every evaluated functor preserves distinguished triangles. -/
  triangulated (E : X) :
    letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ := commShift E
    (F ⋙ (evaluation X Y).obj E).IsTriangulated

namespace ExactFamily

variable {F : K ⥤ (X ⥤ Y)} (h : ExactFamily F)

/-- Evaluate an exact family at one source object, with its chosen shift
coherence exposed as a definition for local instance installation. -/
@[reducible] def evaluationCommShift (E : X) :
    (F ⋙ (evaluation X Y).obj E).CommShift ℤ :=
  h.commShift E

/-- The image of a triangle under an exact family, natural in the source
object of the functors in the family. -/
noncomputable def mapTriangle (T : Triangle K) : X ⥤ Triangle Y :=
  Triangle.functorMk
    (F.map T.mor₁)
    (F.map T.mor₂)
    (F.map T.mor₃ ≫
      (FamilyCommShift.shiftIso h.toFamilyCommShift (1 : ℤ)).hom.app T.obj₁)

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
      letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ := h.commShift E
      (F ⋙ (evaluation X Y).obj E).mapTriangle.obj T :=
  rfl

/-- An exact family sends a distinguished parameter triangle to a triangle
which is distinguished at every source object. -/
theorem mapTriangle_obj_distinguished (T : Triangle K)
    (hT : T ∈ distTriang K) (E : X) :
    (mapTriangle h T).obj E ∈ distTriang Y := by
  rw [mapTriangle_obj h T E]
  letI : (F ⋙ (evaluation X Y).obj E).CommShift ℤ := h.commShift E
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
def firstFamily : ExactFamily F where
  commShift B := h.commShiftFlipObj B
  commShift_naturality n {B B'} f A := by
    letI : F.CommShift₂Int := h.toCommShift₂
    exact (NatTrans.shift_app_comm (F.flip.map f) n A).symm
  triangulated B := h.firstTriangulated B

/-- Forget to the exact family obtained by varying the second variable. -/
def secondFamily : ExactFamily F.flip where
  commShift A := h.commShiftObj A
  commShift_naturality n {A A'} f B := by
    letI : F.CommShift₂Int := h.toCommShift₂
    exact (NatTrans.shift_app_comm (F.map f) n B).symm
  triangulated A := h.secondTriangulated A

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
