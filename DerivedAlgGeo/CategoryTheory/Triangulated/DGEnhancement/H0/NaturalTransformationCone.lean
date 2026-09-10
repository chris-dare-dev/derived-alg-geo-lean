/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.NaturalTransformationH0
import DerivedAlgGeo.Algebra.Homology.DGCategory.Pretriangulated.NaturalTransformationCone
import DerivedAlgGeo.CategoryTheory.Triangulated.DGEnhancement.H0.Triangle

/-!
# The triangle of `H⁰` attached to a closed dg natural transformation

`HomogeneousNatTrans.ConeData` chooses a dg cone of every component of a closed
degree-zero dg natural transformation `α : F ⟶ G`.  Each choice gives a
distinguished triangle of `H⁰ D`,

`F X ⟶ G X ⟶ Cone(α) X ⟶ (F X)⟦1⟧`,

and this file says those triangles are functorial in `X`.

## Why this is not automatic

The three vertices are functorial separately: `F.h0`, `G.h0` and
`ConeData.functor.h0` are ordinary functors `H⁰ C ⥤ H⁰ D`.  What has to be
supplied is that a morphism of `H⁰ C` induces a *morphism of triangles*, and
the third square of a triangle morphism involves the connecting map and the
chosen shift of `H⁰ D`.  That square is the one `IsConeOf.Morphism` was built
to carry, so the work here is to produce a cone morphism from a cocycle of `C`
and hand it to `IsConeOf.Morphism.toTriangleMorphism`.

Producing it needs three naturality statements that already exist and no new
computation:

* the square on the first two vertices is graded naturality of `α` at degree
  zero, where the Koszul sign is `+1`, so the square is strict and the
  homotopy is zero;
* the square on the cone inclusions is naturality of `ConeData.inr`;
* the square on the cone projections is naturality of `ConeData.fst`, whose
  degree-one sign `(-1)^(1 * 0)` is also `+1`.

## The homotopy class, not the representative

A morphism of `H⁰ C` is a homotopy class and a cone morphism needs an actual
cocycle, so different representatives give different cone morphisms.  The
triangle morphism they produce is nevertheless the same, because its three
components are `F.h0.map f`, `G.h0.map f` and `ConeData.functor.h0.map f`,
all of which depend only on the class.  That is why the functor below is
defined with those three components and only its three commuting squares are
proved by choosing a representative.

## What this does not give

No naturality in `α` or in the cone data, and no comparison between the
triangles produced by two different `ConeData` for the same `α`.  The
objectwise cones are choices; `IsConeOf.compare` relates two of them at each
object, but nothing here assembles those comparisons.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u'

namespace CategoryTheory

open DGCategoryStruct DGCategory Pretriangulated

namespace DGFunctor.HomogeneousNatTrans.ConeData

variable {C : Type u} {D : Type u'} [DGCategory.{v} C] [DGCategory.{v} D]
  [IsPretriangulated D] {F G : DGFunctor C D} {α : HomogeneousNatTrans F G 0}
  (K : ConeData α) (hα : IsClosed α)

/-- **The dg cone morphism a degree-zero cocycle of `C` induces.**

The homotopy is zero: graded naturality of `α` at degree zero carries the sign
`(-1)^(0 * 0) = +1`, so the square on the first two vertices commutes on the
nose.  The other two squares are naturality of `ConeData.inr` and of
`ConeData.fst`. -/
noncomputable def coneMorphism {X Y : C} (f : cocycles X Y) :
    IsConeOf.Morphism (K.isCone X) (K.isCone Y)
      (F.map 0 (f : (dgHom X Y).X 0)) (G.map 0 (f : (dgHom X Y).X 0)) where
  square :=
    { toHomogeneousSquare := HomogeneousSquare.strict (by
        symm
        simpa only [zero_mul, Int.negOnePow_zero, one_smul] using
          naturality α 0 0 (by omega) (by omega) (f : (dgHom X Y).X 0))
      a_closed := F.map_mem_cocycles f.2
      b_closed := G.map_mem_cocycles f.2 }
  hom := ⟨K.functor.map 0 (f : (dgHom X Y).X 0),
    K.functor.map_mem_cocycles f.2⟩
  inr_comm := by
    have h := naturality K.inr 0 0 (by omega) (by omega)
      (f : (dgHom X Y).X 0)
    rw [zero_mul, Int.negOnePow_zero, one_smul] at h
    exact h.symm
  fst_comm := by
    have h := naturality K.fst 0 1 (by omega) (by omega)
      (f : (dgHom X Y).X 0)
    rw [mul_zero, Int.negOnePow_zero, one_smul] at h
    exact h

/-- The distinguished triangle of `H⁰ D` at one object. -/
noncomputable def triangleObj (X : C) : Triangle (H0 D) :=
  H0.coneTriangle ⟨app α X, hα.app_mem_cocycles X⟩ (K.isCone X)

theorem triangleObj_mem_distinguishedTriangles (X : C) :
    K.triangleObj hα X ∈ H0.distinguishedTriangles D :=
  H0.coneTriangle_mem _ _

/-- The triangle morphism a cocycle of `C` induces between the cone triangles.

The two cocycles are passed explicitly.  `toTriangleMorphism` takes them as
implicit arguments constrained only through `IsConeOf`, so leaving them to
unification asks Lean to solve `?f.val =?= app α X` for a subtype element, and
it does not terminate. -/
noncomputable def coneTriangleMorphism {X Y : C} (f : cocycles X Y) :
    K.triangleObj hα X ⟶ K.triangleObj hα Y :=
  IsConeOf.Morphism.toTriangleMorphism
    (f₁ := ⟨app α X, hα.app_mem_cocycles X⟩)
    (f₂ := ⟨app α Y, hα.app_mem_cocycles Y⟩)
    (K.isCone X) (K.isCone Y) (K.coneMorphism f)

/-- **The cone triangles are functorial.**

The three components are the three induced functors on `H⁰`, so functoriality
is theirs; only the three commuting squares need a representative. -/
noncomputable def triangleFunctor : H0 C ⥤ Triangle (H0 D) where
  obj X := K.triangleObj hα (H0.of C X)
  map {X Y} f :=
    Triangle.homMk _ _ (F.h0.map f) (G.h0.map f) (K.functor.h0.map f)
      (by
        induction f using Quotient.ind with
        | _ f => exact (K.coneTriangleMorphism hα f).comm₁)
      (by
        induction f using Quotient.ind with
        | _ f => exact (K.coneTriangleMorphism hα f).comm₂)
      (by
        induction f using Quotient.ind with
        | _ f => exact (K.coneTriangleMorphism hα f).comm₃)
  -- The three components are functorial on their own, so both laws are three
  -- applications of `Functor.map_id` / `Functor.map_comp`.  `simp` here does
  -- not terminate: it unfolds `coneTriangle` and with it the chosen shift.
  map_id X := by
    refine Triangle.hom_ext _ _ ?_ ?_ ?_
    · exact F.h0.map_id X
    · exact G.h0.map_id X
    · exact K.functor.h0.map_id X
  map_comp {X Y Z} f g := by
    refine Triangle.hom_ext _ _ ?_ ?_ ?_
    · exact F.h0.map_comp f g
    · exact G.h0.map_comp f g
    · exact K.functor.h0.map_comp f g

@[simp]
theorem triangleFunctor_obj (X : H0 C) :
    (K.triangleFunctor hα).obj X = K.triangleObj hα (H0.of C X) :=
  rfl

@[simp]
theorem triangleFunctor_map_hom₁ {X Y : H0 C} (f : X ⟶ Y) :
    ((K.triangleFunctor hα).map f).hom₁ = F.h0.map f :=
  rfl

@[simp]
theorem triangleFunctor_map_hom₂ {X Y : H0 C} (f : X ⟶ Y) :
    ((K.triangleFunctor hα).map f).hom₂ = G.h0.map f :=
  rfl

@[simp]
theorem triangleFunctor_map_hom₃ {X Y : H0 C} (f : X ⟶ Y) :
    ((K.triangleFunctor hα).map f).hom₃ = K.functor.h0.map f :=
  rfl

/-- Every value of the triangle functor is a distinguished triangle. -/
theorem triangleFunctor_obj_mem_distinguishedTriangles (X : H0 C) :
    (K.triangleFunctor hα).obj X ∈ H0.distinguishedTriangles D :=
  K.triangleObj_mem_distinguishedTriangles hα _

end DGFunctor.HomogeneousNatTrans.ConeData

end CategoryTheory
