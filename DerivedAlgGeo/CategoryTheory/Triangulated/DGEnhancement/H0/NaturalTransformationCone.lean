/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DGCategory.FunctorCategoryH0
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

## Naturality in the transformation, and its hypothesis

A strictly commuting square of closed degree-zero dg natural transformations
between two cone situations induces a natural transformation of triangle
functors (`triangleNatTrans`).  Strictness is the hypothesis that makes this
work and it is not cosmetic: with a zero homotopy every cone map in sight is a
*strict* lift, so `homogeneousLift_strict_comp` collapses each composite to a
single lift and the two agree because `u` and `v` are natural at degree zero.
The cone lifts are therefore natural **on the nose**, not merely up to
homotopy, which is `functor_map_comp_lift`.

When both endpoint maps are isomorphisms in the closed degree-zero dg-functor
category, `triangleIsoOfStrictSquare` upgrades this natural transformation to
a natural isomorphism.  Its first two components are the `H⁰` images of the
endpoint isomorphisms, and its third is the `H⁰` image of the canonical dg
cone-functor isomorphism `ConeData.isoOfStrictSquare`.

The homotopy-coherent version is open.  With a nonzero homotopy the two
composite lifts carry different homotopies, and identifying them needs
uniqueness of the lift up to homotopy, which this repository does not have.

## The cone choices do not matter

`ConeData` is a choice of cone at every object, and `compareIso` says the
triangle functor does not depend on it: two choices give canonically
isomorphic functors.  The comparison is the identity case of the naturality
above, since two `ConeData` for the same `α` are related by the identity
square, and `compareNatTrans_self` and `compareNatTrans_comp` are what make it
an isomorphism rather than merely a map.

## What this does not give

No comparison is made from a merely homotopy-commuting square, and no statement
says that `triangleFunctor` is triangulated or exact in any sense.  The generic
strict-square interface is specialized to object twists in `H0/ObjectTwist`;
autoequivalence and sphericality remain separate questions.
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


/-! ### Naturality in the transformation -/

section Naturality

variable {F' G' : DGFunctor C D} {α' : HomogeneousNatTrans F' G' 0}
  (K' : ConeData α') (hα' : IsClosed α')
  {u : HomogeneousNatTrans F F' 0} {v : HomogeneousNatTrans G G' 0}
  (hu : IsClosed u) (hv : IsClosed v)
  (hsq : composition F G G' 0 0 0 (by omega) α v =
    composition F F' G' 0 0 0 (by omega) u α')

/-- A strictly commuting square of closed degree-zero dg natural
transformations, read at one object.  The homotopy is zero, which is what makes
the whole naturality statement below strict rather than up to homotopy. -/
noncomputable def squareAt (X : C) :
    DGCategory.HomotopySquare (app α X) (app α' X) (app u X) (app v X) :=
  DGCategory.HomotopySquare.ofBoundary (hu.app_mem_cocycles X)
    (hv.app_mem_cocycles X) 0 (by
      rw [map_zero]
      have h := congrArg (fun σ => app σ X) hsq
      rw [composition_apply_app, composition_apply_app] at h
      rw [h, sub_self])

/-- The cone morphism the square induces at one object: the standard dg lift,
with zero homotopy. -/
noncomputable def squareConeMorphism (X : C) :
    IsConeOf.Morphism (K.isCone X) (K'.isCone X) (app u X) (app v X) :=
  IsConeOf.liftMorphism (K.isCone X) (K'.isCone X) (app u X) (app v X)
    (squareAt hu hv hsq X)

/-- The triangle morphism the square induces at one object.

The two cocycles are passed explicitly for the same reason as in
`coneTriangleMorphism`: left to unification they do not resolve. -/
noncomputable def squareTriangleMorphism (X : C) :
    K.triangleObj hα X ⟶ K'.triangleObj hα' X :=
  IsConeOf.Morphism.toTriangleMorphism
    (f₁ := ⟨app α X, hα.app_mem_cocycles X⟩)
    (f₂ := ⟨app α' X, hα'.app_mem_cocycles X⟩)
    (K.isCone X) (K'.isCone X) (K.squareConeMorphism K' hu hv hsq X)

omit [IsPretriangulated D] in
/-- **The cone lifts are natural, on the nose.**

Both composites are a composite of two strict lifts, so
`homogeneousLift_strict_comp` rewrites each to a single strict lift, and the
two agree because `u` and `v` are natural at degree zero, where the Koszul
sign is `+1`.  Nothing here is up to homotopy: that is what the square being
strict buys. -/
theorem functor_map_comp_lift {X Y : C} (f : (dgHom X Y).X 0) :
    dgComp 0 0 0 (by omega) (K.functor.map 0 f)
        ((K.squareConeMorphism K' hu hv hsq Y).hom : (dgHom (K.obj Y) (K'.obj Y)).X 0) =
      dgComp 0 0 0 (by omega)
        ((K.squareConeMorphism K' hu hv hsq X).hom :
          (dgHom (K.obj X) (K'.obj X)).X 0)
        (K'.functor.map 0 f) := by
  -- Both naturality squares are stated at the result index `0 + 0`, which is
  -- the index `homogeneousLift_strict_comp` produces.  `0` and `0 + 0` are
  -- definitionally equal but not syntactically, and `rw` matches
  -- syntactically, so the ascription is what lets the last two rewrites fire.
  have hu' : dgComp 0 0 (0 + 0) (by omega) (F.map 0 f) (app u Y) =
      dgComp 0 0 (0 + 0) (by omega) (app u X) (F'.map 0 f) := by
    have h := naturality u 0 0 (by omega) (by omega) f
    rw [zero_mul, Int.negOnePow_zero, one_smul] at h
    exact h
  have hv' : dgComp 0 0 (0 + 0) (by omega) (G.map 0 f) (app v Y) =
      dgComp 0 0 (0 + 0) (by omega) (app v X) (G'.map 0 f) := by
    have h := naturality v 0 0 (by omega) (by omega) f
    rw [zero_mul, Int.negOnePow_zero, one_smul] at h
    exact h
  show dgComp 0 0 (0 + 0) (by omega)
      ((K.isCone X).homogeneousLift (K.isCone Y) 0 (F.map 0 f) (G.map 0 f) 0)
      ((K.isCone Y).homogeneousLift (K'.isCone Y) 0 (app u Y) (app v Y) 0) =
    dgComp 0 0 (0 + 0) (by omega)
      ((K.isCone X).homogeneousLift (K'.isCone X) 0 (app u X) (app v X) 0)
      ((K'.isCone X).homogeneousLift (K'.isCone Y) 0 (F'.map 0 f) (G'.map 0 f) 0)
  rw [(K.isCone X).homogeneousLift_strict_comp (K.isCone Y) (K'.isCone Y) 0 0,
    (K.isCone X).homogeneousLift_strict_comp (K'.isCone X) (K'.isCone Y) 0 0,
    hu', hv']

@[simp]
theorem squareTriangleMorphism_hom₁ (X : C) :
    (squareTriangleMorphism K hα K' hα' hu hv hsq X).hom₁ =
      H0.homMk (C := D) ⟨app u X, hu.app_mem_cocycles X⟩ :=
  rfl

@[simp]
theorem squareTriangleMorphism_hom₂ (X : C) :
    (squareTriangleMorphism K hα K' hα' hu hv hsq X).hom₂ =
      H0.homMk (C := D) ⟨app v X, hv.app_mem_cocycles X⟩ :=
  rfl

@[simp]
theorem squareTriangleMorphism_hom₃ (X : C) :
    (squareTriangleMorphism K hα K' hα' hu hv hsq X).hom₃ =
      H0.homMk (C := D) (K.squareConeMorphism K' hu hv hsq X).hom :=
  rfl

/-- **The triangle functors are natural in the transformation.**

A strictly commuting square of closed degree-zero dg natural transformations
induces a natural transformation of triangle functors.  The first two
components are naturality of `u` and `v` on `H⁰`; the third is
`functor_map_comp_lift`.

Every step goes through the component lemmas rather than through `exact` on
the assembled triangle morphisms.  The assembled terms unfold to the chosen
cones and the chosen shift, and the defeq check does not terminate. -/
noncomputable def triangleNatTrans :
    K.triangleFunctor hα ⟶ K'.triangleFunctor hα' where
  app X := squareTriangleMorphism K hα K' hα' hu hv hsq (H0.of C X)
  naturality X Y f := by
    refine Triangle.hom_ext _ _ ?_ ?_ ?_
    · rw [comp_hom₁, comp_hom₁, triangleFunctor_map_hom₁,
        squareTriangleMorphism_hom₁, squareTriangleMorphism_hom₁,
        triangleFunctor_map_hom₁]
      exact (HomogeneousNatTrans.h0 u hu).naturality f
    · rw [comp_hom₂, comp_hom₂, triangleFunctor_map_hom₂,
        squareTriangleMorphism_hom₂, squareTriangleMorphism_hom₂,
        triangleFunctor_map_hom₂]
      exact (HomogeneousNatTrans.h0 v hv).naturality f
    · rw [comp_hom₃, comp_hom₃, triangleFunctor_map_hom₃,
        squareTriangleMorphism_hom₃, squareTriangleMorphism_hom₃,
        triangleFunctor_map_hom₃]
      induction f using Quotient.ind with
      | _ f =>
        -- `h0_map_mk` and `homMk_comp` are both `rfl`, so both sides are
        -- already the class of a `dgComp`; rewriting with them only swaps
        -- `H0.homMk` for `QuotientAddGroup.mk` and stops the next rewrite
        -- from matching.
        exact congrArg (fun z => H0.homMk (C := D) z)
          (Subtype.ext (K.functor_map_comp_lift K' hu hv hsq
            (f : (dgHom (H0.of C X) (H0.of C Y)).X 0)))

@[simp]
theorem triangleNatTrans_app (X : H0 C) :
    (triangleNatTrans K hα K' hα' hu hv hsq).app X =
      squareTriangleMorphism K hα K' hα' hu hv hsq (H0.of C X) :=
  rfl

end Naturality


/-! ### Isomorphisms induced by strict isomorphism squares -/

section StrictSquareIso

variable {F' G' : DGFunctor C D} {α' : HomogeneousNatTrans F' G' 0}

private noncomputable def squareTriangleIsoOfStrictSquare
    (K : ConeData α) (hα : IsClosed α)
    (K' : ConeData α') (hα' : IsClosed α')
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α')
    (X : C) :
    K.triangleObj hα X ≅ K'.triangleObj hα' X := by
  let m := squareTriangleMorphism K hα K' hα'
    (DGFunctor.isClosed_of_mem_cocycles eF.hom.2)
    (DGFunctor.isClosed_of_mem_cocycles eG.hom.2) hsq X
  have h₁ : IsIso m.hom₁ := by
    change IsIso ((DGFunctor.h0Iso eF).hom.app (show H0 C from X))
    infer_instance
  have h₂ : IsIso m.hom₂ := by
    change IsIso ((DGFunctor.h0Iso eG).hom.app (show H0 C from X))
    infer_instance
  have h₃ : IsIso m.hom₃ := by
    have heq : m.hom₃ =
        ((DGFunctor.h0Iso (K.isoOfStrictSquare K' eF eG hsq)).app
          (show H0 C from X)).hom := by
      rw [show m.hom₃ =
        H0.homMk (C := D) (K.squareConeMorphism K'
          (DGFunctor.isClosed_of_mem_cocycles eF.hom.2)
          (DGFunctor.isClosed_of_mem_cocycles eG.hom.2) hsq X).hom from rfl,
        DGFunctor.h0Iso_hom_app, HomogeneousNatTrans.h0_app]
      exact congrArg (fun z => H0.homMk (C := D) z)
        (Subtype.ext (K.isoOfStrictSquare_hom_app K' eF eG hsq X).symm)
    rw [heq]
    infer_instance
  letI : IsIso m := Triangle.isIso_of_isIsos m h₁ h₂ h₃
  exact asIso m

private lemma squareTriangleIsoOfStrictSquare_hom
    (K : ConeData α) (hα : IsClosed α)
    (K' : ConeData α') (hα' : IsClosed α')
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α')
    (X : C) :
    (squareTriangleIsoOfStrictSquare K hα K' hα' eF eG hsq X).hom =
      squareTriangleMorphism K hα K' hα'
        (DGFunctor.isClosed_of_mem_cocycles eF.hom.2)
        (DGFunctor.isClosed_of_mem_cocycles eG.hom.2) hsq X := by
  rfl

/-- A strict square of closed dg natural transformations whose two endpoint
maps are isomorphisms induces a natural isomorphism of their cone triangle
functors.  Its third component is the `H⁰` image of the dg cone-functor
isomorphism `ConeData.isoOfStrictSquare`. -/
noncomputable def triangleIsoOfStrictSquare
    (K : ConeData α) (hα : IsClosed α)
    (K' : ConeData α') (hα' : IsClosed α')
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α') :
    K.triangleFunctor hα ≅ K'.triangleFunctor hα' :=
  NatIso.ofComponents
    (fun X => squareTriangleIsoOfStrictSquare K hα K' hα' eF eG hsq
      (H0.of C X))
    (fun f => by
      simpa only [squareTriangleIsoOfStrictSquare_hom,
        triangleNatTrans_app] using
        (triangleNatTrans K hα K' hα'
          (DGFunctor.isClosed_of_mem_cocycles eF.hom.2)
          (DGFunctor.isClosed_of_mem_cocycles eG.hom.2) hsq).naturality f)

@[simp]
theorem triangleIsoOfStrictSquare_hom_app
    (K : ConeData α) (hα : IsClosed α)
    (K' : ConeData α') (hα' : IsClosed α')
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α')
    (X : H0 C) :
    (triangleIsoOfStrictSquare K hα K' hα' eF eG hsq).hom.app X =
      squareTriangleMorphism K hα K' hα'
        (DGFunctor.isClosed_of_mem_cocycles eF.hom.2)
        (DGFunctor.isClosed_of_mem_cocycles eG.hom.2) hsq (H0.of C X) := by
  rfl

@[simp]
theorem triangleIsoOfStrictSquare_hom_app_hom₁
    (K : ConeData α) (hα : IsClosed α)
    (K' : ConeData α') (hα' : IsClosed α')
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α')
    (X : H0 C) :
    ((triangleIsoOfStrictSquare K hα K' hα' eF eG hsq).hom.app X).hom₁ =
      (DGFunctor.h0Iso eF).hom.app X :=
  rfl

@[simp]
theorem triangleIsoOfStrictSquare_hom_app_hom₂
    (K : ConeData α) (hα : IsClosed α)
    (K' : ConeData α') (hα' : IsClosed α')
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α')
    (X : H0 C) :
    ((triangleIsoOfStrictSquare K hα K' hα' eF eG hsq).hom.app X).hom₂ =
      (DGFunctor.h0Iso eG).hom.app X :=
  rfl

theorem triangleIsoOfStrictSquare_hom_app_hom₃
    (K : ConeData α) (hα : IsClosed α)
    (K' : ConeData α') (hα' : IsClosed α')
    (eF : (show Z0 (DGFunctor C D) from F) ≅
      (show Z0 (DGFunctor C D) from F'))
    (eG : (show Z0 (DGFunctor C D) from G) ≅
      (show Z0 (DGFunctor C D) from G'))
    (hsq : composition F G G' 0 0 0 (by omega) α eG.hom.val =
      composition F F' G' 0 0 0 (by omega) eF.hom.val α')
    (X : H0 C) :
    ((triangleIsoOfStrictSquare K hα K' hα' eF eG hsq).hom.app X).hom₃ =
      (DGFunctor.h0Iso (K.isoOfStrictSquare K' eF eG hsq)).hom.app X := by
  rw [triangleIsoOfStrictSquare_hom_app, squareTriangleMorphism_hom₃,
    DGFunctor.h0Iso_hom, HomogeneousNatTrans.h0_app]
  exact congrArg (fun z => H0.homMk (C := D) z)
    (Subtype.ext (K.isoOfStrictSquare_hom_app K' eF eG hsq
      (H0.of C X)).symm)

end StrictSquareIso


/-! ### Independence of the chosen cones -/

section Compare

/-- The comparison map between two chosen cones of the same component: the
strict lift of the two identities. -/
noncomputable def compareCone (L M : ConeData α) (X : C) :
    (dgHom (L.obj X) (M.obj X)).X 0 :=
  (L.isCone X).homogeneousLift (M.isCone X) 0 (dgId (F.obj X)) (dgId (G.obj X)) 0

omit [IsPretriangulated D] in
@[simp]
theorem compareCone_self (L : ConeData α) (X : C) :
    compareCone L L X = dgId (L.obj X) :=
  (L.isCone X).homogeneousLift_id

omit [IsPretriangulated D] in
/-- The comparison maps compose.  Both sides are strict lifts, so
`homogeneousLift_strict_comp` applies and the two identities compose to one. -/
theorem compareCone_comp (L M N : ConeData α) (X : C) :
    dgComp 0 0 0 (by omega) (compareCone L M X) (compareCone M N X) =
      compareCone L N X := by
  have hF : dgComp 0 0 (0 + 0) (by omega) (dgId (F.obj X)) (dgId (F.obj X)) =
      dgId (F.obj X) := dgId_comp 0 (dgId (F.obj X))
  have hG : dgComp 0 0 (0 + 0) (by omega) (dgId (G.obj X)) (dgId (G.obj X)) =
      dgId (G.obj X) := dgId_comp 0 (dgId (G.obj X))
  show dgComp 0 0 (0 + 0) (by omega) (compareCone L M X) (compareCone M N X) = _
  rw [compareCone, compareCone, compareCone,
    (L.isCone X).homogeneousLift_strict_comp (M.isCone X) (N.isCone X) 0 0,
    hF, hG]
  rfl

omit [IsPretriangulated D] in
/-- The identity square relating a cone situation to itself.  Both composites
are `α`, by the two unit laws of the dg category of dg functors. -/
theorem id_square :
    composition F G G 0 0 0 (by omega) α (id G) =
      composition F F G 0 0 0 (by omega) (id F) α :=
  (dgComp_id (C := DGFunctor C D) 0 α).trans
    (dgId_comp (C := DGFunctor C D) 0 α).symm

/-- **The triangle functor does not depend on the chosen cones.**

Two `ConeData` for the same transformation are related by the identity square,
so `triangleNatTrans` applies with `u` and `v` the identities.  The
transformation it produces is the objectwise comparison of cones. -/
noncomputable def compareNatTrans (L M : ConeData α) :
    L.triangleFunctor hα ⟶ M.triangleFunctor hα :=
  triangleNatTrans L hα M hα (isClosed_id F) (isClosed_id G) id_square

@[simp]
theorem compareNatTrans_app_hom₁ (L M : ConeData α) (X : H0 C) :
    ((compareNatTrans hα L M).app X).hom₁ =
      𝟙 (F.h0.obj X) :=
  rfl

@[simp]
theorem compareNatTrans_app_hom₂ (L M : ConeData α) (X : H0 C) :
    ((compareNatTrans hα L M).app X).hom₂ =
      𝟙 (G.h0.obj X) :=
  rfl

@[simp]
theorem compareNatTrans_app_hom₃ (L M : ConeData α) (X : H0 C) :
    ((compareNatTrans hα L M).app X).hom₃ =
      H0.homMk (C := D)
        ⟨compareCone L M (H0.of C X),
          (L.isCone (H0.of C X)).lift_closed (M.isCone (H0.of C X)) _ _ _
            (dgId_cocycle _) (dgId_cocycle _)
            (squareAt (isClosed_id F) (isClosed_id G) id_square
              (H0.of C X)).boundary⟩ :=
  rfl

/-- Comparing a cone choice with itself is the identity. -/
@[simp]
theorem compareNatTrans_self (L : ConeData α) :
    compareNatTrans hα L L = 𝟙 (L.triangleFunctor hα) := by
  apply NatTrans.ext
  funext X
  refine Triangle.hom_ext _ _ ?_ ?_ ?_
  · rw [compareNatTrans_app_hom₁, NatTrans.id_app, id_hom₁]
    rfl
  · rw [compareNatTrans_app_hom₂, NatTrans.id_app, id_hom₂]
    rfl
  · rw [compareNatTrans_app_hom₃, NatTrans.id_app, id_hom₃]
    -- The identity of `H⁰` is the class of `dgId` by definition, so `exact`
    -- can read the target subtype off the goal; `Eq.trans` cannot.
    exact congrArg (fun z => H0.homMk (C := D) z)
      (Subtype.ext (compareCone_self L (H0.of C X)))

/-- The comparisons compose. -/
theorem compareNatTrans_comp (L M N : ConeData α) :
    compareNatTrans hα L M ≫ compareNatTrans hα M N = compareNatTrans hα L N := by
  apply NatTrans.ext
  funext X
  refine Triangle.hom_ext _ _ ?_ ?_ ?_
  · rw [NatTrans.comp_app, comp_hom₁, compareNatTrans_app_hom₁,
      compareNatTrans_app_hom₁, compareNatTrans_app_hom₁]
    exact Category.id_comp _
  · rw [NatTrans.comp_app, comp_hom₂, compareNatTrans_app_hom₂,
      compareNatTrans_app_hom₂, compareNatTrans_app_hom₂]
    exact Category.id_comp _
  · rw [NatTrans.comp_app, comp_hom₃, compareNatTrans_app_hom₃,
      compareNatTrans_app_hom₃, compareNatTrans_app_hom₃]
    exact congrArg (fun z => H0.homMk (C := D) z)
      (Subtype.ext (compareCone_comp L M N (H0.of C X)))

/-- **The triangle functors of two cone choices are canonically isomorphic.** -/
noncomputable def compareIso (L M : ConeData α) :
    L.triangleFunctor hα ≅ M.triangleFunctor hα where
  hom := compareNatTrans hα L M
  inv := compareNatTrans hα M L
  hom_inv_id := by rw [compareNatTrans_comp, compareNatTrans_self]
  inv_hom_id := by rw [compareNatTrans_comp, compareNatTrans_self]

@[simp]
theorem compareIso_hom (L M : ConeData α) :
    (compareIso hα L M).hom = compareNatTrans hα L M :=
  rfl

@[simp]
theorem compareIso_inv (L M : ConeData α) :
    (compareIso hα L M).inv = compareNatTrans hα M L :=
  rfl

end Compare

end DGFunctor.HomogeneousNatTrans.ConeData

end CategoryTheory
