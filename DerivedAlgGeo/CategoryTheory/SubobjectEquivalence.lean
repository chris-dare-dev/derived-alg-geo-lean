/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Subobjects along a functor, and the order isomorphism from an equivalence

Mathlib maps subobjects along a morphism (`Subobject.map`) and along an isomorphism *of objects*
(`Subobject.mapIsoToOrderIso`), both inside a single category. It does not map them along a
**functor**, so an equivalence of categories does not yet carry subobject lattices to subobject
lattices.

This file supplies that. `mapFunctor` pushes a subobject forward along any mono-preserving functor,
and `mapEquivalence` upgrades it to an order isomorphism when the functor is half of an
equivalence.

## Why an order isomorphism and not just a monotone map

The consumers are chain conditions and filtrations. A monotone map carries a chain to a chain, but
it does not carry a *strictly* increasing chain to a strictly increasing one, and it need not carry
the bottom and top to the bottom and top. An order isomorphism does all three, which is what makes
it possible to transport a Harder–Narasimhan filtration along an equivalence.

## The shape of the proofs

Every proof is induction on a subobject down to a representing mono, after which both sides are
`mk` of an explicit morphism and the statement is `mk_eq_mk_of_comm` against a comparison
isomorphism. The only step with content is `mapFunctor_inverse_functor`, where naturality of the
unit turns the round trip into composition with a unit component, which is invertible.
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Subobject

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

section MapFunctor

variable (F : A ⥤ B) [F.PreservesMonomorphisms]

/-- **A subobject pushed forward along a mono-preserving functor.** -/
def mapFunctor {X : A} : Subobject X → Subobject (F.obj X) :=
  Subobject.lift (fun _ f _ ↦ Subobject.mk (F.map f))
    (by
      intro A₁ A₂ f g _ _ i hi
      exact Subobject.mk_eq_mk_of_comm _ _ (F.mapIso i)
        (by rw [Functor.mapIso_hom, ← F.map_comp, hi]))

@[simp]
theorem mapFunctor_mk {X A₁ : A} (f : A₁ ⟶ X) [Mono f] :
    mapFunctor F (Subobject.mk f) = Subobject.mk (F.map f) :=
  rfl

theorem mapFunctor_eq_mk_arrow {X : A} (P : Subobject X) :
    mapFunctor F P = Subobject.mk (F.map P.arrow) := by
  conv_lhs => rw [← Subobject.mk_arrow P]
  rfl

theorem mapFunctor_monotone {X : A} : Monotone (mapFunctor F (X := X)) := by
  intro P Q h
  rw [mapFunctor_eq_mk_arrow, mapFunctor_eq_mk_arrow]
  refine Subobject.mk_le_mk_of_comm (F.map (Subobject.ofLE P Q h)) ?_
  rw [← F.map_comp, Subobject.ofLE_arrow]

/-- Pushing forward along the identity does nothing. -/
theorem mapFunctor_id {X : A} (P : Subobject X) : mapFunctor (𝟭 A) P = P := by
  rw [mapFunctor_eq_mk_arrow]
  exact Subobject.mk_arrow P

/-- Pushing forward along a composite is pushing forward twice. It holds by definition. -/
theorem mapFunctor_comp (G : B ⥤ A) [G.PreservesMonomorphisms]
    [(F ⋙ G).PreservesMonomorphisms] {X : A} (P : Subobject X) :
    mapFunctor (F ⋙ G) P = mapFunctor G (mapFunctor F P) := by
  induction P using Subobject.ind with
  | h f => rfl

/-- Pushing forward commutes with rewriting the ambient object along an isomorphism. -/
theorem mapFunctor_map_hom {X Y : A} (i : X ≅ Y) (P : Subobject X) :
    mapFunctor F ((Subobject.map i.hom).obj P) =
      (Subobject.map (F.map i.hom)).obj (mapFunctor F P) := by
  induction P using Subobject.ind with
  | h f => simp only [Subobject.map_mk, mapFunctor_mk, F.map_comp]

/-- Mapping along an isomorphism and back is the identity. Stated as a lemma rather than reached
by `rw [← map_comp]`, whose motive is not type correct here: `Subobject.map` carries a `Mono`
instance argument that changes under the rewrite. -/
theorem map_inv_map_hom {X Y : A} (i : X ≅ Y) (P : Subobject X) :
    (Subobject.map i.inv).obj ((Subobject.map i.hom).obj P) = P := by
  induction P using Subobject.ind with
  | h f =>
      haveI : Mono (f ≫ i.hom) := mono_comp _ _
      simp only [Subobject.map_mk, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem map_hom_map_inv {X Y : A} (i : X ≅ Y) (Q : Subobject Y) :
    (Subobject.map i.hom).obj ((Subobject.map i.inv).obj Q) = Q := by
  induction Q using Subobject.ind with
  | h f =>
      haveI : Mono (f ≫ i.inv) := mono_comp _ _
      simp only [Subobject.map_mk, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end MapFunctor

section MapEquivalence

variable (e : A ≌ B) [e.functor.PreservesMonomorphisms] [e.inverse.PreservesMonomorphisms]

/-- The unit of an equivalence at `X`, with both endpoints spelled out.

`e.unitIso.app X` has type `(𝟭 A).obj X ≅ (e.functor ⋙ e.inverse).obj X`. That is definitionally
what is wanted but not syntactically, and the difference defeats `rw` on `Subobject.map`, whose
statements are dependent in the ambient object. Naming the isomorphism with its endpoints spelled
out is what makes the rewrites below go through. -/
def unitAt (X : A) : X ≅ e.inverse.obj (e.functor.obj X) := e.unitIso.app X

omit [e.functor.PreservesMonomorphisms] [e.inverse.PreservesMonomorphisms] in
theorem unitAt_naturality {X Y : A} (f : X ⟶ Y) :
    f ≫ (unitAt e Y).hom = (unitAt e X).hom ≫ e.inverse.map (e.functor.map f) :=
  e.unitIso.hom.naturality f

/-- **The round trip through an equivalence is the unit isomorphism.**

This is the one step with content: naturality of the unit rewrites the round trip as composition
with a unit component, and that component is invertible, so the two subobjects agree. -/
theorem mapFunctor_inverse_functor {X : A} (P : Subobject X) :
    mapFunctor e.inverse (mapFunctor e.functor P) =
      (Subobject.map (unitAt e X).hom).obj P := by
  induction P using Subobject.ind with
  | h f =>
      haveI : Mono (e.functor.map f) := inferInstance
      haveI : Mono (e.inverse.map (e.functor.map f)) := inferInstance
      haveI : Mono (f ≫ (unitAt e X).hom) := mono_comp _ _
      simp only [mapFunctor_mk, Subobject.map_mk]
      refine (Subobject.mk_eq_mk_of_comm _ _ (unitAt e _) ?_).symm
      exact (unitAt_naturality e f).symm

/-- **The order isomorphism on subobjects induced by an equivalence.** -/
def mapEquivalence (X : A) : Subobject X ≃o Subobject (e.functor.obj X) where
  toFun := mapFunctor e.functor
  invFun := fun Q ↦ (Subobject.map (unitAt e X).inv).obj (mapFunctor e.inverse Q)
  left_inv := by
    intro P
    dsimp only
    rw [mapFunctor_inverse_functor]
    exact map_inv_map_hom (unitAt e X) P
  right_inv := by
    intro Q
    dsimp only
    induction Q using Subobject.ind with
    | h g =>
        haveI : Mono (e.inverse.map g) := inferInstance
        haveI : Mono (e.inverse.map g ≫ (unitAt e X).inv) := mono_comp _ _
        have hc : e.functor.map ((unitAt e X).inv) =
            (e.counitIso.app (e.functor.obj X)).hom :=
          (Equivalence.counit_app_functor e X).symm
        simp only [mapFunctor_mk, Subobject.map_mk, Functor.map_comp, hc]
        haveI : Mono (e.functor.map (e.inverse.map g) ≫
            (e.counitIso.app (e.functor.obj X)).hom) := mono_comp _ _
        exact Subobject.mk_eq_mk_of_comm _ _ (e.counitIso.app _)
          (e.counitIso.hom.naturality g).symm
  map_rel_iff' := by
    intro P Q
    refine ⟨fun h ↦ ?_, fun h ↦ mapFunctor_monotone _ h⟩
    have hle : (Subobject.map (unitAt e X).hom).obj P ≤
        (Subobject.map (unitAt e X).hom).obj Q := by
      rw [← mapFunctor_inverse_functor, ← mapFunctor_inverse_functor]
      exact mapFunctor_monotone e.inverse h
    have h2 := (Subobject.map (unitAt e X).inv).monotone hle
    simpa only [map_inv_map_hom] using h2

@[simp]
theorem mapEquivalence_apply (X : A) (P : Subobject X) :
    mapEquivalence e X P = mapFunctor e.functor P := rfl

end MapEquivalence

section Cokernel

variable [Abelian A] [Abelian B] (F : A ⥤ B) [F.PreservesZeroMorphisms]
  [F.PreservesMonomorphisms] [PreservesFiniteColimits F]

/-- **The underlying object of a pushed-forward subobject** is the image of the underlying object.

`mapFunctor F P` is only propositionally `mk (F.map P.arrow)`, so this is an `isoOfEqMk` rather
than a definitional equality. -/
noncomputable def mapFunctorIso {X : A} (P : Subobject X) :
    ((mapFunctor F P : Subobject (F.obj X)) : B) ≅ F.obj (P : A) :=
  Subobject.isoOfEqMk _ (F.map P.arrow) (mapFunctor_eq_mk_arrow F P)

omit [Abelian A] [Abelian B] [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] in
@[reassoc (attr := simp)]
theorem mapFunctorIso_hom_arrow {X : A} (P : Subobject X) :
    (mapFunctorIso F P).hom ≫ F.map P.arrow = (mapFunctor F P).arrow := by
  simp [mapFunctorIso]

omit [Abelian A] [Abelian B] [F.PreservesZeroMorphisms] [PreservesFiniteColimits F] in
/-- **The chain step transports.** Both sides are maps into a subobject, so it is enough to compose
with its arrow, which is a mono. -/
theorem ofLE_mapFunctor {X : A} {P Q : Subobject X} (h : P ≤ Q) :
    Subobject.ofLE (mapFunctor F P) (mapFunctor F Q) (mapFunctor_monotone F h) ≫
        (mapFunctorIso F Q).hom =
      (mapFunctorIso F P).hom ≫ F.map (Subobject.ofLE P Q h) := by
  haveI : Mono (F.map Q.arrow) := inferInstance
  refine (cancel_mono (F.map Q.arrow)).1 ?_
  rw [Category.assoc, mapFunctorIso_hom_arrow, Subobject.ofLE_arrow, Category.assoc,
    ← F.map_comp, Subobject.ofLE_arrow, mapFunctorIso_hom_arrow]

/-- **The successive quotient transports.**

This is what a Harder–Narasimhan filtration needs beyond the order isomorphism: its factors are
cokernels of chain steps, and they must be identified with the images of the original factors.
The square of `ofLE_mapFunctor` is an isomorphism square, so the cokernels agree; then `F`
preserving finite colimits moves the cokernel inside. -/
noncomputable def cokernelOfLEMapFunctorIso {X : A} {P Q : Subobject X} (h : P ≤ Q) :
    cokernel (Subobject.ofLE (mapFunctor F P) (mapFunctor F Q) (mapFunctor_monotone F h)) ≅
      F.obj (cokernel (Subobject.ofLE P Q h)) :=
  (cokernel.mapIso _ (F.map (Subobject.ofLE P Q h)) (mapFunctorIso F P) (mapFunctorIso F Q)
      (ofLE_mapFunctor F h)).trans
    (PreservesCokernel.iso F (Subobject.ofLE P Q h)).symm

end Cokernel

end CategoryTheory.Subobject
