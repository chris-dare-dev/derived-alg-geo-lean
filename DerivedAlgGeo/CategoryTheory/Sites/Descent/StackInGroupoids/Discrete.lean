/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids

/-!
# Discrete stacks from sheaves of types

An ordinary sheaf of types on an arbitrary site determines a stack in
discrete groupoids.  This construction is purely site-theoretic; algebraic
geometry consumes it for representable big-Zariski stacks.
-/

namespace CategoryTheory

open Bicategory Opposite

noncomputable section

universe t v w u

/-- Regard a presheaf of types as a pseudofunctor into discrete categories. -/
def discretePseudofunctor {C : Type u} [Category.{v} C]
    (P : Functor Cᵒᵖ (Type w)) :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w} :=
  (P ⋙ typeToCat).toPseudofunctor'

instance discretePseudofunctor_obj_isDiscrete
    {C : Type u} [Category.{v} C] (P : Functor Cᵒᵖ (Type w))
    (X : LocallyDiscrete Cᵒᵖ) :
    IsDiscrete ((discretePseudofunctor P).obj X) := by
  change IsDiscrete (Discrete _)
  infer_instance

instance discretePseudofunctor_obj_isGroupoid
    {C : Type u} [Category.{v} C] (P : Functor Cᵒᵖ (Type w))
    (X : LocallyDiscrete Cᵒᵖ) :
    IsGroupoid ((discretePseudofunctor P).obj X) := by
  infer_instance

namespace DiscretePseudofunctor

variable {C : Type u} [Category.{v} C]
  {P : Functor Cᵒᵖ (Type w)} {I : Type t} {S : C} {X : I → C}
  (f : ∀ i, X i ⟶ S)

private def descentFamily
    (D : (discretePseudofunctor P).DescentData f) (i : I) :
    P.obj (op (X i)) :=
  (D.obj i).as

private lemma descentFamily_compatible
    (D : (discretePseudofunctor P).DescentData f) :
    Presieve.Arrows.Compatible P f (descentFamily f D) := by
  intro i j Z gi gj h
  have e := Discrete.eq_of_hom (D.hom (gi ≫ f i) gi gj rfl h.symm)
  change P.map gi.op (D.obj i).as = P.map gj.op (D.obj j).as at e
  exact e

private theorem toDescentData_essSurj
    (hP : Presieve.IsSheafFor P (Presieve.ofArrows X f)) :
    (discretePseudofunctor P).toDescentData f |>.EssSurj :=
  ⟨fun D ↦ by
    obtain ⟨a, ha, -⟩ :=
      (Presieve.isSheafFor_arrows_iff P f).1 hP
        (descentFamily f D) (descentFamily_compatible f D)
    refine ⟨Discrete.mk a, ⟨?_⟩⟩
    exact Pseudofunctor.DescentData.isoMk
      (fun i ↦ Discrete.eqToIso (by
        change P.map (f i).op a = (D.obj i).as
        exact ha i))
      (by
        intro Z _ _ _ _ _ _ _
        letI : IsDiscrete ((discretePseudofunctor P).obj (.mk (op Z))) :=
          discretePseudofunctor_obj_isDiscrete P _
        apply Subsingleton.elim)⟩

private def toDescentData_fullyFaithful
    (hP : Presieve.IsSheafFor P (Presieve.ofArrows X f)) :
    (discretePseudofunctor P).toDescentData f |>.FullyFaithful := by
  let F := (discretePseudofunctor P).toDescentData f
  letI : F.Faithful :=
    ⟨fun {_ _} _ _ _ ↦ by
      letI : IsDiscrete ((discretePseudofunctor P).obj (.mk (op S))) :=
        discretePseudofunctor_obj_isDiscrete P _
      apply Subsingleton.elim⟩
  letI : F.Full :=
    ⟨fun {A B} g ↦ by
      have heq : A.as = B.as :=
        ((Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible P f).1 hP).1 (by
          apply Subtype.ext
          funext i
          exact Discrete.eq_of_hom (g.hom i))
      refine ⟨Discrete.eqToHom heq, ?_⟩
      ext i
      letI : IsDiscrete ((discretePseudofunctor P).obj (.mk (op (X i)))) :=
        discretePseudofunctor_obj_isDiscrete P _
      apply Subsingleton.elim⟩
  exact Functor.FullyFaithful.ofFullyFaithful F

private theorem toDescentData_isEquivalence
    (hP : Presieve.IsSheafFor P (Presieve.ofArrows X f)) :
    (discretePseudofunctor P).toDescentData f |>.IsEquivalence := by
  let hff := toDescentData_fullyFaithful f hP
  letI := hff.full
  letI := hff.faithful
  exact ⟨inferInstance, inferInstance, toDescentData_essSurj f hP⟩

end DiscretePseudofunctor

/-- A sheaf of types is a stack in discrete groupoids. -/
theorem discretePseudofunctor_isStack
    {C : Type u} [Category.{v} C] {P : Functor Cᵒᵖ (Type w)}
    {J : GrothendieckTopology C} (hP : Presieve.IsSheaf J P) :
    (discretePseudofunctor P).IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro S R hR
  obtain ⟨I, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [Pseudofunctor.IsStackFor_generate_iff,
    Pseudofunctor.isStackFor_ofArrows_iff]
  apply DiscretePseudofunctor.toDescentData_isEquivalence
  apply (Presieve.isSheafFor_iff_generate _).mpr
  exact hP _ hR

/-- Package a sheaf of types as a stack in discrete groupoids. -/
def stackInGroupoidsOfSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (P : Functor Cᵒᵖ (Type w)) (hP : Presieve.IsSheaf J P) :
    StackInGroupoids C J where
  presheaf := discretePseudofunctor P
  fiberIsGroupoid _ := inferInstance
  isStack := discretePseudofunctor_isStack hP

end

end CategoryTheory
