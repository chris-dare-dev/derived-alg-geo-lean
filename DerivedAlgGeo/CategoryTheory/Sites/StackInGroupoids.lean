/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Stacks in groupoids

This file packages Mathlib's stack condition together with the additional
groupoid-valued requirement used in algebraic geometry.  Covers and Čech
descent are the existing `Sieve`, `Presieve`, and `Pseudofunctor.DescentData`
objects: this layer does not replace them with parallel definitions.

The construction is owned by `CategoryTheory/Sites`: it is generic in a
category and a Grothendieck topology and imports no algebraic geometry.  The
declarations use the matching `CategoryTheory` namespace.

`StackInGroupoids` deliberately contains no algebraicity, representability,
boundedness, or finiteness assertion.  The only conditions are groupoid-valued
fibers and effective descent for a chosen Grothendieck topology.
-/

namespace CategoryTheory

open CategoryTheory
open CategoryTheory.Bicategory
open Opposite

noncomputable section

universe t v w u

/-- A groupoid-valued pseudofunctor satisfying effective descent for `J`. -/
structure StackInGroupoids (C : Type u) [Category.{v} C]
    (J : GrothendieckTopology C) where
  /-- The contravariant groupoid-valued pseudofunctor. -/
  presheaf : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}
  /-- Every fiber is a groupoid. -/
  fiberIsGroupoid (X : LocallyDiscrete Cᵒᵖ) : IsGroupoid (presheaf.obj X)
  /-- Objects and morphisms satisfy effective descent for `J`. -/
  isStack : presheaf.IsStack J

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

instance presheaf_obj_isGroupoid
    (F : StackInGroupoids C J) (X : LocallyDiscrete Cᵒᵖ) :
    IsGroupoid (F.presheaf.obj X) :=
  F.fiberIsGroupoid X

instance presheaf_isStack (F : StackInGroupoids C J) :
    F.presheaf.IsStack J :=
  F.isStack

/-- An explicitly indexed covering family for a Grothendieck topology. -/
structure Cover (S : C) where
  /-- The indexing type of the covering family. -/
  index : Type t
  /-- Schemes or site objects in the covering family. -/
  obj : index → C
  /-- The covering arrows. -/
  hom (i : index) : obj i ⟶ S
  /-- The arrows generate a covering sieve. -/
  mem : Sieve.ofArrows obj hom ∈ J S

/-- The category of Čech descent data for a covering family. -/
abbrev CechDescent (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :=
  F.presheaf.DescentData U.hom

/-- Restrict an object and its morphisms to Čech descent data. -/
abbrev toCechDescent (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :=
  F.presheaf.toDescentData U.hom

/-- The stack condition identifies a fiber with the category of Čech descent
data for every covering family. -/
def cechDescentEquivalence (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :
    F.presheaf.obj (.mk (op S)) ≌ F.CechDescent U := by
  letI := F.presheaf.isEquivalence_toDescentData U.hom U.mem
  exact (F.toCechDescent U).asEquivalence

/-- Morphisms satisfy descent: restriction to a cover is fully faithful. -/
def fullyFaithfulToCechDescent (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :
    (F.toCechDescent U).FullyFaithful :=
  F.presheaf.fullyFaithfulToDescentData U.hom U.mem

/-- Objects satisfy effective descent: every Čech descent object comes from an
object over the base, up to isomorphism. -/
theorem essSurjToCechDescent (F : StackInGroupoids C J) {S : C}
    (U : Cover (J := J) S) :
    (F.toCechDescent U).EssSurj := by
  letI := F.presheaf.isEquivalence_toDescentData U.hom U.mem
  infer_instance

end StackInGroupoids

/-! ## Transport of the stack condition -/

/-- Descent-compatible equivalence data between two pseudofunctors.

Mathlib currently has the pseudofunctor and descent-data APIs but no general
pseudonatural-equivalence API.  This structure records exactly the two
equivalences and comparison square needed to transport the stack condition;
it does not hide them behind an unproved equivalence principle. -/
structure StackEquivalence {C : Type u} [Category.{v} C]
    (F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}) where
  /-- Equivalence on each fiber. -/
  fiber (S : C) : F.obj (.mk (op S)) ≌ G.obj (.mk (op S))
  /-- Equivalence on descent data for every sieve. -/
  descent {S : C} (R : Sieve S) :
    F.DescentData (fun (f : R.arrows.category) ↦ f.obj.hom) ≌
      G.DescentData (fun (f : R.arrows.category) ↦ f.obj.hom)
  /-- Restriction to descent data commutes with the two equivalences. -/
  comparison {S : C} (R : Sieve S) :
    F.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom) ⋙
        (descent R).functor ≅
      (fiber S).functor ⋙
        G.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)

namespace StackEquivalence

variable {C : Type u} [Category.{v} C]
  {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w}}

private theorem isStackFor_forward (e : StackEquivalence F G)
    {J : GrothendieckTopology C} [F.IsStack J]
    {S : C} (R : Sieve S) (hR : R ∈ J S) :
    G.IsStackFor R.arrows := by
  let f := fun (a : R.arrows.category) ↦ a.obj.hom
  letI : (F.toDescentData f).IsEquivalence :=
    (F.isStackFor' R hR).isEquivalence
  letI : (e.descent R).functor.IsEquivalence :=
    inferInstance
  letI : (F.toDescentData f ⋙ (e.descent R).functor).IsEquivalence :=
    inferInstance
  letI : ((e.fiber S).functor ⋙ G.toDescentData f).IsEquivalence :=
    Functor.isEquivalence_of_iso (e.comparison R)
  exact ⟨Functor.isEquivalence_of_comp_left
    (e.fiber S).functor (G.toDescentData f)⟩

private theorem isStackFor_backward (e : StackEquivalence F G)
    {J : GrothendieckTopology C} [G.IsStack J]
    {S : C} (R : Sieve S) (hR : R ∈ J S) :
    F.IsStackFor R.arrows := by
  let f := fun (a : R.arrows.category) ↦ a.obj.hom
  letI : (G.toDescentData f).IsEquivalence :=
    (G.isStackFor' R hR).isEquivalence
  letI : (e.fiber S).functor.IsEquivalence :=
    inferInstance
  letI : ((e.fiber S).functor ⋙ G.toDescentData f).IsEquivalence :=
    inferInstance
  letI : (F.toDescentData f ⋙ (e.descent R).functor).IsEquivalence :=
    Functor.isEquivalence_of_iso (e.comparison R).symm
  letI : (e.descent R).functor.IsEquivalence :=
    inferInstance
  exact ⟨Functor.isEquivalence_of_comp_right
    (F.toDescentData f) (e.descent R).functor⟩

/-- The stack condition is invariant under descent-compatible equivalence. -/
theorem isStack_iff (e : StackEquivalence F G)
    (J : GrothendieckTopology C) :
    F.IsStack J ↔ G.IsStack J := by
  constructor
  · intro hF
    letI := hF
    exact Pseudofunctor.IsStack.of_isStackFor
      (fun _ R hR ↦ e.isStackFor_forward R hR)
  · intro hG
    letI := hG
    exact Pseudofunctor.IsStack.of_isStackFor
      (fun _ R hR ↦ e.isStackFor_backward R hR)

end StackEquivalence

/-- Transport a stack in groupoids across descent-compatible equivalence.
The groupoid condition on the target fibers remains explicit. -/
def StackInGroupoids.ofEquivalence {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (F : StackInGroupoids C J)
    (G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w, w})
    (e : StackEquivalence F.presheaf G)
    (hG : ∀ X, IsGroupoid (G.obj X)) : StackInGroupoids C J where
  presheaf := G
  fiberIsGroupoid := hG
  isStack := (e.isStack_iff J).1 F.isStack

end

end CategoryTheory
