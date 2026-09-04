/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids

/-!
# Morphisms and representable fibers of stacks in groupoids

Stack morphisms, their fiber categories, and representability by an object of
an arbitrary site are generic category theory.  Geometric properties of the
representing morphism remain in the corresponding geometric consumer layer.
-/

namespace CategoryTheory

open Bicategory Opposite

noncomputable section

universe v w u

/-- A morphism of stacks is a strong transformation between their underlying
pseudofunctors.  Pullback naturality, identities, and composition are supplied
by Mathlib's pseudofunctor API. -/
abbrev StackMorphism {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (F G : StackInGroupoids C J) :=
  Pseudofunctor.StrongTrans F.presheaf G.presheaf

namespace StackMorphism

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {F G H I : StackInGroupoids C J}

open scoped Pseudofunctor.StrongTrans

/-- The functor induced by a stack morphism on the fiber over `S`. -/
abbrev app (f : StackMorphism F G) (S : C) :
    Functor (F.presheaf.obj (.mk (op S)))
      (G.presheaf.obj (.mk (op S))) :=
  (Pseudofunctor.StrongTrans.app f (.mk (op S))).toFunctor

/-- The pseudonatural pullback comparison of a stack morphism along a site
morphism. -/
abbrev pullbackIso (f : StackMorphism F G) {S T : C} (g : T ⟶ S) :
    (F.presheaf.map g.op.toLoc).toFunctor ⋙ f.app T ≅
      f.app S ⋙ (G.presheaf.map g.op.toLoc).toFunctor :=
  Cat.Hom.toNatIso (f.naturality g.op.toLoc)

/-- The identity stack morphism, including its pseudonaturality coherence. -/
abbrev id (F : StackInGroupoids C J) : StackMorphism F F :=
  Pseudofunctor.StrongTrans.id F.presheaf

/-- Composition of stack morphisms. -/
abbrev comp (f : StackMorphism F G) (g : StackMorphism G H) :
    StackMorphism F H :=
  Pseudofunctor.StrongTrans.vcomp f g

/-- A 2-morphism between stack morphisms is a modification. -/
abbrev Modification (f g : StackMorphism F G) :=
  Pseudofunctor.StrongTrans.Modification f g

/-- The groupoid fiber of a stack morphism over a test object and a chosen
target object. -/
abbrev FiberCategory (f : StackMorphism F G) {S : C}
    (y : G.presheaf.obj (.mk (op S))) (T : Over S) :=
  Core (StructuredArrow
    ((G.presheaf.map T.hom.op.toLoc).toFunctor.obj y)
    (f.app T.left))

/-- An object of the site representing one fiber of a stack morphism. -/
structure FiberRepresentation (f : StackMorphism F G) {S : C}
    (y : G.presheaf.obj (.mk (op S))) where
  /-- The representing object over `S`. -/
  representing : Over S
  /-- The Yoneda comparison on every test object over `S`. -/
  fiberEquivalence (T : Over S) :
    Discrete (T ⟶ representing) ≌ f.FiberCategory y T

/-- A stack morphism is representable when every fiber over a test object has
a representing object of the site. -/
class IsRepresentable (f : StackMorphism F G) : Prop where
  representation {S : C} (y : G.presheaf.obj (.mk (op S))) :
    Nonempty (f.FiberRepresentation y)

end StackMorphism

end


end CategoryTheory
