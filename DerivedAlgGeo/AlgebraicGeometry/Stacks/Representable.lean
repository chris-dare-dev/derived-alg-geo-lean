/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Core
import Mathlib.CategoryTheory.Groupoid.Discrete
import Mathlib.CategoryTheory.Sites.EffectiveEpimorphic
import DerivedAlgGeo.CategoryTheory.Sites.StackInGroupoids

/-!
# Discrete and representable stacks

An ordinary sheaf of types determines a stack in discrete groupoids.  The
proof below connects Mathlib's componentwise sheaf condition to its category
of descent data: separatedness gives full faithfulness, and amalgamation gives
essential surjectivity.

For the big Zariski site, the Yoneda presheaf of every scheme is a sheaf by
subcanonicity.  This produces a concrete, nonconstant representable stack whose
objects over `T` are precisely scheme morphisms `T ⟶ X`.
-/

namespace AlgebraicGeometry

open CategoryTheory
open CategoryTheory.Bicategory
open Opposite

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

/-! ## Coherent and representable morphism interfaces -/

/-- A morphism of stacks is a strong transformation between their underlying
pseudofunctors.  Thus the pullback comparison is pseudonatural: its naturality,
identity, and composition laws are part of Mathlib's
`Pseudofunctor.StrongTrans`, rather than additional unchecked data. -/
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
target object. Objects are lifts together with an isomorphism to the pulled
back target object. -/
abbrev FiberCategory (f : StackMorphism F G) {S : C}
    (y : G.presheaf.obj (.mk (op S))) (T : Over S) :=
  Core (StructuredArrow
    ((G.presheaf.map T.hom.op.toLoc).toFunctor.obj y)
    (f.app T.left))

/-- A scheme- or site-object representation of one fiber of a stack
morphism.  It identifies lifts over every test object with arrows to a fixed
representing object over the base. -/
structure FiberRepresentation (f : StackMorphism F G) {S : C}
    (y : G.presheaf.obj (.mk (op S))) where
  /-- The representing object over `S`. -/
  representing : Over S
  /-- The Yoneda comparison on every test object over `S`. -/
  fiberEquivalence (T : Over S) :
    Discrete (T ⟶ representing) ≌ f.FiberCategory y T

/-- A stack morphism is representable when every fiber over a test object has
a representing object.  This is intentionally separate from being a stack. -/
class IsRepresentable (f : StackMorphism F G) : Prop where
  representation {S : C} (y : G.presheaf.obj (.mk (op S))) :
    Nonempty (f.FiberRepresentation y)

end StackMorphism

/-! ## The representable big-Zariski stack -/

/-- The big-Zariski stack represented by a scheme `X`. -/
def representableZariskiStack (X : Scheme.{u}) :
    StackInGroupoids Scheme.{u} Scheme.zariskiTopology :=
  stackInGroupoidsOfSheaf Scheme.zariskiTopology (yoneda.obj X)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (J := Scheme.zariskiTopology.{u}) (yoneda.obj X))

/-- The stack represented by `X` has effective Čech descent for every big
Zariski covering family. -/
def representableZariskiCechDescentEquivalence
    (X S : Scheme.{u})
    (U : StackInGroupoids.Cover (J := Scheme.zariskiTopology) S) :=
  (representableZariskiStack X).cechDescentEquivalence U

/-- A morphism `T ⟶ X`, regarded as an object of the stack represented by
`X` over `T`. -/
def representableZariskiObject {X T : Scheme.{u}} (f : T ⟶ X) :
    (representableZariskiStack X).presheaf.obj (.mk (op T)) :=
  Discrete.mk f

/-- The representable stack remembers its scheme morphisms faithfully. -/
theorem representableZariskiObject_injective {X T : Scheme.{u}} :
    Function.Injective (representableZariskiObject (X := X) (T := T)) := by
  intro f g h
  exact congrArg Discrete.as h

end

end AlgebraicGeometry
