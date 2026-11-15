/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Canonical
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Discrete
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Morphism
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.ULift

/-!
# Representable stacks on subcanonical sites

A subcanonical topology makes every Yoneda presheaf a sheaf and hence a discrete stack. Its
universe lift places the represented stack in any fibre universes `Cat.{max v w₁, max v w₂}`.

## Main definitions

* `CategoryTheory.StackInGroupoids.representable` constructs the stack represented by an object.
* `CategoryTheory.StackInGroupoids.representableObj` is the object of the represented stack
  given by a morphism to the representing object, and
  `CategoryTheory.StackInGroupoids.representableObjEquiv` identifies all its objects with such
  morphisms.
* `CategoryTheory.StackInGroupoids.representableMap` induces its maps by postcomposition.

## Main results

* `CategoryTheory.StackInGroupoids.representableObj_injective`: the represented stack remembers
  morphisms to the representing object.
* `CategoryTheory.StackInGroupoids.representableMap_app_obj` records the definitional action.
* `CategoryTheory.StackInGroupoids.representable_ofLE` identifies restriction to a coarser site.

## Implementation notes

The construction reuses `CategoryTheory.stackInGroupoidsOfSheaf`: subcanonicity supplies its
sheaf proof, rather than an additional descent hypothesis. Its fibres `Discrete (T ⟶ X)` lie in
`Cat.{v, v}`. `CategoryTheory.StackInGroupoids.ulift` then raises the morphism universe by `w₁`
and the object universe by `w₂`, so a represented stack maps into stacks whose fibres are
sheaves (`Cat.{u, u + 1}`) as well as complexes (`Cat.{u + 1, u + 1}`).

The fibres of the lift are thin, so `CategoryTheory.StackInGroupoids.representableMap` is built
directly: its components are those of `CategoryTheory.StackInGroupoids.discreteMap` conjugated
by the lift, and its coherence conditions hold because parallel morphisms in a fibre are equal.

## References

Mathlib's `CategoryTheory/Sites/Canonical.lean` supplies the represented-sheaf theorem.
[Stacks Project, Tag 0268](https://stacks.math.columbia.edu/tag/0268) describes stacks by their
fibre-to-descent-data equivalences, the condition carried by the existing sheaf-to-stack root.
[Stacks Project, Tag 0305](https://stacks.math.columbia.edu/tag/0305) is the stack associated to
a sheaf.

## Tags

subcanonical sites, representable stacks, discrete groupoids, universe lift
-/

namespace CategoryTheory

open Opposite

noncomputable section

universe w₁ w₂ v u

namespace StackInGroupoids

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]

/-- The stack represented by `X` on a subcanonical site: the universe lift
`CategoryTheory.StackInGroupoids.ulift` of the discrete stack of `yoneda.obj X`, constructed by
`CategoryTheory.stackInGroupoidsOfSheaf`. Its objects over `T` are the morphisms `T ⟶ X`.

Its fibres lie in `Cat.{max v w₁, max v w₂}`. Taking `w₁ = w₂ = v` gives fibres in
`Cat.{v, v}` that are equivalent to those of `stackInGroupoidsOfSheaf J (yoneda.obj X)`, by
`CategoryTheory.Pseudofunctor.ulift.objEquivalence`, but not definitionally equal to them. -/
def representable (X : C) : StackInGroupoids.{max v w₁, v, max v w₂, u} C J :=
  (stackInGroupoidsOfSheaf J (yoneda.obj X)
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj X))).ulift

instance representable_presheaf_obj_isDiscrete (X : C) (T : LocallyDiscrete Cᵒᵖ) :
    IsDiscrete ((representable.{w₁, w₂} J X).presheaf.obj T) :=
  Pseudofunctor.ulift.isDiscrete_obj (discretePseudofunctor (yoneda.obj X)) T

/-- A morphism `g : T ⟶ X`, regarded as an object of the stack represented by `X` over `T`. -/
def representableObj {X T : C} (g : T ⟶ X) :
    (representable.{w₁, w₂} J X).presheaf.obj (.mk (op T)) :=
  (Pseudofunctor.ulift.objEquivalence _ _).functor.obj (Discrete.mk g)

/-- The objects of the stack represented by `X` over `T` are the morphisms `T ⟶ X`. -/
@[simps apply]
def representableObjEquiv {X T : C} :
    (T ⟶ X) ≃ (representable.{w₁, w₂} J X).presheaf.obj (.mk (op T)) where
  toFun := representableObj J
  invFun x := Discrete.as ((Pseudofunctor.ulift.objEquivalence
    (discretePseudofunctor (yoneda.obj X)) (.mk (op T))).inverse.obj x)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The represented stack remembers its morphisms to the representing object. -/
theorem representableObj_injective {X T : C} :
    Function.Injective (representableObj.{w₁, w₂} (J := J) (X := X) (T := T)) :=
  (representableObjEquiv J).injective

/-- A morphism induces `CategoryTheory.StackInGroupoids.representableMap` by postcomposition
on each fibre of the corresponding representable stacks. -/
def representableMap {X Y : C} (f : X ⟶ Y) :
    StackMorphism (representable.{w₁, w₂} J X) (representable.{w₁, w₂} J Y) where
  app T := ((Pseudofunctor.ulift.objEquivalence _ T).inverse ⋙
    ((discretePseudofunctorMap (yoneda.map f)).app T).toFunctor ⋙
      (Pseudofunctor.ulift.objEquivalence _ T).functor).toCatHom
  naturality {a b} g := Cat.Hom.isoMk (NatIso.ofComponents
    (fun x ↦ eqToIso (congrArg (fun k ↦ (Pseudofunctor.ulift.objEquivalence
        (discretePseudofunctor (yoneda.obj Y)) b).functor.obj (Discrete.mk k))
      (Category.assoc g.as.unop (Discrete.as ((Pseudofunctor.ulift.objEquivalence
        (discretePseudofunctor (yoneda.obj X)) a).inverse.obj x)) f)))
    (fun _ ↦ Subsingleton.elim _ _))
  naturality_naturality _ := Cat.Hom₂.ext (NatTrans.ext (funext fun _ ↦ Subsingleton.elim _ _))
  naturality_id _ := Cat.Hom₂.ext (NatTrans.ext (funext fun _ ↦ Subsingleton.elim _ _))
  naturality_comp _ _ := Cat.Hom₂.ext (NatTrans.ext (funext fun _ ↦ Subsingleton.elim _ _))

/-- The component functors of `CategoryTheory.StackInGroupoids.representableMap` act by
postcomposition, definitionally. -/
@[simp]
theorem representableMap_app_obj {X Y T : C} (f : X ⟶ Y) (g : T ⟶ X) :
    ((representableMap.{w₁, w₂} J f).app T).obj (representableObj J g) =
      representableObj J (g ≫ f) :=
  rfl

/-- `CategoryTheory.StackInGroupoids.representable` is unchanged by restriction along an
inequality between subcanonical topologies: `CategoryTheory.StackInGroupoids.ofLE` changes
only its descent proof. -/
theorem representable_ofLE {J₁ J₂ : GrothendieckTopology C}
    [J₁.Subcanonical] [J₂.Subcanonical] (h : J₁ ≤ J₂) (X : C) :
    (representable.{w₁, w₂} J₂ X).ofLE h = representable.{w₁, w₂} J₁ X :=
  rfl

end StackInGroupoids

end

end CategoryTheory
