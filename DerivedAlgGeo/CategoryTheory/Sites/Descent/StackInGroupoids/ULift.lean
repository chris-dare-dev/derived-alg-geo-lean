/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids
import DerivedAlgGeo.CategoryTheory.Sites.Descent.ULift

/-!
# Universe lifts of stacks in groupoids

A stack in groupoids with fibres in `Cat.{v', u'}` lifts to a stack in groupoids with fibres
in `Cat.{max v' w₁, max u' w₂}`, for any `w₁` and `w₂`. The object and morphism universes are
raised independently.

## Main definitions

* `CategoryTheory.StackInGroupoids.ulift`: the universe lift of a stack in groupoids, with
  underlying pseudofunctor `Pseudofunctor.ulift`.

## Main results

* `CategoryTheory.StackInGroupoids.ulift_presheaf`: the underlying pseudofunctor of the lift
  is the universe lift of the underlying pseudofunctor.

## Implementation notes

The lift is a new inhabitant of the existing carrier `CategoryTheory.StackInGroupoids`. Its
fibres are groupoids by `Pseudofunctor.ulift.isGroupoid_obj`, and its stack condition is
`Pseudofunctor.isStack_ulift_iff`; neither is assumed.

## References

* [Stacks Project, Tag 042X](https://stacks.math.columbia.edu/tag/042X): equivalences of
  categories fibred in groupoids preserve the stack condition.

## Tags

stack in groupoids, universe lift
-/

universe w₁ w₂ v' u' v u

namespace CategoryTheory.StackInGroupoids

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The universe lift of a stack in groupoids: its fibres are those of `X` lifted from
`Cat.{v', u'}` to `Cat.{max v' w₁, max u' w₂}` by `Pseudofunctor.ulift`. -/
def ulift (X : StackInGroupoids.{v', v, u', u} C J) :
    StackInGroupoids.{max v' w₁, v, max u' w₂, u} C J where
  presheaf := X.presheaf.ulift.{w₁, w₂}
  fiberIsGroupoid _ := inferInstance
  isStack := (Pseudofunctor.isStack_ulift_iff X.presheaf J).2 X.isStack

@[simp]
lemma ulift_presheaf (X : StackInGroupoids.{v', v, u', u} C J) :
    (X.ulift.{w₁, w₂}).presheaf = X.presheaf.ulift.{w₁, w₂} :=
  rfl

end CategoryTheory.StackInGroupoids
