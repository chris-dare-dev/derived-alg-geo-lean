/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.Core

/-!
# Object properties of the core of a pseudofunctor

An object property `P` of a pseudofunctor `F : LocallyDiscrete B₀ ⥤ᵖ Cat` restricts to the
core `F.core`: an object of `Core (F.obj X)` satisfies `P.core` when its underlying object
satisfies `P`. Closure under mapped objects and under isomorphisms pass to `P.core`, so
`P.core.fullsubcategory` is the full sub-pseudofunctor of `F.core` cut out by `P`.

## Main definitions

* `CategoryTheory.Pseudofunctor.ObjectProperty.core P : F.core.ObjectProperty`.

## Main results

* `Pseudofunctor.ObjectProperty.core_isClosedUnderMapObj` and
  `Pseudofunctor.ObjectProperty.core_isClosedUnderIsomorphisms`: `P.core` is preserved by the
  transition functors, or closed under isomorphisms, when `P` is.

## Implementation notes

The objects of `F.core.obj X` are those of `F.obj X`, wrapped in `Core.mk`, so `P.core` holds
of `M` exactly when `P` holds of `M.of` (`core_prop`), definitionally.

## References

* [Stacks, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU): full subcategories of fibred
  categories cut out by a property of objects.

## Tags

object property, core, pseudofunctor
-/

universe v u v' u'

namespace CategoryTheory.Pseudofunctor.ObjectProperty

open Bicategory

variable {B₀ : Type u} [Category.{v} B₀] {F : LocallyDiscrete B₀ ⥤ᵖ Cat.{v', u'}}
  (P : F.ObjectProperty)

/-- The restriction of `P` to the core of `F`: an object of `Core (F.obj X)` satisfies
`P.core` when its underlying object of `F.obj X` satisfies `P`. -/
def core : F.core.ObjectProperty where
  prop X M := P.prop X (M : Core (F.obj X)).of

@[simp]
lemma core_prop (X : LocallyDiscrete B₀) (M : Core (F.obj X)) :
    P.core.prop X M ↔ P.prop X M.of :=
  Iff.rfl

instance core_isClosedUnderMapObj [P.IsClosedUnderMapObj] : P.core.IsClosedUnderMapObj where
  map_obj hM f := P.map_obj hM f

instance core_isClosedUnderIsomorphisms [P.IsClosedUnderIsomorphisms] :
    P.core.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms X :=
    { of_iso := fun e hM => (P.prop X).prop_of_iso ((Core.inclusion (F.obj X)).mapIso e) hM }

end CategoryTheory.Pseudofunctor.ObjectProperty
