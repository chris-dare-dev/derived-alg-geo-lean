/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Modification.Pseudo

/-!
# Inclusions of full sub-pseudofunctors

If `Q` and `P` are object properties of a pseudofunctor `F : B ⥤ᵖ Cat` that are preserved by
the transition functors, and `Q` implies `P` in every fibre, then the full sub-pseudofunctor
cut out by `Q` includes into the one cut out by `P`.

## Main definitions

* `CategoryTheory.Pseudofunctor.ObjectProperty.ιOfLE h : Q.fullsubcategory ⟶ P.fullsubcategory`:
  `CategoryTheory.ObjectProperty.ιOfLE` in each fibre, with identity naturality isomorphisms.
* `CategoryTheory.Pseudofunctor.ObjectProperty.ιOfLECompι h : ιOfLE h ≫ P.ι ≅ Q.ι`: the
  inclusion is compatible with the inclusions into `F`.

## Main results

None beyond the compatibility isomorphism `ιOfLECompι`, whose components are identities.

## Implementation notes

The base is an arbitrary bicategory, as for Mathlib's `Pseudofunctor.ObjectProperty.ι`. The
naturality isomorphisms of `ιOfLE h`, and the components of `ιOfLECompι h`, are identities,
because both full sub-pseudofunctors have the transition functors of `F` on objects and
morphisms.

## References

* [Stacks, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU): full subcategories of fibred
  categories cut out by a property of objects.

## Tags

object property, full subcategory, pseudofunctor
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe w v v' u u'

namespace CategoryTheory.Pseudofunctor.ObjectProperty

open Bicategory
open scoped StrongTrans

variable {B : Type u} [Bicategory.{w, v} B] {F : B ⥤ᵖ Cat.{v', u'}}
  {P Q : F.ObjectProperty} [P.IsClosedUnderMapObj] [Q.IsClosedUnderMapObj]

/-- If `Q` implies `P` in every fibre, the full sub-pseudofunctor cut out by `Q` includes into
the one cut out by `P`, by `CategoryTheory.ObjectProperty.ιOfLE` in each fibre. -/
@[simps]
def ιOfLE (h : ∀ X, Q.prop X ≤ P.prop X) : Q.fullsubcategory ⟶ P.fullsubcategory where
  app X := Cat.Hom.ofFunctor (CategoryTheory.ObjectProperty.ιOfLE (h X))
  naturality f := Iso.refl _

/-- The inclusion `ιOfLE h` followed by the inclusion of `P.fullsubcategory` into `F` is the
inclusion of `Q.fullsubcategory` into `F`. -/
@[simps!]
def ιOfLECompι (h : ∀ X, Q.prop X ≤ P.prop X) : ιOfLE h ≫ P.ι ≅ Q.ι :=
  StrongTrans.isoMk (fun X => Iso.refl _)

end CategoryTheory.Pseudofunctor.ObjectProperty
