/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty.Monotone
import DerivedAlgGeo.CategoryTheory.Sites.Descent.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Morphism

/-!
# Moduli of objects

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a stack for `J` and `P` a local object property of `F`
closed under isomorphisms. The stack in groupoids of objects of `F` satisfying `P`, and their
isomorphisms, is `StackInGroupoids.ofObjectProperty F P`. It is the single moduli-of-objects
constructor: a moduli stack of objects with a property is this construction applied to that
property, not a new carrier.

## Main definitions

* `CategoryTheory.StackInGroupoids.ofStack F`: the core `F.core` of a stack, the moduli of all
  objects of `F`.
* `CategoryTheory.StackInGroupoids.ofObjectProperty F P`: the full sub-pseudofunctor of `F.core`
  cut out by `P`, the moduli of objects of `F` satisfying `P`.
* `CategoryTheory.StackInGroupoids.ofObjectPropertyι F P`: its inclusion into `ofStack F`.
* `CategoryTheory.StackInGroupoids.ofObjectPropertyMap F h`: the inclusion induced by `Q ≤ P`.
  It is compatible with the inclusions into `ofStack F` by
  `Pseudofunctor.ObjectProperty.ιOfLECompι`.

## Main results

None beyond the constructions: the stack conditions are `Pseudofunctor.isStack_core` and
`Pseudofunctor.ObjectProperty.isStack_fullsubcategory`.

## Implementation notes

`ofObjectProperty F P` is `P.core.fullsubcategory`, a full sub-pseudofunctor of `F.core`, rather
than the core of `P.fullsubcategory`. Its inclusion into `ofStack F` is then Mathlib's
`Pseudofunctor.ObjectProperty.ι`, and no functoriality of cores along strong transformations
is needed.

The stack condition of the result is a theorem, `Pseudofunctor.isStack_core` and
`Pseudofunctor.ObjectProperty.isStack_fullsubcategory`, not a hypothesis.

## References

* [Stacks, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU), Lemma 8.4.3.
* [Stacks, Tag 03YI](https://stacks.math.columbia.edu/tag/03YI), Lemma 8.5.3.

## Tags

moduli of objects, stack in groupoids, substack
-/

universe v w u

namespace CategoryTheory.StackInGroupoids

open Bicategory Pseudofunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The stack in groupoids of objects of a stack `F` and their isomorphisms: the core `F.core`
([Stacks, Tag 03YI](https://stacks.math.columbia.edu/tag/03YI)). -/
@[simps presheaf]
def ofStack (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, w}) [F.IsStack J] : StackInGroupoids C J where
  presheaf := F.core
  fiberIsGroupoid _ := inferInstance
  isStack := isStack_core

/-- The moduli of objects of a stack `F` satisfying `P`: the stack in groupoids of objects of
`F` satisfying `P` and their isomorphisms, the full sub-pseudofunctor `P.core.fullsubcategory`
of `F.core`. This is the moduli-of-objects constructor; a moduli stack of objects with a
property is this construction applied to that property.

It is a stack by `Pseudofunctor.isStack_core` and
`Pseudofunctor.ObjectProperty.isStack_fullsubcategory`; the stack condition is proved from
`F.IsStack J` and locality, never taken as a field or hypothesis. This constructor does not
claim:
* that any particular property is local, which is the consumer's obligation;
* that any locus is open;
* any descent theorem for a particular `F`, such as descent of quasi-coherent sheaves or the
  fpqc-locality of flatness and finite presentation;
* the stack property of any particular moduli problem, such as one of semistable objects;
* anything for pseudofunctors that are only prestacks, such as derived categories, to which
  it does not apply. -/
@[simps presheaf]
def ofObjectProperty (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, w}) [F.IsStack J]
    (P : F.ObjectProperty) [P.IsLocal J] [P.IsClosedUnderIsomorphisms] :
    StackInGroupoids C J where
  presheaf := P.core.fullsubcategory
  fiberIsGroupoid X :=
    show IsGroupoid (P.core.prop X).FullSubcategory from
      isGroupoid_of_reflects_iso (P.core.prop X).ι
  isStack :=
    have : F.core.IsStack J := isStack_core
    P.core.isStack_fullsubcategory

/-- The inclusion of the moduli of objects satisfying `P` into the moduli of all objects. -/
def ofObjectPropertyι (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, w}) [F.IsStack J]
    (P : F.ObjectProperty) [P.IsLocal J] [P.IsClosedUnderIsomorphisms] :
    StackMorphism (ofObjectProperty (J := J) F P) (ofStack F) :=
  P.core.ι

/-- If `Q` implies `P`, the moduli of objects satisfying `Q` includes into the moduli of
objects satisfying `P`. -/
def ofObjectPropertyMap (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, w}) [F.IsStack J]
    {P Q : F.ObjectProperty} [P.IsLocal J] [P.IsClosedUnderIsomorphisms] [Q.IsLocal J]
    [Q.IsClosedUnderIsomorphisms] (h : ∀ X, Q.prop X ≤ P.prop X) :
    StackMorphism (ofObjectProperty (J := J) F Q) (ofObjectProperty F P) :=
  Pseudofunctor.ObjectProperty.ιOfLE (P := P.core) (Q := Q.core) fun X M hM => h X M.of hM

end CategoryTheory.StackInGroupoids
