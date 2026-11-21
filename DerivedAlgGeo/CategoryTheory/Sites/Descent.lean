/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentData
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentDataPrime
import DerivedAlgGeo.CategoryTheory.Sites.Descent.FiberProduct
import DerivedAlgGeo.CategoryTheory.Sites.Descent.IsStack
import DerivedAlgGeo.CategoryTheory.Sites.Descent.Local
import DerivedAlgGeo.CategoryTheory.Sites.Descent.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Sites.Descent.Over
import DerivedAlgGeo.CategoryTheory.Sites.Descent.SheafOver
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Discrete
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Fibered
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.FiberProduct
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Morphism
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Over
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representable
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representability
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.ULift
import DerivedAlgGeo.CategoryTheory.Sites.Descent.ULift

/-!
# Descent and stacks

Extensions of Mathlib's `CategoryTheory/Sites/Descent/`, where `IsStack` is
defined. `StackInGroupoids.lean` declares the structure and does not re-export
its directory, so this umbrella imports the children directly.

## Main definitions

* `DescentData.lean`: functoriality of descent data along strong
  transformations.
* `DescentDataAsCoalgebra.lean`: the base change morphism of a chosen pullback,
  and descent data along one morphism as coalgebras for the comonad of
  `f^* ⊣ f_*` when two base change morphisms are isomorphisms.
* `ObjectProperty.lean`: local object properties and the equivalence between
  descent data of the core and the core of descent data.
* `StackInGroupoids.lean` and its children: stacks in groupoids, discrete
  stacks from sheaves, stack morphisms, site-object representability, the
  moduli of objects `StackInGroupoids.ofObjectProperty`, universe lifts of
  stacks, 2-fibre products, diagonals and Isom sheaves of stacks in
  groupoids, the 2-Yoneda equivalence `StackInGroupoids.yonedaEquivalence`,
  representable morphisms of stacks, natural in the test object
  (`StackMorphism.IsRepresentable`), and the total stack `StackInGroupoids.overTotal` of a stack
  on a slice site.
* `ULift.lean`: descent data of the universe lift `Pseudofunctor.ulift` are
  equivalent to those of the original pseudofunctor.

## Main results

* `IsStack.lean`: the prestack and stack conditions are invariant under strong
  transformations whose components are equivalences of categories.
* `DescentDataAsCoalgebra.lean`: effective descent along one morphism is
  comonadicity of its pullback functor, under the base change hypotheses.
* `DescentDataPrime.lean`: effective descent along a family of morphisms is unchanged by
  reindexing along a functor that preserves the pullbacks involved.
* `FiberProduct.lean`: the 2-fibre product of two stacks over a prestack is a
  stack, and the terminal pseudofunctor is a stack.
* `Local.lean`: effective descent along a covering sieve can be checked on the
  members of a covering family of a second topology for which the pseudofunctor is a
  stack.
* `ObjectProperty.lean`: the core of a stack is a stack, and a local object
  property closed under isomorphisms cuts out a substack.
* `Over.lean`: the pullback of a stack along a continuous functor is a stack, so a stack on
  `C` pulls back to a stack on `Over S` along `Over.forget S` and along `X ×_S -`; and when
  `yoneda.obj S` is a sheaf, a pseudofunctor on `Over S` is a stack for the slice topology if and
  only if its total pseudofunctor on `C` is a stack.
* `SheafOver.lean`: sheaves on the slices of a site form a prestack for every coefficient
  category, and sheaves of types form a stack when covering sieves contain small covering
  families.
* `ULift.lean`: a pseudofunctor is a prestack (a stack) exactly when its universe lift is.
* `StackInGroupoids/Fibered.lean`: the Grothendieck construction of a stack in
  groupoids is a category fibred in groupoids (`StackInGroupoids.isStronglyCartesian`).

## Implementation notes

This module only re-exports its children.

## References

Each child module lists its own references.

## Tags

descent, stack, stack in groupoids
-/
