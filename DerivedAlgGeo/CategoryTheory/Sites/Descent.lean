/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentData
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentDataPrime
import DerivedAlgGeo.CategoryTheory.Sites.Descent.IsStack
import DerivedAlgGeo.CategoryTheory.Sites.Descent.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Discrete
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Morphism
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representable

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
  stacks from sheaves, stack morphisms, site-object representability, and
  the moduli of objects `StackInGroupoids.ofObjectProperty`.

## Main results

* `IsStack.lean`: the prestack and stack conditions are invariant under strong
  transformations whose components are equivalences of categories.
* `DescentDataAsCoalgebra.lean`: effective descent along one morphism is
  comonadicity of its pullback functor, under the base change hypotheses.
* `DescentDataPrime.lean`: effective descent along one morphism is unchanged by
  reindexing along a functor that preserves the pullbacks involved.
* `ObjectProperty.lean`: the core of a stack is a stack, and a local object
  property closed under isomorphisms cuts out a substack.

## Implementation notes

This module only re-exports its children.

## References

Each child module lists its own references.

## Tags

descent, stack, stack in groupoids
-/
