/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentData
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentDataPrime
import DerivedAlgGeo.CategoryTheory.Sites.Descent.IsStack
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Discrete
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Morphism
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representable
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
* `StackInGroupoids.lean` and its children: stacks in groupoids, discrete
  stacks from sheaves, stack morphisms, site-object representability, and
  universe lifts of stacks.
* `ULift.lean`: descent data of the universe lift `Pseudofunctor.ulift` are
  equivalent to those of the original pseudofunctor.

## Main results

* `IsStack.lean`: the prestack and stack conditions are invariant under strong
  transformations whose components are equivalences of categories.
* `DescentDataAsCoalgebra.lean`: effective descent along one morphism is
  comonadicity of its pullback functor, under the base change hypotheses.
* `DescentDataPrime.lean`: effective descent along one morphism is unchanged by
  reindexing along a functor that preserves the pullbacks involved.
* `ULift.lean`: a pseudofunctor is a prestack (a stack) exactly when its universe lift is.

## Implementation notes

This module only re-exports its children.

## References

Each child module lists its own references.

## Tags

descent, stack, stack in groupoids
-/
