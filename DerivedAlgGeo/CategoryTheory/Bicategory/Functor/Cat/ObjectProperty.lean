/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty.Core
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty.Monotone
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty.UniversallyStable

/-!
# Object properties and subprestacks of pseudofunctors

Extensions of Mathlib's `Pseudofunctor.ObjectProperty`, the canonical carrier for a
fiberwise locus. Closure under isomorphisms makes the locus replete; closure
under mapped objects makes it a subprestack, represented by
`Pseudofunctor.ObjectProperty.fullsubcategory` and its inclusion `ι`.

## Main definitions

This umbrella introduces no definitions. It exports:

* `ObjectProperty/UniversallyStable.lean`: the universally stable closure
  `Pseudofunctor.ObjectProperty.universallyStable`;
* `ObjectProperty/Core.lean`: the restriction `Pseudofunctor.ObjectProperty.core`
  of a locus to the core of a pseudofunctor;
* `ObjectProperty/Monotone.lean`: the inclusion
  `Pseudofunctor.ObjectProperty.ιOfLE` of the subprestack of a smaller locus
  into that of a larger one.

## Main results

The children prove the closure instances of their constructions.

## Implementation notes

This module only re-exports its children; none introduces a new carrier.

## References

Each child module lists its own references.

## Tags

object property, subprestack, pseudofunctor
-/
