/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Sites.Descent.DescentData
import DerivedAlgGeo.CategoryTheory.Sites.Descent.IsStack
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Discrete
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Morphism
import DerivedAlgGeo.CategoryTheory.Sites.Descent.StackInGroupoids.Representable

/-!
# Descent and stacks

Extensions of Mathlib's `CategoryTheory/Sites/Descent/`, where `IsStack` is
defined. `StackInGroupoids.lean` declares the structure and does not re-export
its directory, so this umbrella imports the children directly.

## Main definitions

* `DescentData.lean`: functoriality of descent data along strong
  transformations.
* `StackInGroupoids.lean` and its children: stacks in groupoids, discrete
  stacks from sheaves, stack morphisms, and site-object representability.

## Main results

* `IsStack.lean`: the prestack and stack conditions are invariant under strong
  transformations whose components are equivalences of categories.

## Implementation notes

This module only re-exports its children.

## References

Each child module lists its own references.

## Tags

descent, stack, stack in groupoids
-/
