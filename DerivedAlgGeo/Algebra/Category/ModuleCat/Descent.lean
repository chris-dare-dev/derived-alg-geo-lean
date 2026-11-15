/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Descent.BaseChange
import DerivedAlgGeo.Algebra.Category.ModuleCat.Descent.FaithfullyFlat

/-!
# Descent for modules

Descent for the module pseudofunctor `CommRingCat.moduleCatAdjPseudofunctor` on the site
`CommRingCatᵒᵖ`, at Mathlib's path `Algebra/Category/ModuleCat/Descent`.

## Main definitions

* `FaithfullyFlat.lean`: the equivalence between modules over `A` and modules over `B` with
  descent data along a faithfully flat map `A ⟶ B`.

## Main results

* `BaseChange.lean`: the base change morphism of the module pseudofunctor at every pushout
  square of commutative rings is an isomorphism.
* `FaithfullyFlat.lean`: the module pseudofunctor is a stack for the singleton presieve of a
  faithfully flat ring map (Stacks Project, Tag 023N).

## Implementation notes

This module only re-exports its children.

## References

Each child module lists its own references.

## Tags

descent, faithfully flat, module
-/
