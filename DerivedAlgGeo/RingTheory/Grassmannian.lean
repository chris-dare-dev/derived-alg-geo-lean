/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.RingTheory.Grassmannian.Chart

/-!
# Grassmannians

Extensions of Mathlib's `Mathlib/RingTheory/Grassmannian.lean`, at Mathlib's path.

## Main definitions

None: this umbrella re-exports its children.

## Main results

* `Module.Grassmannian.chartFunctor`: the affine charts of `Module.Grassmannian.functor`, which
  are open (`Module.Grassmannian.exists_opens_isInChart_iff`), are affine spaces for `R^n`
  (`Module.Grassmannian.chartCorepresentableBy`) and cover
  (`Module.Grassmannian.exists_isInChart_away`).

## Implementation notes

The children import Mathlib only, and no scheme appears in them.

## References

* [Stacks: Tag 089T](https://stacks.math.columbia.edu/tag/089T)

## Tags

Grassmannian, affine chart
-/
