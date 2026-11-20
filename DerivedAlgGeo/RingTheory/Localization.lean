/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.RingTheory.Localization.Free

/-!
# Localization

Extensions of Mathlib's `RingTheory/Localization/`, at Mathlib's paths.

## Main definitions

None: this umbrella re-exports its children.

## Main results

* `Module.exists_free_localizedModule_away_of_finiteType`: generic freeness, Stacks 051R.
* `Module.exists_notMem_free_localizedModule_away_of_mem_minimalPrimes`: its form at a minimal
  prime of a reduced ring, the pointwise content of Stacks 051Z.

## Implementation notes

The children import Mathlib only.

## References

* [Stacks: Tag 051R](https://stacks.math.columbia.edu/tag/051R)
* [Stacks: Tag 051Z](https://stacks.math.columbia.edu/tag/051Z)

## Tags

localization, generic freeness
-/
