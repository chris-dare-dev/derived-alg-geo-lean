/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.RingTheory.LocalRing.LocalSubring

/-!
# Local rings

Extensions of Mathlib's `RingTheory/LocalRing/`, at Mathlib's paths.

## Main definitions

None: this umbrella re-exports its children.

## Main results

* `LocalSubring.exists_le_ringKrullDim_eq_one`: Stacks 00P8.

## Implementation notes

The children import Mathlib only, so the Nagata-ring files can import this root and not the
reverse.

## References

* [Stacks: Tag 00P8](https://stacks.math.columbia.edu/tag/00P8)

## Tags

local ring, local subring
-/
