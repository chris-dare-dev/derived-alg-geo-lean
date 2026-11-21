/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.RingTheory.Flat.FaithfullyFlat
import DerivedAlgGeo.RingTheory.Flat.FilteredColimit
import DerivedAlgGeo.RingTheory.Flat.LocalCriterion

/-!
# Flat modules

Extensions of Mathlib's `RingTheory/Flat/`, at Mathlib's paths.

## Main definitions

None: this umbrella re-exports its children.

## Main results

* `Module.Flat.tensorProduct_of_flat`: Stacks 0584 (1).
* `Module.Flat.of_flat_tensorProduct_of_faithfullyFlat`: Stacks 0584 (2).
* `Module.Flat.of_injective_maximalIdeal_of_isLocalHom`: Stacks 00MK, the local criterion.
* `Module.Flat.of_injective_of_flat_quotient_of_isLocalHom`: Stacks 00ML, its variant.
* `Module.Flat.exists_fg_subalgebra_flat_of_isNoetherianRing`: Stacks 02JO (1) over a Noetherian
  base, EGA IV₃ 11.2.6.1 and 11.2.7: flatness is reached on a finitely generated subalgebra.
* `Module.Flat.exists_flat_of_isColimit`: EGA IV₃ 11.2.6.1 (ii): flatness descends to a finite stage
  of a filtered colimit of rings.

## Implementation notes

The children import Mathlib only, except `FilteredColimit`, which also imports `LocalCriterion`,
the generic freeness file `Localization/Free` and the Noetherian models of finitely presented
modules.

## References

* [Stacks: Tag 0584](https://stacks.math.columbia.edu/tag/0584)
* [Stacks: Tag 00MK](https://stacks.math.columbia.edu/tag/00MK)
* [Stacks: Tag 00ML](https://stacks.math.columbia.edu/tag/00ML)
* [Stacks: Tag 02JO](https://stacks.math.columbia.edu/tag/02JO)

## Tags

flat, faithfully flat, descent, local criterion, filtered colimit
-/
