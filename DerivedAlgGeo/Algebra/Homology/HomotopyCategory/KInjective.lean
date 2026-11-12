/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.KInjective.Criterion
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.KInjective.Factorization

/-!
# K-injective complexes in Grothendieck abelian categories

Extensions of Mathlib's `CochainComplex.IsKInjective` toward the existence of
K-injective resolutions of unbounded complexes in a Grothendieck abelian category
(Stacks, Section 19.12).

## Main definitions

None: this umbrella re-exports its children.

## Main results

None; this module re-exports its children, among them
`CochainComplex.isKInjective_of_injective_of_homotopy_zero`, the criterion of
Stacks, Tag 079L, and `CochainComplex.injectiveReplacement`, the functorial replacement
of Stacks, Tags 079M and 079N.

## Implementation notes

The construction of K-injective resolutions spans several files below
`KInjective/`, one for each step of the proof in Stacks, Section 19.12. Nothing
here imports the dg enhancement of the homotopy category.

## References

* [The Stacks project, Section 19.12](https://stacks.math.columbia.edu/tag/079I)

## Tags

K-injective complex, Grothendieck abelian category
-/
