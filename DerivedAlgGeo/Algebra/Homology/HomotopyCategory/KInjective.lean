/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.KInjective.AcyclicSubcomplex
import DerivedAlgGeo.Algebra.Homology.HomotopyCategory.KInjective.Criterion

/-!
# K-injective complexes in Grothendieck abelian categories

Extensions of Mathlib's `CochainComplex.IsKInjective` toward the existence of
K-injective resolutions of unbounded complexes in a Grothendieck abelian category
(Stacks, Section 19.12).

## Main definitions

None: this umbrella re-exports its children.

## Main results

None; this module re-exports its children, among them
`CochainComplex.exists_mono_smallAcyclic`, the small family of acyclic complexes of
Stacks, Tag 079K, and `CochainComplex.isKInjective_of_injective_of_homotopy_zero`, the
criterion of Stacks, Tag 079L.

## Implementation notes

The construction of K-injective resolutions spans several files below
`KInjective/`, one for each step of the proof in Stacks, Section 19.12. Nothing
here imports the dg enhancement of the homotopy category.

## References

* [The Stacks project, Section 19.12](https://stacks.math.columbia.edu/tag/079I)

## Tags

K-injective complex, Grothendieck abelian category
-/
