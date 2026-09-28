/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Embedding.Extend
import DerivedAlgGeo.Algebra.Homology.Embedding.CochainComplex
import DerivedAlgGeo.Algebra.Homology.Embedding.StupidTruncGE

/-!
# Embedding and truncation extensions

Natural comparisons for Mathlib's homological-complex embedding API, and
canonical towers of good cochain truncations and inclusions between
degree-at-least stupid truncations.

## Main definitions

`CochainComplex.truncLETower` and `CochainComplex.truncLETowerCocone` assemble
the canonical good-truncation diagram and inclusion cocone.

## Main results

`CochainComplex.isColimitTruncLETowerCocone` proves its colimit property.

## Implementation notes

This umbrella re-exports the direct Mathlib embedding extensions. The good
cochain tower is independent of the stupid-truncation comparisons in its
sibling leaf.

## References

Mathlib's `CochainComplex.truncLE` and `CochainComplex.ιTruncLE` supply the
underlying good truncations and inclusions.
-/
