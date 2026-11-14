/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.Basic

/-!
# Gieseker stability of coherent sheaves

The Gieseker order on coherent sheaves — the reduced Hilbert function compared for large `n` —
the lexicographic criterion that decides it, and the two stability predicates built from it.

## Main definitions

None: this umbrella re-exports `Gieseker/Basic.lean`, which defines
`PolarizedVarietyData.GiesekerLE`, `PolarizedVarietyData.IsGiesekerSemistable` and
`PolarizedVarietyData.IsGiesekerStable`.

## Main results

None; this module re-exports its child, whose lexicographic criterion is
`PolarizedVarietyData.giesekerLE_iff_coeffLexLE`.

## Implementation notes

The shared Hilbert-polynomial data this rests on is one directory up:
`HilbertPolynomial.lean` owns `PolarizedVarietyData` and the Hilbert function,
`Coefficients.lean` owns the Newton coefficients, and `Purity.lean` owns `IsPure`, which
μ-slope stability needs for reasons of its own. Harder–Narasimhan filtrations are not here: the
repository's HN theorem on `Coh X` is for the μ-slope, and lives with it in `Slope/`.

## References

The definitions are in `Gieseker/Basic.lean`, built on `PolarizedVarietyData` from
`HilbertPolynomial.lean`.

## Tags

Gieseker stability, reduced Hilbert polynomial, coherent sheaf
-/
