/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Perfect.BaseChange
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Perfect.Relative

/-!
# Perfectness predicates on scheme-derived objects

Pseudo-coherence, local finite Tor amplitude over a base, relative perfection
and the universally-gluable refinement: properties of one complex over one
morphism, stated before any moduli problem consumes them.

## Main definitions

None; this module re-exports its children. `Perfect/Relative.lean` defines
`AlgebraicGeometry.schemePseudoCoherent`,
`AlgebraicGeometry.schemeLocallyFiniteTorAmplitudeOver`,
`AlgebraicGeometry.schemeRelativePerfect` and
`AlgebraicGeometry.schemeUniversallyGluableRelativePerfect`.

## Main results

None; this module re-exports its children. `Perfect/BaseChange.lean` proves that relative
perfection is stable under derived base change of a flat family,
`AlgebraicGeometry.schemeRelativePerfect_baseChange`.

## Implementation notes

Absolute perfection, `schemePerfect` and `schemePerfectInDqc`, belongs to
`Coherent.lean` and `Dqc.lean`; the one-way comparisons among the repository's
three uses of "perfect" stay in `Moduli/PerfectComplex/Comparison.lean`.

## References

The repository's `SchemeQuasicoherentDerivedCategory`, on which these predicates
are defined.

## Tags

perfect complex, pseudo-coherence, Tor amplitude, relative perfection
-/
