/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.Cohomology.Sequence

/-!
# Owner-native cohomology exactness

This module is the boundary through which mass subadditivity reaches
t-structure cohomology. It re-exports `Weak/Tilting/Cohomology/Sequence.lean`,
which proves homologicality and the shifted cohomology sequences directly for
`originalHeartCohFunctor`; importing that module is the complete public
boundary needed by mass subadditivity.

## Main definitions

This file introduces no declarations. It re-exports
`Tilting.originalHeartCohomologySixTermSequence` and
`Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact`.

## Main results

Re-exported: the instance `Tilting.originalHeartCohFunctor_isHomological`,
under which heart cohomology in every degree sends distinguished triangles to
exact short complexes, and `Tilting.originalHeartCohomologySixTermSequence_exact`.

## Implementation notes

The import is the whole content. Consumers under `Mass/Subadditivity/` import
this module rather than the tilting cohomology tree, so mass subadditivity
reaches t-structure cohomology through one named boundary.

## References

Mathlib's `CategoryTheory.Functor.IsHomological`.

## Tags

t-structure cohomology, homological functor, mass subadditivity
-/
