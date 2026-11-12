/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Families
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.HarderNarasimhan
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Mass
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Support
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting

/-!
# Weak stability conditions

The dependency parent for Bridgeland stability: weak central charges,
Harder--Narasimhan theory, support, and tilting.

## Main definitions

None in this module. Its child `Weak/Basic/Definitions.lean` defines
`CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition`
and the heart-level `WeakStabilityFunction` and `StabilityFunction`.

## Main results

None; this module re-exports its children `Weak/Foundation.lean`,
`Weak/Basic.lean`, `Weak/Families.lean`, `Weak/Heart.lean`,
`Weak/HarderNarasimhan.lean`, `Weak/Mass.lean`, `Weak/Support.lean` and
`Weak/Tilting.lean`.

## Implementation notes

### Directory and namespace

This is the child `Weak/` of `StabilityCondition/`, the way `PseudoMetricSpace`
is `MetricSpace/Pseudo/` in Mathlib: the directory is named for the canonical
concept and the weakened variant by its adjective, while the dependency runs the
other way. Nothing below `Weak/` imports the Bridgeland theory, and this
umbrella is importable without it. Declaration namespaces remain
`CategoryTheory.Triangulated.WeakStabilityCondition`.

### The abelian half lives elsewhere

Stability functions on an abelian category, their Harder--Narasimhan
filtrations, and the `ClassDatum` the charge condition is stated over are owned
by `CategoryTheory/Abelian/Stability/`; `Weak/Foundation.lean` consumes that
owner and re-exports it, so this umbrella offers the same names. What lives
below `Weak/` is the triangulated theory: slicings, the heart adapter, support,
tilting and the families.

## References

This module cites no literature. It builds on Mathlib's
`CategoryTheory.Triangulated.TStructure` and the abelian stability functions of
`CategoryTheory/Abelian/Stability/`.

## Tags

weak stability condition, stability function, slicing, Harder--Narasimhan
filtration, tilting
-/
