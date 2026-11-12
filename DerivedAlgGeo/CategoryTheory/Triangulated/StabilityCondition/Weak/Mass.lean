/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Mass.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Mass.Uniqueness

/-!
# Mass theory available at weak stability

The weak-stability half of the mass API, sibling to the Bridgeland-level
`StabilityCondition/Mass/`.

## Main definitions

None in this module. Its children define the class mass
`CategoryTheory.Triangulated.Slicing.classMass` of a bare slicing and charge
(`Weak/Mass/Uniqueness.lean`) and the mass
`CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.stabilityMass`
of a weak prestability condition (`Weak/Mass/Basic.lean`).

## Main results

None; this module re-exports its children `Weak/Mass/Basic.lean` and
`Weak/Mass/Uniqueness.lean`.

## Implementation notes

The mass theory here needs no compatibility ray, so it is stated at weak
stability and the Bridgeland-level `StabilityCondition/Mass/` specializes it.

## References

This module cites no literature. It builds on
`CategoryTheory.Triangulated.HNFiltration` and
`CategoryTheory.Triangulated.Slicing`.

## Tags

weak stability condition, Harder--Narasimhan filtration, mass
-/
