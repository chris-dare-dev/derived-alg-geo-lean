/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.Cutoff
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.CutoffSlope
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.Extrema
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.HNTransport
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.HarderNarasimhan
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.Slope
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeCutoff
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeGeometry
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeOrder
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeTop
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.SlopeTransport
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.Splitting
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.Tail
import DerivedAlgGeo.CategoryTheory.Abelian.Stability.Weak.Truncation

/-!
# Weak stability functions on an abelian category

The weakened variant of the theory its parent directory owns: the charge is
allowed to land on `0`, so the slope takes values in `WithTop ℝ` and a
zero-charge object is not excluded from the subobject quantifier. Everything
here is a variant of a neighbour one level up, which is why it is a child and
not a sibling -- `MetricSpace/Pseudo/` in Mathlib names the same relationship.

## Main definitions

None; this module re-exports its children. The central ones are
`CategoryTheory.Triangulated.WeakSlopeData` in `Weak/Slope.lean` and
`CategoryTheory.Triangulated.AbelianWeakHNFiltration` in
`Weak/HarderNarasimhan.lean`.

## Main results

None; this module re-exports its children.

## Implementation notes

### Dependency direction

The dependency runs the other way, as it does in Mathlib's `MetricSpace/Pseudo/`.
`Stability/Slope.lean` imports `Weak/Slope.lean` and adds the strict positivity
that rules `⊤` out; `Stability/PhaseMonotone.lean` and the `Uniqueness/` files
are shared by both. Directory nesting names the variant, not the import
direction.

### Why this is not below `Triangulated/`

Nothing in this subtree mentions a shift, a distinguished triangle, a
t-structure or a heart. It needs an abelian category, an additive charge out
of its Grothendieck group, and a half-plane. The triangulated weak theory
consumes it across the `CategoryTheory/Abelian/` boundary like any other
client.

Declaration namespaces remain `CategoryTheory.Triangulated`, which differs from
the path, so that the fully qualified names stay stable for the external
references that use them.

## References

The subtree builds on `CategoryTheory.Triangulated.WeakStabilityFunctionOn`
and `CategoryTheory.Triangulated.abelianDatum` from `Stability/Basic.lean`.

## Tags

weak stability function, slope, abelian category, Harder--Narasimhan filtration,
torsion pair
-/
