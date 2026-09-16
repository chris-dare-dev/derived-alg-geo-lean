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

The dependency runs the other way, as it does there. `Stability/Slope.lean`
imports `Weak/Slope.lean` and adds the strict positivity that rules `⊤` out;
`Stability/PhaseMonotone.lean` and the `Uniqueness/` files are shared by both.
Directory nesting names the variant, not the import direction.

## Why this is not below `Triangulated/`

Nothing in this subtree mentions a shift, a distinguished triangle, a
t-structure or a heart. It asks for an abelian category, an additive charge out
of its Grothendieck group, and a half-plane. Until MO1.08 (#1319) it lived
below `Triangulated/StabilityCondition/Weak/Foundation/`, where the subject it
is a foundation *for* owned it; the triangulated weak theory now consumes it
across the `CategoryTheory/Abelian/` boundary like any other client.

Declaration namespaces are unchanged and remain `CategoryTheory.Triangulated`;
see decision 1 of the MO1 owner map in `docs/architecture/cutover-ledger.md`.
-/
