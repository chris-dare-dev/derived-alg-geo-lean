/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.BoundaryFactors
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.BoundaryTruncation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.CoreConsequences
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.CutoffTruncation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.FiltrationOperations
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.HeadTail
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhaseBounds
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhases
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseBounds
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseCutClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseShift
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseTruncation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.IntervalCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.HeartDatum
import DerivedAlgGeo.CategoryTheory.Abelian.Stability

/-!
# Foundations shared by weak and Bridgeland stability

Slicings and their generic consequences, interval categories, and the heart
class datum, all needed before imposing the stronger open-ray and
local-finiteness conditions.

The stability functions themselves are not owned here. They are abelian, and
MO1.08 (#1319) moved them to `CategoryTheory/Abelian/Stability/`; this umbrella
re-exports that owner so the triangulated weak theory keeps one import surface.
`HeartDatum.lean` is the adapter that instantiates the abelian `ClassDatum` at
the heart of a t-structure, and is the only part of the old
`Foundation/StabilityFunction/` directory that mentions a triangulated
category at all.
-/
