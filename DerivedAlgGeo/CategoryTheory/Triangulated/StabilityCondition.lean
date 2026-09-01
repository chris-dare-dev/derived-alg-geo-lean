/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Support
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families

/-!
# Stability conditions

The Bridgeland refinement of weak stability, together with phase analysis,
symmetry actions, metric geometry, support properties, numerical walls, and
abstract family interfaces. Weak stability is the child `Weak/`, which this
umbrella imports; ordinary prestability and stability conditions carry their
weak parent structurally. Declaration namespaces remain
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition`; a
namespace cutover would invalidate the immutable review payloads that
`exe/RestateHistoricalNames.lean` protects.
-/
