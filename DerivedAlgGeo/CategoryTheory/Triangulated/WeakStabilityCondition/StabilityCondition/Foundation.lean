/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.PostnikovTower
import DerivedAlgGeo.CategoryTheory.Triangulated.ExtensionClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing
import DerivedAlgGeo.CategoryTheory.GrothendieckGroup.Presentation
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.Functorial
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.PreStabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.IntervalCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.QuasiAbelian
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.PhaseBounds
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.FiltrationOperations
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.BoundaryFactors
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.IntrinsicPhases
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.IntrinsicPhaseBounds
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.CoreConsequences
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.PhaseCutClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.PhaseShift
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.PhaseTruncation
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Slicing
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.ImageFactorisation

/-!
# Repository-owned Bridgeland foundations

Stable owner-authored root data for filtrations and stability conditions.

## Import policy

This file is the complete downstream umbrella and is not an internal prelude. Implementation
modules import the narrow owner of the declarations they use:

* `Foundation.Slicing` for the root slicing and HN-filtration structures, with individual
  `Foundation.Slicing.*` leaves for later consequences;
* `Foundation.PreStabilityCondition`, `Foundation.IntervalCategory`, and
  `Foundation.StabilityCondition` for their respective stable layers;
* individual `Foundation.StabilityFunction.*` leaves for the abelian HN API;
* individual `Foundation.Deformation.*` leaves for deformation-theoretic results.

The `foundation-import-boundary` gate prevents implementation modules from importing this
umbrella and silently acquiring all of those layers.
-/
