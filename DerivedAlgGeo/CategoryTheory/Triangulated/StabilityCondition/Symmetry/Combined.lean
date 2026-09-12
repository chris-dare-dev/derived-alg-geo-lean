/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.Action
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.Components
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.Effective
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.LatticeAut
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.OrbitSpace
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.PeriodMap
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.ProperDiscontinuity
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Combined.Topology

/-!
# Combined symmetries

Commuting lifted-linear and autoequivalence actions, including their topology,
component transport, orbit spaces, period-map equivariance, and effective quotient.
Proper discontinuity remains explicit external data, with only its valid
point-stabilizer, quotient-separation, and free-locus covering consequences.
-/
