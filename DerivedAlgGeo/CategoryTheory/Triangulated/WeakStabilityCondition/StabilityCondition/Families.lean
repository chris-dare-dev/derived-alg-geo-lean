/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Families
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Families
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.Ordinary
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.PreStabilityBaseChange
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.FiberwiseSupport
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.FiberwiseOrdinary
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families.CategoricalOrdinary

/-!
# Abstract interfaces for stability conditions in families

This umbrella is deliberately geometry-independent. Scheme-indexed
derived categories, derived pullback, `Dqc`, and Fourier--Mukai kernels are
owned by `DerivedAlgGeo.AlgebraicGeometry.DerivedCategory`; actual semistable
loci and relative HN filtrations are owned by `AlgebraicGeometry.Moduli`.
Their realizations of the interfaces exported here live with those geometric
objects, under `AlgebraicGeometry/Moduli/` and
`AlgebraicGeometry/DerivedCategory/Stability/`.

The declarations use the matching
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Families`
namespace.
-/
