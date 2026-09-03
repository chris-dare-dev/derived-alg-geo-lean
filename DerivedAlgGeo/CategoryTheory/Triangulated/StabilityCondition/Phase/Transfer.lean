/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Phase
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Equivariance
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.InducedTStructures
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.HN
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.IndExtensions
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Inducing
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.PreStability
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.LocallyFinite
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Bayer
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Metric
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Adjoint

/-!
# Transfer of slicings and stability conditions along functors

Raw phase preimages, the explicit slicing-lifting criterion, phase and order
transport, equivariance, phase-indexed induced t-structures, their finite
phase-truncation HN theorem, the named Polishchuk/Ind theorem boundary, the
transfer of pre-stability and stability conditions themselves, the
behaviour of the Bayer property, the mass, and the stability metric under
that transfer, and the adjoint transposition that turns the paper's
pushforward criterion into the inducing hypothesis.
-/
