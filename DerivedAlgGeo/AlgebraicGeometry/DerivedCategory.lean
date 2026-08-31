/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Basic
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Coherent
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.Affine
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineDerivedEquivalence
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineRealization
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectivePullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectiveCoherence
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectiveUnitality
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectivePseudofunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineKProjectiveDerivedPseudofunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineGeometricPseudofunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineGeometricCorePseudofunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Dqc.AffineFamilyPseudofunctor
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.FourierMukai

/-!
# Derived algebraic geometry

The geometric inputs and realizations of the generic categorical derived
category: module-sheaf and coherent-sheaf derived categories, `Dqc`,
scheme-indexed pullback, and geometric Fourier--Mukai kernels. Foundational
scheme-derived declarations use `AlgebraicGeometry.DerivedCategory`;
scheme-family declarations use `AlgebraicGeometry.DerivedCategory.Families`;
`Dqc` declarations use `AlgebraicGeometry.DerivedCategory.Dqc`; geometric
kernel declarations use `AlgebraicGeometry.DerivedCategory.FourierMukai`.
-/
