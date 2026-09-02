/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.BoundedCoherentBaseChange
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.BoundedCoherentPushforward
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.DerivedPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.FourierMukaiAction

/-!
# Stability conditions on scheme-derived categories

The scheme-derived category consumers that need Bridgeland stability:
bounded-coherent and derived-pullback base change of pre-stability data, the
pushforward of stability conditions along bounded coherent pullback, and
the action of geometric Fourier--Mukai kernels on stability conditions.

This is the one subtree below `AlgebraicGeometry/DerivedCategory/` that
imports the stability tree. The `DerivedCategory` umbrella deliberately does
not re-export it, so `Dᵇ(Coh X)`, `Dqc`, pullback, and kernels stay importable
without stability conditions; the top-level `AlgebraicGeometry` umbrella
imports it. Declarations keep the namespaces of the objects they extend,
`AlgebraicGeometry.DerivedCategory.Families` and
`AlgebraicGeometry.DerivedCategory.FourierMukai`.
-/
