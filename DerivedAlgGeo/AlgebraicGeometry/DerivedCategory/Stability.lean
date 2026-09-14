/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.BoundedCoherentBaseChange
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.BoundedCoherentPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.BoundedCoherentPushforward
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.DerivedPullback
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.FourierMukaiAction
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.K3MukaiTilt
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.K3MukaiTiltScheme
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.MassHom
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.MassHomTheorem75

/-!
# Stability conditions on scheme-derived categories

The scheme-derived category consumers that need Bridgeland stability:
bounded-coherent and derived-pullback base change of pre-stability data, the
pushforward of stability conditions along bounded coherent pullback, their
pullback along bounded coherent direct image, and the action of geometric
Fourier--Mukai kernels on stability conditions. It also identifies perfect
objects as the geometric test class for mass--Hom bounds.

This is the one subtree below `AlgebraicGeometry/DerivedCategory/` that
imports the stability tree. The `DerivedCategory` umbrella deliberately does
not re-export it, so `Dᵇ(Coh X)`, `Dqc`, pullback, and kernels stay importable
without stability conditions; the top-level `AlgebraicGeometry` umbrella
imports it. Declarations keep the namespaces of the objects they extend,
`AlgebraicGeometry.DerivedCategory.Families` and
`AlgebraicGeometry.DerivedCategory.FourierMukai`.
-/
