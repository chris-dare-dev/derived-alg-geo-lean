/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.Enriques
import DerivedAlgGeo.AlgebraicGeometry.Surface.K3
import DerivedAlgGeo.AlgebraicGeometry.Surface.Spherical
import DerivedAlgGeo.AlgebraicGeometry.Surface.SphericalCategorical
import DerivedAlgGeo.AlgebraicGeometry.Surface.SphericalMukai

/-!
# Surfaces

Geometric surface theory: varieties of pure dimension two, distinguished by
conditions on their canonical sheaf and cohomology.

## Main definitions

None: this umbrella re-exports its children `Surface/Enriques`, `Surface/K3`,
`Surface/Spherical`, `Surface/SphericalCategorical` and `Surface/SphericalMukai`.

## Main results

None; this module re-exports its children.

## Implementation notes

This is the *geometric* surface theory. `IntersectionTheory/Surface/` and
`RiemannRoch/Surface/` are numerical, and `Numerical/Examples/Surface/`
exhibits models of the numerical axioms; none of them mentions a scheme.

## References

The children build on the repository's `IsSmoothProperVariety` and Serre-duality interfaces.

## Tags

surface, K3 surface, Enriques surface, spherical object
-/
