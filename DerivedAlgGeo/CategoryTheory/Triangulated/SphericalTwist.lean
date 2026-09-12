/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Mukai
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.StabilityAction
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Braid
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctorH0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctorK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.ObjectTwistK0

/-! # The spherical twist

The Seidel--Thomas twist `T_E`, approached from `K₀` upwards. This umbrella
currently re-exports the `K₀`-level twist — `τ_E(x) = x - χ(E, x) • [E]`, its
involutivity, and its preservation of the Euler form — together with its
identification, along a supplied Mukai realization, with the lattice reflection
`ρ_{v[E]}` of `LinearAlgebra/Lattice/Mukai/Reflection.lean`, and the braid
relation `τ_A τ_B τ_A = τ_B τ_A τ_B` for an `A₂`-configuration.

The dg-level construction now includes functorial cones of closed homogeneous
natural transformations, counit-cone twist candidates for dg adjunctions, and
the four enhanced cone choices attached to a functor with left and right dg
adjoints.  Their distinguished triangles compute the four conventional
functors' `K₀` actions as the identity minus the corresponding adjunction
composite.  The object-twist triangle similarly acts as identity minus its
evaluation functor, and the explicit `IsEulerCopower` realization capability
identifies its object classes with the existing numerical `twistK₀` formula;
together with chosen-cone preservation it identifies the induced maps.  It
deliberately stops short of asserting sphericality: the
adjoint-comparison maps and the Morita/higher-cone theorem of
Anno--Logvinenko are not yet repository primitives.  The object-specific
evaluation functor `RHom(E,-) ⊗ E` and its identification with a
Fourier--Mukai kernel remain geometric realization obligations.
-/
