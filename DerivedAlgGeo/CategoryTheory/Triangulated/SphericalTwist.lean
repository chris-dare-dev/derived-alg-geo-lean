/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Definition
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Autoequivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.BraidStatement
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Mukai
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.StabilityAction
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Braid
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedAdjunctionComparison
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctor
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctorH0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.EnhancedFunctorK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.ObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.LinearObjectTwistK0
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.ObjectTwistData

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
composite.  The additive and scalar-linear object-twist cones similarly act
as identity minus their evaluation functors.  Their parallel explicit
`IsEulerCopower` capabilities identify object classes with the existing
numerical `twistK₀` formula; automatic dg-functor exactness identifies the
induced maps.  The scalar-linear path requires no adapter to the
incompatible additive universal property.  It
deliberately stops short of asserting sphericality: the canonical
adjoint-comparison maps and their `H⁰` invertibility conditions are now named,
but the Morita/higher-cone theorem of Anno--Logvinenko is not a repository
primitive.  The object-specific
evaluation functor `RHom(E,-) ⊗ E` and its identification with a
Fourier--Mukai kernel remain geometric realization obligations.

`Definition.lean` states the functor `T_E` on an arbitrary `k`-linear pretriangulated category as
supplied data, `SphericalTwistData`, and proves that its map on `K₀` is `twistK₀`.
`ObjectTwistData.lean` realizes it by both dg object twists. `Autoequivalence.lean` and
`BraidStatement.lean` state the Seidel--Thomas autoequivalence and braid theorems as supplied,
unasserted structures, and derive their `TwistShaped` and `K₀` consequences.
-/
