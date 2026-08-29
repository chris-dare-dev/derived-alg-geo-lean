/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.GrothendieckGroup

/-! # The spherical twist

The Seidel--Thomas twist `T_E`, approached from `K₀` upwards. This umbrella
currently re-exports the `K₀`-level twist only: `τ_E(x) = x - χ(E, x) • [E]`,
its involutivity, and its preservation of the Euler form.

The autoequivalence `T_E` itself is not here and is not asserted anywhere in
this directory. It is defined by the cone of an evaluation map, which needs a
Hom-complex tensor and a functorial cone; see the lane's remaining issues.
-/
