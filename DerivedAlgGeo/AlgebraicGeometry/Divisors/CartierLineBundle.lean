/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.AssociatedSheaf.PicardMap
import DerivedAlgGeo.AlgebraicGeometry.Divisors.LineBundleDual

/-!
# Cartier divisors as line-bundle data

The associated sheaf of a Cartier divisor is intrinsically invertible.
`CartierDivisor.lineBundleData` upgrades it to the repository's explicit
`LineBundleData` interface, choosing the sheafified dual as tensor inverse.
The resulting Picard class agrees with the direct Cartier-divisor
construction.

This bridge is deliberately a leaf: it needs both the associated-sheaf API
and the determinant/dual line-bundle API. Keeping it out of the narrower
`Divisors.AssociatedSheaf` umbrella avoids imposing the expensive determinant
dependency on consumers such as effective-divisor exact sequences.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.CartierDivisor

variable {X : Scheme.{u}} [IsIntegral X]

noncomputable section

/-- The line-bundle package canonically associated to a Cartier divisor. Its
underlying sheaf is `O_X(D)` and its chosen inverse is the sheafified dual. -/
noncomputable def lineBundleData (D : CartierDivisor X) :
    Modules.LineBundleData X :=
  Modules.LineBundleData.ofIsInvertible (associatedSheaf D)

@[simp]
theorem lineBundleData_line (D : CartierDivisor X) :
    (lineBundleData D).line = associatedSheaf D :=
  rfl

@[simp]
theorem lineBundleData_inverse (D : CartierDivisor X) :
    (lineBundleData D).inverse = Modules.dualLine (associatedSheaf D) :=
  rfl

/-- The Picard class obtained through explicit line-bundle data is the same
class as the direct Cartier-divisor construction. The chosen inverse objects
may differ, but `Pic` remembers only their invertible classes. -/
@[simp]
theorem lineBundleData_toPic (D : CartierDivisor X) :
    (lineBundleData D).toPic = toPic D := by
  apply Units.ext
  rfl

/-- A Cartier divisor's associated sheaf is coherent, exposed through the
canonical line-bundle adapter rather than reproved from local equations. -/
theorem associatedSheaf_isCoherent (D : CartierDivisor X) :
    Scheme.coherent X (associatedSheaf D) :=
  (lineBundleData D).isCoherent

end

end AlgebraicGeometry.Scheme.CartierDivisor
