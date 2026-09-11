/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.Spherical
import DerivedAlgGeo.CategoryTheory.Triangulated.SphericalTwist.Basic

/-!
# The K3 spherical Ext profile is an abstract spherical object

`Surface/Spherical.lean` states sphericity for `Dᵇ(Coh X)` on a smooth proper `X`;
`SphericalTwist/Basic.lean` states it for any `k`-linear category. This file is the one-way bridge,
and it is what lets the twist lane's Euler input be discharged from geometry.

## The direction is one-way, and deliberately so

`SphericalExtProfile E → IsSphericalObject k 2 E`, never the converse. The abstract predicate has
no canonical bundle and so no `E ⊗ ω_X ≅ E` content; on a K3 that clause is automatic because
`ω_X ≅ O_X`, which is why `Surface/Spherical.lean` can omit it. **The two omissions have different
reasons** — triviality there, vacuity here — and a converse would have to invent the first from the
second.

## Why the Euler agreement is not free

`selfEuler` is a bespoke three-term sum over degrees `0, 1, 2`; `chiHom` is a `finsum` over all of
`ℤ`. They agree for a spherical object because both compute `2`, the first by its definition and
the second by the `{0, 2}` support argument of `chiHom_self_eq`. Neither is definitionally the
other, and for a non-spherical object they need not agree at all: `selfEuler` ignores every degree
outside `0, 1, 2` while `chiHom` does not.
-/

universe u

open CategoryTheory CategoryTheory.Triangulated

namespace AlgebraicGeometry

namespace K3Surface

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k X] {E : DerivedCat X}

/-- **The K3 profile is an abstract `2`-spherical object.**

Field for field, with `ext_two` supplying `top_one`. Nothing is proved here beyond the
identification; the content is that the two spellings agree on the nose, which is what makes the
relocation in `SphericalTwist/Basic.lean` a generalisation rather than a redefinition. -/
theorem SphericalExtProfile.isSphericalObject (h : SphericalExtProfile (k := k) E) :
    SphericalTwist.IsSphericalObject k (2 : ℤ) E where
  vanishing := h.vanishing
  end_one := h.end_one
  top_one := h.ext_two

/-- **The three-term Euler sum agrees with the total one** for a spherical object.

Both sides are `2`. See the module docstring on why this is not a definitional identity and does
not extend to arbitrary objects. -/
theorem SphericalExtProfile.selfEuler_eq_chiHom (h : SphericalExtProfile (k := k) E) :
    selfEuler E = chiHom k (DerivedCat X) E E := by
  rw [h.selfEuler_eq_two,
    SphericalTwist.chiHom_self_eq h.isSphericalObject two_ne_zero,
    show (2 : ℤ) = 2 * 1 by norm_num, Int.negOnePow_two_mul]
  norm_num

end K3Surface

end AlgebraicGeometry
