/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.K3Mukai
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.Pairing

/-!
# The integral of Mukai classes, evaluated on the rank-one K3 model

`Mukai/Pairing.lean` proves `χ(E,F) = ∫_X v(E)^∨·v(F)` and warns, at length, that the identity
carries **no** minus sign while the Mukai pairing does. This file is the arithmetic check on that
warning: on the degree-`2d` rank-one model both sides are explicit polynomials in the coordinates,
and the sign is either right or visibly wrong.

That is the point of the file. A sign error in `Pairing.lean` would still elaborate — every
statement there is an equation between two things the reader cannot evaluate — so the check has to
be somewhere the numbers are concrete.

## Placement

Here rather than in `Mukai/Pairing.lean`, because the model lives under `Numerical/Examples/` and
the general theory must not depend on an example. The dependency runs example → theory, never the
other way.
-/

open AlgebraicGeometry.Numerical

namespace AlgebraicGeometry.Numerical.Examples

/-- **The integral of Mukai classes on the model, written out.**

`∫_X v(E)^∨·v(F) = −(2d·c·c′ − r·s′ − r′·s)` with `s(E) = r + 2d·e₂`, which is exactly minus
`pairing_mukaiVector_k3`. The minus is the whole content: it is the sign relating the Mukai pairing
to the integral of the dual product. -/
theorem mukaiIntegral_k3 (d : ℕ) (hd : d ≠ 0) (E F : SurfaceNum) :
    K3.mukaiIntegral (k3NumericalVariety d) E F =
      -((2 * (d : ℤ) * (E 1) * (F 1)
          - (E 0) * (F 0 + 2 * (d : ℤ) * F 2)
          - (F 0) * (E 0 + 2 * (d : ℤ) * E 2) : ℤ) : ℚ) := by
  rw [K3.mukaiIntegral_eq_neg_mukaiPairing (k3_isK3 d hd), mukaiPairing_k3 d hd]

/-- **The Euler pairing on the model is that same polynomial**, with no sign in front.

Composing the headline identity with the evaluation above. Read together with
`mukaiIntegral_k3` this is the sign check in its sharpest form: `χ` and the integral agree, and
both are minus the Mukai pairing. -/
theorem chi₂_k3_eq_mukaiIntegral (d : ℕ) (hd : d ≠ 0) (E F : SurfaceNum) :
    (k3NumericalVariety d).chi₂ E F =
      -((2 * (d : ℤ) * (E 1) * (F 1)
          - (E 0) * (F 0 + 2 * (d : ℤ) * F 2)
          - (F 0) * (E 0 + 2 * (d : ℤ) * E 2) : ℤ) : ℚ) := by
  rw [K3.chi₂_eq_mukaiIntegral (k3_isK3 d hd), mukaiIntegral_k3 d hd]

/-- **The diagonal check the sign discussion names.**

The structure-sheaf class `![1,0,0]` is spherical, so its Mukai self-pairing is `−2` and the
integral of its dual product is `+2`. A sign error anywhere upstream lands here as `−2`. -/
theorem mukaiIntegral_structureSheaf_k3 (d : ℕ) (hd : d ≠ 0) :
    K3.mukaiIntegral (k3NumericalVariety d) ![1, 0, 0] ![1, 0, 0] = 2 := by
  rw [mukaiIntegral_k3 d hd]
  simp

end AlgebraicGeometry.Numerical.Examples
