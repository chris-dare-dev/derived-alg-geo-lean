/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Dual

/-!
# Line-bundle data from an intrinsically invertible sheaf

`LineBundleData` (in `Divisors.Determinant`) packages an invertible sheaf together with an
explicit tensor inverse. `dualLine` (in `Divisors.Dual`) produces such an inverse. This file
is the one place where the two meet.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.LineBundleData.ofIsInvertible` upgrades an intrinsically
  invertible sheaf to line-bundle data whose inverse is its sheafified dual.

## Main results

This file proves no theorems; the invertibility and tensor-inverse fields come from
`dualLine_isInvertible` and `tensorDualIso`.

## Implementation notes

### Why this is its own file

This declaration is the only point at which the dual-line API needs `Divisors.Determinant`.
Keeping it in a leaf keeps `Divisors.Dual` independent of `Determinant`, and so of
`ExteriorPower`, an expensive module to elaborate: `Dual` and `ExteriorPower` then elaborate in
parallel, and a change to `ExteriorPower` or `Determinant` does not rebuild `Dual`.

Keep this file a leaf. Anything added here that does not genuinely need *both* `Determinant` and
`Dual` belongs in whichever of them it actually depends on, or the edge comes back.

## References

This combines `AlgebraicGeometry.Scheme.Modules.LineBundleData` with `dualLine`,
`dualLine_isInvertible` and `tensorDualIso`, built on Mathlib's `SheafOfModules.IsInvertible`.

## Tags

line bundle, invertible sheaf, dual, tensor inverse
-/

universe u

open CategoryTheory TopologicalSpace Opposite MonoidalCategory

-- As in `Divisors.Dual`, whose declarations this one is built from.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

/-- Upgrade an intrinsically invertible sheaf to line-bundle data with an
explicit sheafified-dual tensor inverse. -/
noncomputable def LineBundleData.ofIsInvertible (L : X.Modules)
    [hL : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] : LineBundleData X where
  line := L
  inverse := dualLine L
  lineIsInvertible := hL
  inverseIsInvertible := dualLine_isInvertible L
  tensorInverseIso := tensorDualIso L

end

end AlgebraicGeometry.Scheme.Modules
