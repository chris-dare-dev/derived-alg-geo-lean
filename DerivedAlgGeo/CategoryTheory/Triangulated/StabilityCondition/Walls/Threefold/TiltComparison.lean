/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Exponential.Comparison
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Threefold.Tilt

/-!
# The tilt family is the kernel's, and there is only one of it

The `(n, m) = (3, 2)` tilt charge has one carrier, `Tilt.tiltFamily`. This file
proves that it is the exponential kernel of `Exponential/Kernel.lean` at
truncation degree `m = 2`, so the kernel-level form of the tilt charge is a
theorem rather than a second carrier.

## Main definitions

This file introduces no new definitions: no charge, no polynomial and no slope.

## Main results

* `Tilt.tiltFamily_eq_exp` -- the tilt family **is** the exponential kernel at
  `m = 2`, reindexed by the surface chart and the `(alpha, beta)`
  transposition and pulled back along the truncation.
* `Tilt.tiltFamily_charge_eq_exp` -- the same equation read off a single class.

## Implementation notes

### One carrier

`Tilt.tiltFamily` is canonical; it is the only Lean declaration of the tilt
charge family.

* The kernel-level form is `tiltFamily_eq_exp`, a theorem rather than a second
  carrier. Nothing needed constructing; the equation follows from
  `stChargeFamily_eq` and the three `ChargeFamily` naturality lemmas.
* The geometric transport `AlgebraicGeometry.Numerical.Threefold.wallChargeFamily`
  pulls back the **untilted** `Threefold.chargeFamily`. That is a different
  object, and `Tilt.exists_tilt_alignmentValue_ne_threefold` proves it with a
  computed witness rather than leaving it to a docstring.

### The two slopes

`Threefold.nu` and `AlgebraicGeometry.Numerical.Threefold.nu` both survive, and
neither is redundant: the first is the four-coordinate numerical model, the
second its realization on a polarised numerical threefold, which is the
separation `Numerical/Models/` versus `Numerical/Examples/` exists to keep. They
are bridged, in the direction the ownership policy wants, by
`AlgebraicGeometry.Numerical.Threefold.nu_toNumClass`. No third slope is
introduced here: `Tilt.nu_eq_tilt_slope` states the tilt family's charge slope
in terms of the existing `Threefold.nu` rather than defining one.

## References

This file cites no literature. It builds on `Wall.Exp.chargeFamily`,
`Wall.Tilt.tiltFamily` and `Wall.stChargeFamily_eq`.

## Tags

tilt stability, charge family, exponential charge, truncation degree
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

namespace Tilt

/-- **The tilt family is the exponential kernel's, at `m = 2`.**

This is the kernel-level form of the tilt charge, supplied as a comparison
instead of a second carrier. The truncation degree is `m = 2` and the dimension
is three: the index is the truncation degree, never the dimension, which is the
whole point of `Exponential/Kernel.lean`'s index discussion.

The parameter map is `Exp.stChart` after the `(alpha, beta)` transposition, and
the class map is the surface coordinate identification after the four-to-three
drop. Both exist independently; only their composition is new. -/
theorem tiltFamily_eq_exp :
    tiltFamily
      = ((Exp.chargeFamily 2).reindex (Exp.stChart ∘ _root_.Prod.swap)).pullback
          (surfaceVec.toAddMonoidHom.comp threefoldTruncate) := by
  rw [tiltFamily, stChargeFamily_eq, ChargeFamily.pullback_reindex,
    ChargeFamily.pullback_pullback, ChargeFamily.reindex_reindex]

/-- The same equation read off a single class, which is the form a consumer
wanting the kernel's moments actually needs. -/
theorem tiltFamily_charge_eq_exp (p : ℝ × ℝ) (v : Threefold.NumClass) :
    tiltFamily.charge p v
      = Exp.charge 2 (Exp.stChart p.swap) (surfaceVec (threefoldTruncate v)) := by
  rw [tiltFamily_eq_exp]
  rfl

end Tilt

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
