/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Exponential.Comparison
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Threefold.Tilt

/-!
# The tilt family is the kernel's, and there is only one of it

The abstraction-audit remediation recorded **three unbridged spellings** of the
`(n, m) = (3, 2)` tilt charge and asked for a comparison or a deletion (#1228).
This file settles the kernel-level one, and the module docstring records what
the other two turned out to be.

## The adjudication

`Tilt.tiltFamily` is canonical. It is the only one of the three that exists as a
Lean declaration.

* **`Exp.tiltChargeFamily`, the kernel-level spelling.** Never declared; the
  remediation planned it for a later slice that did not happen, and
  `Exponential/Kernel.lean` still forward-referenced it. `tiltFamily_eq_exp`
  below is that spelling, as a theorem rather than a second carrier: the tilt
  family **is** the exponential kernel at `m = 2`, reindexed by the surface
  chart and the `(alpha, beta)` transposition and pulled back along the
  truncation. Nothing needed constructing; the equation was available from
  `stChargeFamily_eq` and the three `ChargeFamily` naturality lemmas.
* **`tiltWallChargeFamily`, the transport-level spelling.** Never declared
  either. It existed only in `design-final.lean` in the sketch, and the
  implemented geometric transport is `ThreefoldWallTransport.wallChargeFamily`,
  which pulls back the **untilted** `Threefold.chargeFamily`. That is a
  different object, and `Tilt.exists_tilt_alignmentValue_ne_threefold` already
  proves it with a computed witness rather than leaving it to a docstring.

## The two slopes

`Threefold.nu` and `AlgebraicGeometry.Numerical.Stability.BMT.nu` both survive,
and neither is redundant: the first is the four-coordinate numerical model, the
second its realization on a polarised numerical threefold, which is the
separation `Numerical/Models/` versus `Numerical/Examples/` exists to keep. They
are bridged, in the direction the ownership policy wants, by
`ThreefoldWallTransport.nu_toNumClass`. No third slope is introduced here:
`Tilt.nu_eq_tilt_slope` states the tilt family's charge slope in terms of the
existing `Threefold.nu` rather than defining one.

This file adds no charge, no polynomial and no slope. It adds one equation.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

namespace Tilt

/-- **The tilt family is the exponential kernel's, at `m = 2`.**

This is the kernel-level spelling the remediation called `Exp.tiltChargeFamily`,
supplied as a comparison instead of a second carrier. The truncation degree is
`m = 2` and the dimension is three: the index is the truncation degree, never
the dimension, which is the whole point of `Exponential/Kernel.lean`'s index
discussion and the reason `numerical-k-theory-e5` was parked.

The parameter map is `Exp.stChart` after the `(alpha, beta)` transposition, and
the class map is the surface coordinate identification after the four-to-three
drop. Both were already there; only their composition is new. -/
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
