/-
Threefold tilt slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Threefold.Tilt
open CategoryTheory.Triangulated

/-! ## The tilt family, as the surface family pulled back along a truncation

The `(n, m) = (3, 2)` tilt charge introduces no polynomial and no kernel.
`tiltFamily` is `stChargeFamily` -- the existing surface family owned by
`CentralCharge/Numerical/SurfaceFamily.lean` -- reindexed by `Prod.swap` and
pulled back along `threefoldTruncate`, which is the one new construction here:
the additive map forgetting the fourth compressed degree. `tiltFamily_re` and
`tiltFamily_im` write the result in Bayer--Macri--Toda coordinates, and
`nu_eq_tilt_slope` and `chargeSlope_tilt` identify the existing `Threefold.nu`
with the charge slope rescaled by `alpha`, under the hypothesis the slope
convention needs.

`rotatedTiltFamily` is that family at `phaseRotate (1/2)`, and
`rotatedTiltFamily_alignmentLocus_eq_preimage` makes every rotated tilt wall a
`Prod.swap` preimage of an `stChargeFamily` alignment locus, which is what lets
the surface nested-semicircle theorems apply to tilt walls at all.

Two negative results are audited with the rest, because they are what stops the
construction being read as more than it is.
`exists_tilt_alignmentValue_ne_threefold` is the computed witness that the tilt
family is NOT a chart change of `Threefold.chargeFamily`: two classes sharing a
truncation but differing in the fourth degree are aligned for one family and
not the other. `exists_chargeSlope_rotatedTiltFamily_ne` is the computed
witness that the rotation moves `chargeSlope` even though it fixes every
alignment value, so dropping it is wrong about semistability exactly where it
is right about walls.

No heart, slicing or BMT inequality is asserted; this slice audits numerical
data. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.threefoldTruncate
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.threefoldTruncate_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.rk_threefoldTruncate
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.deg_threefoldTruncate
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.ch2_threefoldTruncate
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.tiltFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.rotatedTiltFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.tiltFamily_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.tiltFamily_re
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.tiltFamily_im
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.nu_eq_tilt_slope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.chargeSlope_tilt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.rotatedTiltFamily_alignmentLocus_eq_preimage
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.rotatedTiltFamily_alignmentValue
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.exists_tilt_alignmentValue_ne_threefold
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.exists_chargeSlope_rotatedTiltFamily_ne
