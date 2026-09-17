/-
NumericalThreefoldTiltTransport slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability

/-! ## The tilt family on a polarised threefold, and the slope it induces

ThreefoldWallTransport proves nu_toNumClass, that the four-coordinate model's
slope is the BMT.nu this directory already had. Walls/Threefold/Tilt proves
nu_eq_tilt_slope, that the same model slope is alpha times the tilt family's
charge slope. Neither alone connects Tilt.tiltFamily to a threefold, and #1228
owns the composition.

tiltFamily_im_toNumClass and tiltFamily_re_toNumClass restate the tilt charge in
the degrees this directory reads, which is what makes the slope theorems'
positivity hypothesis checkable on a threefold rather than on a coordinate of an
abstract quadruple. nu_eq_tiltFamily_slope is the composition; the ch0 slot in
the real part carries no beta, so the subtrahend reads the untwisted rank slot.
chargeSlope_tiltFamily_toNumClass is the same statement in the vocabulary
Abelian/Stability/ uses.

No tiltWallChargeFamily is minted here, and no third slope is defined. -/

#print axioms AlgebraicGeometry.Numerical.Threefold.tiltFamily_im_toNumClass
#print axioms AlgebraicGeometry.Numerical.Threefold.tiltFamily_re_toNumClass
#print axioms AlgebraicGeometry.Numerical.Threefold.nu_eq_tiltFamily_slope
#print axioms AlgebraicGeometry.Numerical.Threefold.chargeSlope_tiltFamily_toNumClass
