/-
ThreefoldTiltComparison slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Threefold.TiltComparison
open CategoryTheory.Triangulated

/-! ## The tilt family is the exponential kernel's, at m = 2

The abstraction-audit remediation recorded three unbridged spellings of the
(n, m) = (3, 2) tilt charge and asked for a comparison or a deletion (#1228).
Only Tilt.tiltFamily was ever declared. tiltFamily_eq_exp supplies the
kernel-level spelling as a theorem rather than a second carrier: the tilt family
IS Exp.chargeFamily at m = 2, reindexed by the surface chart after the
(alpha, beta) transposition and pulled back along threefoldTruncate. It needed
no construction, only stChargeFamily_eq and the three ChargeFamily naturality
lemmas. tiltFamily_charge_eq_exp is the same equation on a single class.

The transport-level spelling gets the opposite verdict and is recorded in the
module docstring: the implemented geometric transport pulls back the UNTILTED
Threefold.chargeFamily, which Tilt.exists_tilt_alignmentValue_ne_threefold
already separates from the tilt family with a computed witness. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.tiltFamily_eq_exp
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Tilt.tiltFamily_charge_eq_exp
