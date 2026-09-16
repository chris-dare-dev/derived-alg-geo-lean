/-
Rotation slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Rotation
open CategoryTheory.Triangulated

/-! ## The phase rotation of a charge family

`ChargeFamily.phaseRotate beta` rescales every charge by `exp (-pi beta i)`. It
is not a new rotation: `phaseRotate_charge` proves it is
`WeakPreStabilityCondition.phaseTiltRotation`, which `Weak/Tilting/Semistable/
TiltGeometry.lean` already owns, and `phaseRotate_constFamily` proves it is
that condition's `phaseTiltCharge` on a constant family. The rotation scalar
has unit modulus, so `phaseRotate_alignmentValue` fixes the alignment
expression itself and not only its zero set;
`phaseRotate_alignmentLocus` is the locus statement, which is
`alignmentLocus_smul` at `Complex.exp_ne_zero`.
`exists_chargeSlope_phaseRotate_ne` is the negative result: the rotation is
free on alignment loci and provably not free on phases, so a construction that
drops it is wrong about semistability even where it is right about walls. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.phaseRotate
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.phaseRotate_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.phaseRotate_constFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.phaseRotate_alignmentValue
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.phaseRotate_alignmentLocus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily.exists_chargeSlope_phaseRotate_ne
