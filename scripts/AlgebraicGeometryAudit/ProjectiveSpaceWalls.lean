/-
ProjectiveSpaceWalls slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Threefold

/-! ## The threefold wall transport, on P3

Stability/ThreefoldWallTransport carries a polarised threefold class into the
four-coordinate (alpha, beta) charge plane, and Examples/Threefold/ProjectiveSpace
builds the P3 model. NOTHING CONNECTED THEM: the model was referenced only inside
its own file, and no polarization was defined for it at all. p3Polarization is
the first polarization of a threefold model here, and the four p3_toNumClass_deg
lemmas evaluate the transport: (a,b,c,e) goes to (a, b, -b/2 + c, b/6 - c + e),
which is threefoldChCoeff read against int H^3 = 1. p3_reZ and p3_imZ are the
charge in those coordinates.

p3BMTSanity IS NOT GEOMETRY. BMTData had no witness anywhere, so every
consequence of it was vacuous, and it cannot be given an honest one by proving
the inequality: the Bayer-Macri-Toda conjecture is FALSE for some threefolds
(the blow-up of P3 at a point, Schmidt) and true for P3 itself only by a real
theorem this repository does not contain. So TiltSemistable is DEFINED to be the
conclusion and nonneg holds tautologously, exactly as in k3BogomolovSanity. It
asserts NOTHING about sheaves or about tilt stability, and
p3_Q_toNumClass_nonneg has exactly that content, namely none. What the witness
buys is that the transported statements are about an inhabited structure.

No scheme, sheaf, heart, or tilt-stable object appears. -/

#print axioms AlgebraicGeometry.Numerical.Examples.p3BMTSanity
#print axioms AlgebraicGeometry.Numerical.Examples.p3Polarization
#print axioms AlgebraicGeometry.Numerical.Examples.p3Polarization_cls
#print axioms AlgebraicGeometry.Numerical.Examples.p3WallChargeFamily
#print axioms AlgebraicGeometry.Numerical.Examples.p3WallChargeFamily_charge
#print axioms AlgebraicGeometry.Numerical.Examples.p3_Q_toNumClass_nonneg
#print axioms AlgebraicGeometry.Numerical.Examples.p3_degree_H_pow_three
#print axioms AlgebraicGeometry.Numerical.Examples.p3_imZ
#print axioms AlgebraicGeometry.Numerical.Examples.p3_reZ
#print axioms AlgebraicGeometry.Numerical.Examples.p3_toNumClass_deg0
#print axioms AlgebraicGeometry.Numerical.Examples.p3_toNumClass_deg1
#print axioms AlgebraicGeometry.Numerical.Examples.p3_toNumClass_deg2
#print axioms AlgebraicGeometry.Numerical.Examples.p3_toNumClass_deg3
