/-
FourfoldWalls slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Fourfold

/-! ## The fourfold wall layer, at zero polynomial cost

The fourfold numerical models existed with proved Riemann-Roch and NO CHARGE
REACHED THEM: no fourfold charge or wall family existed anywhere in the tree,
because every charge in the tree was written per dimension and nobody had
written the dimension-four one.

NOTHING IN THIS SLICE IS A CHARGE POLYNOMIAL. The whole content is one
Polarization per model -- p4Polarization on P4 and sexticPolarization on the
smooth sextic in P5 -- after which Polarised.wallChargeFamily at
(n, m, kappa) = (4, 4, 1) supplies the family and Wall.Exp.ofMoments supplies
the polynomial. That is what the root bought, and a reviewer can confirm it
from the diff: p4_charge and sextic_charge EVALUATE the kernel's coefficients
1, -1, 1/2, -1/6, 1/24 rather than declaring them.

The degree is visible on exactly one of the two models. int_P4 H^4 = 1, so the
five slots of p4_hDegrees_eq_chCoeff are the linear-section Chern coefficients
on the nose; int_X H^4 = 6 on the sextic, so sextic_hDegrees_eq_chCoeff carries
the factor 6 in all five slots and sextic_charge factors it out. THAT
FACTORISATION IS A FACT ABOUT PICARD RANK ONE, NOT ABOUT THE TRANSPORT: slot 0
carries int H^n in every dimension and every Picard rank, which is the root's
hDegrees_zero, while the other slots share the factor here only because there
is a single generator to integrate against.

ONE GAP, RECORDED RATHER THAN FILLED. The n = 4 graded pairing has no
counterpart in this repository: no fourfold discriminant, no fourfold
self-pairing, hence no comparison to prove and no consumer to serve. The charge
needs none of it, so the slot is left genuinely empty. A pairing invented to
fill it would be a definition with no leaf reaching it.

kappa stays at unitCorr on both models, so these are plain Chern characters and
not Mukai vectors. On a Calabi-Yau fourfold td_1 = td_3 = 0, so sqrt(td) differs
from 1 in codimensions two and four and corrComp there gives a genuinely
different family rather than a rescaling of this one. The two must not be fused.

No scheme, sheaf, heart, or stable object appears. -/

#print axioms AlgebraicGeometry.Numerical.Examples.p4_degree_H_pow_four
#print axioms AlgebraicGeometry.Numerical.Examples.p4Polarization
#print axioms AlgebraicGeometry.Numerical.Examples.p4Polarization_cls
#print axioms AlgebraicGeometry.Numerical.Examples.p4_hDegrees_eq_chCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.p4WallChargeFamily
#print axioms AlgebraicGeometry.Numerical.Examples.p4WallChargeFamily_charge
#print axioms AlgebraicGeometry.Numerical.Examples.p4_charge
#print axioms AlgebraicGeometry.Numerical.Examples.sextic_degree_H_pow_four
#print axioms AlgebraicGeometry.Numerical.Examples.sexticPolarization
#print axioms AlgebraicGeometry.Numerical.Examples.sexticPolarization_cls
#print axioms AlgebraicGeometry.Numerical.Examples.sextic_hDegrees_eq_chCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.sexticWallChargeFamily
#print axioms AlgebraicGeometry.Numerical.Examples.sexticWallChargeFamily_charge
#print axioms AlgebraicGeometry.Numerical.Examples.sextic_charge
