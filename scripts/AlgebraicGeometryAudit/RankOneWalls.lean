/-
RankOneWalls slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface

/-! ## Local finiteness of spherical walls, on a surface

surfaceHasSignatureTwo is the first record here: the real Mukai extension of a
Picard-rank-one surface has signature (2,1), obtained from
hasSignatureTwo_of_hodgeDefinite and surfaceHodgeDefinite. Nothing is assumed;
the Hodge input is free on a line, which is why the rank-one case is the honest
first instance.

surfaceMukaiBasis is Mukai.extendBasis of the divisor line, and
span_surfaceMukaiBasis identifies its Z-span with the integral Mukai extension
Z + ZH + Z. That is what makes the finiteness statements below statements about
INTEGRAL classes rather than about an abstract ZSpan.

surface_finite_walls_through_expPlane and its two K3 corollaries then say: only
finitely many spherical classes of that lattice have a wall through the plane of
exp(B + i omega), for every omega non-zero. Both hypotheses are discharged.

The region-wise statement is not here, for the reason recorded in the
StabilityCondition lane. Nothing identifies the carrier with K_num(X) for a
geometric K3. -/

#print axioms AlgebraicGeometry.Numerical.Examples.k3HasSignatureTwo
#print axioms AlgebraicGeometry.Numerical.Examples.k3_finite_walls_integral
#print axioms AlgebraicGeometry.Numerical.Examples.k3_finite_walls_through_expPlane
#print axioms AlgebraicGeometry.Numerical.Examples.span_surfaceMukaiBasis
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceDivisorBasis
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceHasSignatureTwo
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceMukaiBasis
#print axioms AlgebraicGeometry.Numerical.Examples.surface_finite_walls_through_expPlane
