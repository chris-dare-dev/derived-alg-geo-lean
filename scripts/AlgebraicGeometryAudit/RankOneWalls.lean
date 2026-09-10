/-
RankOneWalls slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface

/-! ## Local finiteness of spherical walls, on a surface

surfaceHasSignatureTwo is the first record: the real Mukai extension of a
Picard-rank-one surface has signature (2,1), from hasSignatureTwo_of_hodgeDefinite
and surfaceHodgeDefinite. Nothing is assumed; the Hodge input is free on a line,
which is why the rank-one case is the honest first instance.

surfaceMukaiBasis is Mukai.extendBasis of the divisor line, and
span_surfaceMukaiBasis identifies its Z-span with the integral Mukai extension
Z + ZH + Z. That is what makes the counts below statements about INTEGRAL
classes rather than about an abstract ZSpan.

Two counts are recorded. surface_finite_walls_through_expPlane and its two K3
corollaries are POINTWISE: finitely many spherical classes have a wall through
the plane of exp(B + i omega), for one parameter pair. parameterBox and
surface_finite_walls_meeting_box are REGION-WISE, over the compact box
|B| <= b0, t0 <= omega <= t1 with t0 > 0, which is the form a wall-and-chamber
argument consumes; k3_finite_walls_meeting_box is that on the degree-2d K3.
Both discharge every hypothesis.

CHAMBERS ARE NOT PROVED, and nothing identifies the carrier with K_num(X) for a
geometric K3. -/

#print axioms AlgebraicGeometry.Numerical.Examples.isCompact_parameterBox
#print axioms AlgebraicGeometry.Numerical.Examples.k3HasSignatureTwo
#print axioms AlgebraicGeometry.Numerical.Examples.k3_finite_walls_integral
#print axioms AlgebraicGeometry.Numerical.Examples.k3_finite_walls_meeting_box
#print axioms AlgebraicGeometry.Numerical.Examples.k3_finite_walls_through_expPlane
#print axioms AlgebraicGeometry.Numerical.Examples.omega_sq_pos_on_parameterBox
#print axioms AlgebraicGeometry.Numerical.Examples.parameterBox
#print axioms AlgebraicGeometry.Numerical.Examples.span_surfaceMukaiBasis
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceDivisorBasis
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceHasSignatureTwo
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceMukaiBasis
#print axioms AlgebraicGeometry.Numerical.Examples.surface_finite_walls_meeting_box
#print axioms AlgebraicGeometry.Numerical.Examples.surface_finite_walls_through_expPlane
