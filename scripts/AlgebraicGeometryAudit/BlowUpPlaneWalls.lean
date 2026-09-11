/-
BlowUpPlaneWalls slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface

/-! ## Walls and chambers on the two-point blow-up

BlowUpPlane proved the hard part and got none of the consequences: it has
hodgeDefinite, the reverse Cauchy-Schwarz inequality for diag(1,-1,-1), and
hasSignatureTwo follows -- but no basis of the rank-three divisor space, and
Mukai.extendBasis wants one, so no lattice, no wall count, no region, no
chamber. divisorBasis is that missing ingredient and span_mukaiBasis identifies
the Z-span of its extension with the integral Mukai extension of
ZH + ZE_1 + ZE_2, which is the lattice the counts are stated against.

THIS IS THE MODEL WHERE THE STATEMENTS HAVE CONTENT. RankOneWalls has the same
chain on the line, but there omega-perp is zero and the definiteness clause of
the Hodge certificate says nothing. Here omega-perp is a genuine negative
definite plane.

Every hypothesis is discharged. Because hodgeDefinite needs only omega^2 > 0 on
this surface, so does everything below; no separate Hodge certificate is
carried. ampleBox is the compact family ||B|| <= b0 with omega on the segment
[t0,t1].omega_0 of a ray through a class of positive square, and
antiCanonical_sq_pos supplies -K = 3H - E_1 - E_2, of square 7, as such a class.

CHAMBERS SAY NOTHING ABOUT SEMISTABLE OBJECTS: chamber is a subset of the
parameter chart and no constancy on it is asserted. The carrier is not
identified with K_num(X) for a geometric blow-up, and no Hodge index theorem is
proved for one -- hodgeDefinite is proved for THIS lattice. -/

/-! ## The integral Neron-Severi lattice, and the spherical comparison

The blow-up had no integral lattice at all. IntLattice and intForm supply it --
ZH + ZE_1 + ZE_2 with diag(1,-1,-1) over Z -- and integralComparison is the
second witness for Spherical.IntegralComparison, the one where the form is NOT
definite: the lattice has isotropic vectors and the comparison is not a scaling
of Z. isSpherical_map_iff is the consequence, and
intLatticeMap_antiCanonical records that the ray the chamber statements use is
an integral class. -/

#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.IntLattice
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.ampleBox
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.antiCanonical_sq_pos
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.boxRegion
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.chamber_inter_ampleBox
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.divisorBasis
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.divisorCoordEquiv
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.finite_wallCandidates_ampleBox
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.finite_walls_meeting_ampleBox
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.finite_walls_meeting_antiCanonicalBox
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.finite_walls_through_expPlane
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.intForm
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.intForm_apply
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.intLatticeMap
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.intLatticeMap_antiCanonical
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.intLatticeMap_apply
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.integralComparison
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.isCompact_ampleBox
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.isSpherical_map_iff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.mukaiBasis
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.omega_sq_pos_on_ampleBox
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.span_mukaiBasis
