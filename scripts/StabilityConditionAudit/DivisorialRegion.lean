/-
DivisorialRegion slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.

This subtree contains NO scheme, sheaf, numerical intersection ring, heart,
slicing, or stability condition. DivisorSpace.HodgeDefinite is a
proposition-valued certificate supplied by the caller and is never proved here.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls
open CategoryTheory.Triangulated

/-! ## Region-wise local finiteness of spherical walls

Divisorial/Signature counts the walls through ONE plane. That is not enough for
a wall-and-chamber structure, which needs finiteness across a neighbourhood.

QuadraticForm/WallRegion records that the coercivity constant of -Q on W-perp
degrades to 0 at the boundary of the positive-plane locus, so a family inherits
no constant from its members and PlaneRegion carries it as a field. Its
criterion ofCompactPairs supplies that field for a COMPACT family -- but only
from PeriodDomain.HasSignatureTwo, which nothing could provide for a divisor
space until hasSignatureTwo_of_hodgeDefinite. So the input here is the same
single certificate as everywhere else in this subtree.

expPairMap sends (B, omega) to the spanning pair of the plane of exp(B + i omega),
and continuous_expPairMap is what turns a compact set of PARAMETERS into a
compact set of PAIRS; it holds because the intersection form is a bilinear map
on a finite-dimensional space. expPlaneRegion packages the region, and
finite_walls_meeting_expFamily states the count with the parameters rather than
the region, which is the form a chamber argument consumes.

CHAMBERS ARE NOT PROVED. Finitely many walls meeting a compact family does not
by itself produce the connected components of its complement, nor constancy of
the semistable objects on one. The lattice is the Z-span of an R-basis and is
not asserted to be a geometric lattice. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.continuous_expPairMap
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.continuous_pair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.exists_ampleLower
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.exists_uniform_negDefinite
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.expPairMap
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.expPairMap_fst
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.expPairMap_snd
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.expPlaneRegion
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.expPlaneRegion_carrier
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.expPlane_eq_span
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.finite_wallClasses_expPlaneRegion
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.finite_walls_meeting_expFamily
