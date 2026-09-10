/-
DivisorialSignature slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.

This subtree contains NO scheme, sheaf, numerical intersection ring, heart,
slicing, or stability condition. It proves neither a Bogomolov inequality nor a
Hodge index theorem; DivisorSpace.HodgeDefinite is a proposition-valued
certificate supplied by the caller.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls
open CategoryTheory.Triangulated

/-! ## The Hodge certificate is the signature hypothesis

sigPos_sigNeg_of_hodgeDefinite translates DivisorSpace.HodgeDefinite into the
indices of inertia: the form splits orthogonally as the H-line plus H-perp,
positive definite on the first and negative definite on the second, so
sigPos = 1 and sigNeg = dim D - 1 by QuadraticMap.sigPos_eq_add. The weaker
HodgeIndex certificate would NOT do: it permits an isotropic class in H-perp,
which puts a radical in the form and breaks the count.

hasSignatureTwo_of_hodgeDefinite then feeds Mukai.hasSignatureTwo_realForm, so
PeriodDomain.HasSignatureTwo -- carried as an assumption by every period-domain
result -- becomes a consequence of the same certificate the support property
uses. Nothing here proves that certificate for a geometric surface. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeDefinite.of_pair_pos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.expPlane
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.finite_sphericalOrthogonal_expPlane
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.finite_walls_through_expPlane
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.hasSignatureTwo_of_hodgeDefinite
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.intersectionQuadratic
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.intersectionQuadratic_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.isPositivePlane_expPlane
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.nondegenerate_of_hodgeDefinite
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.polar_intersectionQuadratic
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.sigPos_sigNeg_of_hodgeDefinite
