/-
DivisorialSupport slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.

This slice covers the two halves of the Kontsevich--Soibelman support property
on the real Mukai extension of a divisor space. It proves NEITHER supplied
input: DivisorSpace.HodgeDefinite is a proposition-valued certificate, and the
Bogomolov--Gieseker nonnegativity it is paired with is supplied by the caller
and audited in the AlgebraicGeometry lane. There is no scheme, sheaf, heart,
slicing, or stability condition here, and nothing below claims the charge is
one.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls
open CategoryTheory.Triangulated

/-! ## The strict Hodge certificate

HodgeDefinite is H^2 > 0 together with negative definiteness of the
intersection form on H-perp, which is what the Hodge index theorem gives on
N^1(X)_R for H ample. toHodgeIndex shows it implies the weaker inequality
certificate HodgeIndex; the converse is false, since the inequality permits an
isotropic class in H-perp. That gap is exactly what a support property cannot
tolerate, and is why the strict form is introduced. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeDefinite
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeDefinite.H_square_pos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeDefinite.neg_definite
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeDefinite.toHodgeIndex

/-! ## The bundled forms and the linear charge

realDiscriminant is Delta = c^2 - 2rs as a genuine QuadraticForm R on the real
Mukai extension R x D x R, without the halving of Mukai.realForm;
omegaTwistedDegree is the linear functional v |-> omega . (c - r B); and
realDiscriminantC is Delta + C (omega . c^B)^2, the Macri--Schmidt Definition
6.12 form, bundled. realCentralCharge is Mukai.expCharge as an R-linear map;
it is not a second charge formula. The four *_toRealExtension records are the
identifications with the unbundled functions of the Discriminant module, so
neither quantity is defined twice. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.omegaTwistedDegree_toRealExtension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.realCentralCharge_toRealExtension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.realDiscriminantC_toRealExtension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.realDiscriminant_toRealExtension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.omegaTwistedDegree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.omegaTwistedDegree_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.realCentralCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.realCentralCharge_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.realDiscriminant
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.realDiscriminantC
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.realDiscriminantC_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.realDiscriminant_apply

/-! ## Negative definiteness on the kernel

On ker Z the imaginary part of the charge kills the twisted omega-degree, so
the C term of Delta^C drops and NO sign condition on C is needed; the real part
eliminates s, leaving Delta^C(v) = (c^B)^2 - r^2 omega^2. HodgeDefinite then
gives strict negativity in both branches. Nonnegativity on a locus is NOT
proved here: hasQuadraticSupportProperty and hasSupportProperty take it as a
hypothesis, and hasQuadraticSupportProperty_image transports it along the class
map. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.hasQuadraticSupportProperty_image
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.hasQuadraticSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.hasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.omegaTwistedDegree_eq_zero_of_charge_eq_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.realDiscriminantC_neg_of_charge_eq_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.realDiscriminantC_of_charge_eq_zero
