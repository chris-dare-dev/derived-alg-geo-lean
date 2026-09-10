/-
RankOneRealization slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface

/-! ## The real divisor realization of a Picard-rank-one surface, and the K3 model

RankOne.lean built the rational ring Q[H]/(H^3) with int H^2 = h2, and K3,
ProjectivePlane and Abelian are three variety presentations over it, but none
had a Surface.NumericalRealization. Every divisorial statement about them was
therefore conditional on a realization existing. surfaceRealization supplies it
once for every h2: the divisor space is the line R with intersection form
h2*x*y.

surfaceHodgeDefinite is free in rank one, because the orthogonal complement of
a nonzero vector on a line is zero and the definiteness clause is vacuous; only
omega^2 > 0 carries content. That is deliberate, and it is what separates "the
support property argument is correct" from "the Hodge input is available".
k3HasQuadraticSupportProperty then fires on a model rather than on hypotheses.

Its Bogomolov input is k3BogomolovSanity, whose Semistable predicate is DEFINED
to be 0 <= discDegH, so the locus is the nonnegative-discriminant locus and
NOTHING is claimed about semistable sheaves. What is not tautologous is
negativity of the C-discriminant on the kernel of the charge.

k3Realization_sqrtTodd and k3Realization_mukaiCharge fire the Mukai adapter on
the same model. The carrier is not identified with K_num(X) for a geometric K3. -/

#print axioms AlgebraicGeometry.Numerical.Examples.SurfaceDivisor
#print axioms AlgebraicGeometry.Numerical.Examples.coord_idx1_smul_H
#print axioms AlgebraicGeometry.Numerical.Examples.exists_smul_H
#print axioms AlgebraicGeometry.Numerical.Examples.idx1
#print axioms AlgebraicGeometry.Numerical.Examples.k3HasQuadraticSupportProperty
#print axioms AlgebraicGeometry.Numerical.Examples.k3HasSupportProperty
#print axioms AlgebraicGeometry.Numerical.Examples.k3HodgeDefinite
#print axioms AlgebraicGeometry.Numerical.Examples.k3Realization
#print axioms AlgebraicGeometry.Numerical.Examples.k3Realization_chernCharacter_chOne
#print axioms AlgebraicGeometry.Numerical.Examples.k3Realization_chernCharacter_chTwo
#print axioms AlgebraicGeometry.Numerical.Examples.k3Realization_chernCharacter_rank
#print axioms AlgebraicGeometry.Numerical.Examples.k3Realization_divisorSpace
#print axioms AlgebraicGeometry.Numerical.Examples.k3Realization_mukaiCharge
#print axioms AlgebraicGeometry.Numerical.Examples.k3Realization_polarization
#print axioms AlgebraicGeometry.Numerical.Examples.k3Realization_sqrtTodd
#print axioms AlgebraicGeometry.Numerical.Examples.one_lt_dim
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceDivisorClass
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceDivisorClass_H
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceDivisorClass_apply
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceDivisorClass_intersection
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceDivisorClass_map_rat_smul
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceDivisorSpace
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceDivisorSpace_pair
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceHodgeDefinite
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceIntersectionForm
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceIntersectionForm_apply
#print axioms AlgebraicGeometry.Numerical.Examples.surfacePB_basis_idx1
#print axioms AlgebraicGeometry.Numerical.Examples.surfacePieceOne_eq_span
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceRealization
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceRealization_divisorSpace
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceW_preimage_one
