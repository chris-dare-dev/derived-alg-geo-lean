/-
The linear cohomology and projective-geometry slice of the AlgebraicGeometry audit,
split out so concurrent branches append to different files (#480). See the umbrella file
for the contract.

The records here cover the `k`-linear form against `coherentScalarAction`, integrality of
`Proj` of a graded domain, and polynomial projective space as a variety.
-/
import DerivedAlgGeo.AlgebraicGeometry
open AlgebraicGeometry

#print axioms AlgebraicGeometry.Cohomology.coherentH
#print axioms AlgebraicGeometry.Cohomology.LinearCohomology
#print axioms AlgebraicGeometry.Cohomology.FiniteDimensionalCohomology
#print axioms AlgebraicGeometry.Cohomology.globalSectionSmul
#print axioms AlgebraicGeometry.Cohomology.globalSectionSmul_app
#print axioms AlgebraicGeometry.Cohomology.globalSectionAction
#print axioms AlgebraicGeometry.Cohomology.globalSectionSmul_naturality
#print axioms AlgebraicGeometry.Cohomology.baseFieldToGlobalSections
#print axioms AlgebraicGeometry.Cohomology.varietyScalarAction
#print axioms AlgebraicGeometry.Cohomology.varietyScalarAction_naturality
#print axioms AlgebraicGeometry.Cohomology.coherentScalarAction
#print axioms AlgebraicGeometry.Cohomology.coherentScalarAction_naturality
#print axioms AlgebraicGeometry.Cohomology.additiveMapEndRingHom
#print axioms AlgebraicGeometry.Cohomology.addCommGrpEndRingHom
#print axioms AlgebraicGeometry.Cohomology.coherentH_additive
#print axioms AlgebraicGeometry.Cohomology.coherentHScalarAction
#print axioms AlgebraicGeometry.Cohomology.coherentHModule
#print axioms AlgebraicGeometry.Cohomology.coherentH_map_smul
#print axioms AlgebraicGeometry.Cohomology.linearCoherentH
#print axioms AlgebraicGeometry.Cohomology.linearCoherentHComparison
#print axioms AlgebraicGeometry.Cohomology.canonicalLinearCohomology
#print axioms AlgebraicGeometry.Cohomology.FiniteDimensionalCohomology.dimension
#print axioms AlgebraicGeometry.Cohomology.FiniteDimensionalCohomology.dimension_iso
#print axioms AlgebraicGeometry.Proj.isReduced_spec_away
#print axioms AlgebraicGeometry.Proj.isReduced
#print axioms AlgebraicGeometry.Proj.isDomain_away
#print axioms AlgebraicGeometry.Proj.isPreirreducible_basicOpen
#print axioms AlgebraicGeometry.Proj.basicOpen_nonempty
#print axioms AlgebraicGeometry.Proj.irreducibleSpace
#print axioms AlgebraicGeometry.Proj.isIntegral
#print axioms AlgebraicGeometry.Proj.intShiftOverSelfIso
#print axioms AlgebraicGeometry.Proj.intShift_isCoherent
#print axioms AlgebraicGeometry.Proj.algebraMap_polynomialGradeZero_surjective
#print axioms AlgebraicGeometry.Proj.finiteType_polynomialGradeZero
#print axioms AlgebraicGeometry.Proj.isScalarTower_polynomialGradeZero
#print axioms AlgebraicGeometry.Proj.finiteType_polynomialGrading
#print axioms AlgebraicGeometry.Proj.projectiveSpaceToSpec
#print axioms AlgebraicGeometry.Proj.locallyOfFiniteType_projectiveSpaceToSpec
#print axioms AlgebraicGeometry.Proj.nonempty_projectiveSpace
#print axioms AlgebraicGeometry.Proj.instOverProjectiveSpace
#print axioms AlgebraicGeometry.Proj.isVariety_projectiveSpace
#print axioms AlgebraicGeometry.Proj.polynomialIntShift_isCoherent
#print axioms AlgebraicGeometry.Proj.projectiveSpaceTwist
#print axioms AlgebraicGeometry.Proj.projectiveSpaceTwist_obj
#print axioms AlgebraicGeometry.Proj.isLocallyNoetherian_projectiveSpace
#print axioms AlgebraicGeometry.Proj.homogeneousZeroRingEquiv_toRingHom_eq_algebraMap
#print axioms AlgebraicGeometry.Proj.projectiveSpaceToSpec_eq
#print axioms AlgebraicGeometry.Proj.projectiveSpaceSelfEmbedding
#print axioms AlgebraicGeometry.Proj.projectiveSpaceSelfEmbedding_isClosedImmersion
#print axioms AlgebraicGeometry.Proj.projectiveSpaceSelfPresentation
#print axioms AlgebraicGeometry.Proj.isProjective_projectiveSpace
#print axioms TopologicalSpace.isPreirreducible_univ_of_cover
#print axioms TopologicalSpace.irreducibleSpace_of_cover
