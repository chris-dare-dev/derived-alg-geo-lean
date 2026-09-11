import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveVariety

/-!
# Serre finiteness for projective varieties (#332 step 3)

## The closed-immersion comparison is linear (Cohomology/Finiteness/ProjectiveVariety.lean)

The base field acts through global functions; a morphism over `Spec k` pulls the global function
of the target back to that of the source, and pushforward carries multiplication by the pulled-back
function to multiplication by the original. The comparison is natural in the sheaf, so it
commutes with the scalar endomorphisms. `coherentHPushforwardAddEquiv` is the closed-immersion
comparison at the `HasExt` witness `coherentH` uses, `HasExt.standard`. -/

#print axioms AlgebraicGeometry.Cohomology.baseFieldToGlobalSections_comp
#print axioms AlgebraicGeometry.Cohomology.pushforward_varietyScalarAction
#print axioms AlgebraicGeometry.Cohomology.pushforward_coherentScalarAction
#print axioms AlgebraicGeometry.Cohomology.coherentHPushforwardAddEquiv
#print axioms AlgebraicGeometry.Cohomology.coherentHPushforwardAddEquiv_naturality
#print axioms AlgebraicGeometry.Cohomology.coherentHPushforwardAddEquiv_smul
#print axioms AlgebraicGeometry.Cohomology.coherentHPushforwardLinearEquiv
#print axioms AlgebraicGeometry.Cohomology.module_finite_linearCoherentH_of_isClosedImmersion

/-! ## Projective varieties

The two spellings of the structure morphism of `Pⁿ` agree, and finiteness on `Pⁿ` descends along
the presentation's closed immersion. `finiteDimensionalCohomology` and `finiteCohomology` inhabit
the packages by theorem for any presentation into a projective space with at least two
coordinates; nothing is supplied. -/

#print axioms AlgebraicGeometry.projectiveSpaceToSpec_eq
#print axioms AlgebraicGeometry.ProjectivePresentation.module_finite_linearCoherentH
#print axioms AlgebraicGeometry.ProjectivePresentation.finiteDimensionalCohomology
#print axioms AlgebraicGeometry.ProjectivePresentation.finiteCohomology
