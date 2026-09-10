/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Limits
import DerivedAlgGeo.Algebra.Homology.DerivedCategory

/-!
Audit records for generic derived-category extensions on arbitrary abelian
categories. Scheme and affine consumers are audited by AlgebraicGeometryAudit.
-/

/-! ## Short-exact derived triangles -/

#print axioms CategoryTheory.ShortComplex.ShortExact.singleTriangle.map_id
#print axioms CategoryTheory.ShortComplex.ShortExact.singleTriangle.map_comp
#print axioms CategoryTheory.ShortComplex.ShortExact.singleTriangle.map_comp_assoc

/-! ## Opposites and exact linear duality -/

#print axioms CategoryTheory.DerivedCategory.OppositeComparison
#print axioms CategoryTheory.DerivedCategory.OppositeComparison.mk.inj
#print axioms CategoryTheory.DerivedCategory.OppositeComparison.mk.sizeOf_spec
#print axioms CategoryTheory.DerivedCategory.OppositeComparison.equivalence
#print axioms ModuleCat.linearDualFunctor_obj
#print axioms ModuleCat.linearDualFunctor_map
#print axioms ModuleCat.fgSubmoduleDiagram
#print axioms ModuleCat.fgSubmoduleCocone
#print axioms ModuleCat.fgSubmoduleCocone_pt_carrier
#print axioms ModuleCat.fgSubmoduleCocone_ι_app
#print axioms ModuleCat.fgSubmoduleCoconeIsColimit
#print axioms ModuleCat.instAdditiveOppositeLinearDualFunctor
#print axioms ModuleCat.linearDualFunctor_map_shortExact
#print axioms ModuleCat.linearDualFunctor_preservesFiniteLimits_and_colimits
#print axioms ModuleCat.linearDualFunctor_preservesFiniteLimits
#print axioms ModuleCat.linearDualFunctor_preservesFiniteColimits
#print axioms ModuleCat.instPreservesFiniteLimitsOppositeLinearDualFunctor
#print axioms ModuleCat.instPreservesFiniteColimitsOppositeLinearDualFunctor
#print axioms ModuleCat.derivedLinearDualFunctor
#print axioms ModuleCat.derivedLinearDualFromOpposite
#print axioms ModuleCat.derivedLinearDualShift

/-! ## T-structures and exact derived functors -/

#print axioms CategoryTheory.tStructureIsLE_of_retract
#print axioms CategoryTheory.tStructureIsGE_of_retract
#print axioms CategoryTheory.instIsStableUnderRetractsMinus_derivedAlgGeo
#print axioms CategoryTheory.instIsStableUnderRetractsPlus_derivedAlgGeo
#print axioms CategoryTheory.instIsStableUnderRetractsBounded_derivedAlgGeo
#print axioms CategoryTheory.mapHomologicalComplex_isStrictlyLE
#print axioms CategoryTheory.mapHomologicalComplex_isStrictlyGE
#print axioms CategoryTheory.mapDerivedCategory_isLE
#print axioms CategoryTheory.mapDerivedCategory_isGE
#print axioms CategoryTheory.mapDerivedCategory_bounded
#print axioms CategoryTheory.mapDerivedCategoryHomologyIso
#print axioms CategoryTheory.NatIso.mapDerivedCategory
#print axioms CategoryTheory.Functor.mapDerivedCategoryIdIso
#print axioms CategoryTheory.Functor.mapDerivedCategoryCompIso
#print axioms CategoryTheory.Functor.singleFunctorIsoOfFactors
#print axioms DerivedCategory.isoOfFactors
#print axioms DerivedCategory.idFactors
#print axioms DerivedCategory.compFactors

/-! ## K-projective derived functors -/

#print axioms CategoryTheory.kProjectiveHomotopy
#print axioms CategoryTheory.KProjectiveHomotopyCategory
#print axioms CategoryTheory.kProjectiveHomotopyCategory_isKProjective
#print axioms CategoryTheory.kProjectiveQh
#print axioms CategoryTheory.kProjectiveQh_full
#print axioms CategoryTheory.kProjectiveQh_faithful
#print axioms CategoryTheory.KProjectiveDerivedCategory
#print axioms CategoryTheory.kProjectiveQhEquivalence
#print axioms CategoryTheory.KProjectiveHomotopyCategory.ofBoundedAboveProjectives
#print axioms CategoryTheory.kProjectiveDerivedFunctor
#print axioms CategoryTheory.kProjectiveLocusDerivedFunctor
#print axioms CategoryTheory.kProjectiveLocusDerivedComparison
#print axioms CategoryTheory.kProjectiveDerivedFunctorObjIso

/-! ## Bounded-above projective locus -/

#print axioms CategoryTheory.boundedAboveProjectiveHomotopy
#print axioms CategoryTheory.BoundedAboveProjectiveHomotopyCategory
#print axioms CategoryTheory.boundedAboveProjectiveHomotopy_le_kProjective
#print axioms CategoryTheory.boundedAboveProjectiveToKProjective
#print axioms CategoryTheory.boundedAboveProjectiveQh
#print axioms CategoryTheory.boundedAboveProjectiveHomotopyCategory_isKProjective
#print axioms CategoryTheory.boundedAboveProjectiveQh_full
#print axioms CategoryTheory.boundedAboveProjectiveQh_faithful
#print axioms CategoryTheory.BoundedAboveProjectiveDerivedCategory
#print axioms CategoryTheory.boundedAboveProjectiveQhEquivalence
#print axioms CategoryTheory.mapBoundedAboveProjectiveHomotopy
#print axioms CategoryTheory.mapBoundedAboveProjectiveHomotopyCompIso
#print axioms CategoryTheory.boundedAboveProjectiveDerivedFunctor
#print axioms CategoryTheory.boundedAboveProjectiveDerivedFunctorCompIso
#print axioms CategoryTheory.mapBoundedAboveProjectiveHomotopyIso
#print axioms CategoryTheory.mapBoundedAboveProjectiveHomotopyIdIso
#print axioms CategoryTheory.boundedAboveProjectiveDerivedFunctorIso
#print axioms CategoryTheory.boundedAboveProjectiveDerivedFunctorIdIso
#print axioms DerivedCategory.trW_subcategoryAcyclic_isStableUnderCoproductsOfShape
#print axioms DerivedCategory.hasCoproductsOfShape
#print axioms DerivedCategory.Qh_preservesCoproductsOfShape
#print axioms DerivedCategory.Q_preservesCoproductsOfShape
#print axioms DerivedCategory.homologyFunctor_preservesCoproductsOfShape
#print axioms DerivedCategory.cohomologyIn_isClosedUnderColimitsOfShape_discrete

/-! ## The heart of the canonical t-structure is the original category (#1121)

Mathlib names this as the motivating example of `TStructure.Heart` and leaves it unproved; nothing
in either tree identified the heart of the canonical t-structure with anything. Both halves already
existed -- `singleFunctor C 0` is additive, full and faithful, and its objects are `≤ 0` and `≥ 0`,
while `exists_iso_singleFunctor_obj_of_isGE_of_isLE` at `n = 0` is the converse -- so the content
here is the assembly into Mathlib's own `Heart` interface, plus the equivalence that transports
numerical data written on `C` onto the heart. -/

#print axioms DerivedCategory.heart_singleFunctor_obj
#print axioms DerivedCategory.essImage_singleFunctor_eq_heart
#print axioms DerivedCategory.isHeart
#print axioms DerivedCategory.ιHeart_eq
#print axioms DerivedCategory.toHeart
#print axioms DerivedCategory.toHeart_comp_ι
#print axioms DerivedCategory.toHeart_obj_obj
#print axioms DerivedCategory.heartEquivalence
#print axioms DerivedCategory.heartEquivalence_functor
