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
#print axioms CategoryTheory.Adjunction.mapHomologicalComplex
#print axioms CategoryTheory.Adjunction.mapDerivedCategory
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
#print axioms DerivedCategory.singleFunctor_preservesCoproductsOfShape
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
#print axioms DerivedCategory.toHeart_full
#print axioms DerivedCategory.toHeart_faithful
#print axioms DerivedCategory.toHeart_essSurj
#print axioms DerivedCategory.toHeart_isEquivalence
#print axioms DerivedCategory.toHeart_obj_obj
#print axioms DerivedCategory.heartEquivalence
#print axioms DerivedCategory.heartEquivalence_functor

/-! ## The standard heart of the bounded derived category (#1121) -/

#print axioms DerivedCategory.boundedSingleFunctor
#print axioms DerivedCategory.boundedSingleFunctor_additive
#print axioms DerivedCategory.boundedSingleFunctor_full
#print axioms DerivedCategory.boundedSingleFunctor_faithful
#print axioms DerivedCategory.boundedSingleFunctor_obj_obj
#print axioms DerivedCategory.boundedHeart_singleFunctor_obj
#print axioms DerivedCategory.essImage_boundedSingleFunctor_eq_boundedHeart
#print axioms DerivedCategory.isBoundedHeart
#print axioms DerivedCategory.toBoundedHeart
#print axioms DerivedCategory.toBoundedHeart_comp_ι
#print axioms DerivedCategory.toBoundedHeart_full
#print axioms DerivedCategory.toBoundedHeart_faithful
#print axioms DerivedCategory.toBoundedHeart_essSurj
#print axioms DerivedCategory.toBoundedHeart_isEquivalence
#print axioms DerivedCategory.boundedHeartEquivalence
#print axioms DerivedCategory.boundedHeartEquivalence_functor
#print axioms DerivedCategory.toBoundedHeart_obj_obj_obj

/-! ## The derived functor of an exact functor on bounded objects (#1070, #1071)

For an exact functor that is bijective on every `Ext` group, `mapDerivedCategory`
is fully faithful on bounded objects and essentially surjective onto the bounded
objects with cohomology in the essential image. The hypothesis is carried
explicitly; no instance supplies it.
-/

#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_iff_of_iso_left
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_iff_of_iso_right
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_shift_iff
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_shift_left
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_of_forall_shift
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_obj₃_left
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_obj₃_right
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_obj₂_left
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_obj₂_right
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_single_of_neg
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_single_iff_mapExt_bijective
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_single
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_bounded_single
#print axioms CategoryTheory.Functor.mapDerivedCategory_map_bijective_of_bounded
#print axioms CategoryTheory.Functor.exists_bounded_iso_mapDerivedCategory_obj

/-! ## Bounded derived Hom-finiteness from heart Ext-finiteness (#1121)

`ExtFiniteBounded` is the explicit heart-level input. Its ordinary-Ext
constructor proves negative shifted Homs vanish from the canonical t-structure;
the two-variable dévissage then propagates finite-dimensionality and finite
support to all bounded derived objects. Nothing here supplies coherent-sheaf
Ext finiteness or a geometric vanishing bound.
-/

#print axioms Module.Finite.of_exact_middle
#print axioms DerivedCategory.ExtFiniteBounded
#print axioms DerivedCategory.ExtFiniteBounded.finite
#print axioms DerivedCategory.ExtFiniteBounded.support_finite
#print axioms DerivedCategory.ExtFiniteBounded.of_ext
#print axioms DerivedCategory.HomFiniteBoundedPair
#print axioms DerivedCategory.HomFiniteBoundedPair.finite
#print axioms DerivedCategory.HomFiniteBoundedPair.support_finite
#print axioms DerivedCategory.HomFiniteBoundedPair.of_iso
#print axioms DerivedCategory.HomFiniteBoundedPair.shift
#print axioms DerivedCategory.HomFiniteBoundedPair.obj₂_right
#print axioms DerivedCategory.HomFiniteBoundedPair.obj₂_left
#print axioms DerivedCategory.homFiniteBoundedPair_of_bounded
#print axioms DerivedCategory.homFiniteBounded_boundedDerived
