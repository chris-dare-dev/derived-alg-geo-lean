/-
Transfer slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the
contract and reading guide.

Covers the transfer of pre-stability and stability conditions along a
phase-detecting functor (arXiv:2607.28411v1 Definitions 3.1 and 3.6, Remarks
3.2 and 3.7, Lemmas 3.5 and 3.9; arXiv:2601.22994 Definition 3.1 and Lemma
3.3), together with the support-property transfer, the twist, Bayer, and
metric layer, and Proposition 3.8's adjoint transposition into the Corollary
A.23 hypothesis, and Theorem 2.8(3)'s categorical core.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
open CategoryTheory.Triangulated

/-! ## Conservativity and order transfer from the lifting witness -/

#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.reflectsZeroObjects
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.not_isZero_obj
#print axioms CategoryTheory.Triangulated.Slicing.Precedes.preimage_of_preimageData
#print axioms CategoryTheory.Triangulated.Slicing.PrecedesWeak.preimage_of_preimageData
#print axioms CategoryTheory.Triangulated.slicingDist_preimage_le

/-! ## Pre-stability conditions along a phase-detecting functor -/

#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_slicing
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_Z
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_charge
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_phiPlus
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_phiMinus
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.pullback
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.pushforward

/-! ## Support property under transfer -/

#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_semistableClasses_subset
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.HasSupportProperty.preimage
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.QuadraticSupportData.preimage

/-! ## Local finiteness under transfer and stability conditions -/

#print axioms CategoryTheory.Triangulated.Slicing.preimage_intervalProp_iff
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.reflectsIsomorphisms
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.intervalFunctor
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.intervalFunctor_map_strictMono
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.strictImage
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.strictImage_strictMono
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.isStrictFiniteLengthObject_of_intervalFunctor_obj
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.isLocallyFinite
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage_toWithClassMap
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage_Z
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage_charge
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.pullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.pushforward

/-! ## Twists, the Bayer property, mass, and the metric under transfer -/

#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.mapEquiv
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.preimage_mapEquiv
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair.preimage
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair.preimage_Φ
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair.preimage_lam
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair.preimage_act
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.HasBayerProperty.preimage
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.BayerProperty.preimage
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_mapPreimage
#print axioms CategoryTheory.Triangulated.stabilityMass_preimage
#print axioms CategoryTheory.Triangulated.phiPlusDist_preimage
#print axioms CategoryTheory.Triangulated.phiMinusDist_preimage
#print axioms CategoryTheory.Triangulated.massDist_preimage
#print axioms CategoryTheory.Triangulated.stabilityDistTerm_preimage
#print axioms CategoryTheory.Triangulated.stabilityDist_preimage_le

/-! ## The adjoint transposition behind Proposition 3.8 -/

#print axioms CategoryTheory.Triangulated.Slicing.MapsSemistableLE
#print axioms CategoryTheory.Triangulated.Slicing.MapsSemistableGE
#print axioms CategoryTheory.Triangulated.Slicing.MapsSemistableLE.leProp_of_leProp
#print axioms CategoryTheory.Triangulated.Slicing.MapsSemistableGE.of_mapsSemistableLE

/-! ## Definition A.22: Ind-extensions of the dual t-structures of a slicing -/

#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.tStructure
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.indExtensionData
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.mk.inj
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.ofCompactGenerators
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.ofBrown
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.instHasInducedTStructure
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.isLE_zero_iff_geProp
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.isGE_one_iff_ltProp
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.tStructure_isBounded
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.le_zero_anti
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.MapsSemistableAisle
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.isLE_zero_of_semistable
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePhase
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePhase_iff_semistable
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePhase_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePhase_of_isZero
#print axioms CategoryTheory.Triangulated.Slicing.boundedAisle_shift
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.isLE_zero_shift
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.isGE_one_shift
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePhase_shift
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePhase_shift_int
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePhase_shift_iff
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.mapsSemistableAisle_of_coproduct

/-! ## Corollary A.23: the joint between Theorem A.17 and the phase truncation -/

#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.mapsSemistableGE_iff
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.monad_isLE_zero_of_geProp
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.monad_isRightTExact
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePreimagePhase
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePreimagePhase_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePreimage
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.largePreimage_P
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.tStructure
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.isBounded
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.le_zero_iff
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.ge_one_iff
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.mk.inj
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.hom_vanishing
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.ofIso
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.toInducedTStructures
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.InducedTStructuresLarge.ofInducedTStructures
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.nonempty_inducedTStructures
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.preimageData
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.nonempty_inducedTStructures_of_le
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.preimageData_of_le
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.nonempty_inducedTStructuresLarge
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.preimageData_of_coproduct_of_le
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.preimageData_of_coproduct
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.preimageData_of_mapsSemistableLE

/-! ## Theorem 2.8(3): semistability under base change -/

#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.isLE_zero_coproduct
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.isGE_one_coproduct
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.semistable_iff_largePhase_of_iso_coproduct
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.semistable_iff_semistable_of_iso_coproduct
#print axioms CategoryTheory.Triangulated.Slicing.IndExtensions.semistable_iff_preimage_of_coproduct
