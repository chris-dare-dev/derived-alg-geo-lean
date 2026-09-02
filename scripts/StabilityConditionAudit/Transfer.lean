/-
Transfer slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the
contract and reading guide.

Covers the transfer of pre-stability and stability conditions along a
phase-detecting functor (arXiv:2607.28411v1 Definitions 3.1 and 3.6, Remarks
3.2 and 3.7, Lemmas 3.5 and 3.9; arXiv:2601.22994 Definition 3.1 and Lemma
3.3), together with the support-property transfer.
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
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_P_iff
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_charge
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_phiPlus
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.preimage_phiMinus
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.pullback
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.pushforward

/-! ## Support property under transfer -/

#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.semistableClasses_preimage_subset
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.HasSupportProperty.preimage
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.QuadraticSupportData.preimage

/-! ## Local finiteness under transfer and stability conditions -/

#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.reflectsIsomorphisms
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.intervalProp_iff
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.intervalFunctor
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.intervalFunctor_map_strictMono
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.strictImage
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.strictImage_monotone
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.strictImage_strictMono
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.isStrictFiniteLengthObject
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.isLocallyFinite
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage_toWithClassMap
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage_Z
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.preimage_charge
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.pullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.pushforward
