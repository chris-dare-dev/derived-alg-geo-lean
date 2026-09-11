/-
Serre-functor and paper-object slice of the StabilityCondition audit.  These
are generic linear/triangulated category interfaces; the Enriques geometric
specialization is audited separately in AlgebraicGeometryAudit/Core.lean.

The classification structures are SUPPLIED DATA.  Ext-profile constructors
and their bidirectional transport under a Serre-compatible equivalence are
proved here.  A clean axiom list says that their formal consequences use no
hidden axioms; it does not construct the geometric Ext calculations assumed
by the two papers.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SerreFunctor

#print axioms ModuleCat.linearDualFunctor
#print axioms CategoryTheory.SerreFunctor.HomFinite
#print axioms CategoryTheory.SerreFunctor.HomFinite.finite
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.S
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.eta
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.naturality_left
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.naturality_right
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.mk.inj
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.mk.sizeOf_spec
#print axioms CategoryTheory.SerreFunctor.HasRightSerreFunctor
#print axioms CategoryTheory.SerreFunctor.SerreCategoryData
#print axioms CategoryTheory.SerreFunctor.SerreCategoryData.serre
#print axioms CategoryTheory.SerreFunctor.SerreCategoryData.serreIsEquivalence
#print axioms CategoryTheory.SerreFunctor.SerreCategoryData.mk.inj
#print axioms CategoryTheory.SerreFunctor.SerreCategoryData.mk.sizeOf_spec
#print axioms CategoryTheory.SerreFunctor.SerreCategoryData.hasSerreEquivalence
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.pairing
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.pairing_apply
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.pairing_separating_left
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.pairing_separating_right
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.finrank_hom_eq
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.trace
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.trace_apply
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.trace_comp

#print axioms CategoryTheory.SerreFunctor.IsSphericalObject
#print axioms CategoryTheory.SerreFunctor.IsSphericalObject.vanishing
#print axioms CategoryTheory.SerreFunctor.IsSphericalObject.end_one
#print axioms CategoryTheory.SerreFunctor.IsSphericalObject.top_one
#print axioms CategoryTheory.SerreFunctor.IsSphericalObject.serre_shift
#print axioms CategoryTheory.SerreFunctor.IsSphericalObject.not_isZero
#print axioms CategoryTheory.SerreFunctor.IsSphericalObject.finrank_end
#print axioms CategoryTheory.SerreFunctor.IsSphericalObject.finrank_top
#print axioms CategoryTheory.SerreFunctor.IsSphericalObject.finrank_hom_eq_zero
#print axioms CategoryTheory.SerreFunctor.IsSphericalObject.of_iso
#print axioms CategoryTheory.SerreFunctor.IsPseudoprojectiveObject
#print axioms CategoryTheory.SerreFunctor.IsPseudoprojectiveObject.inRange_one
#print axioms CategoryTheory.SerreFunctor.IsPseudoprojectiveObject.vanishing
#print axioms CategoryTheory.SerreFunctor.IsPseudoprojectiveObject.serre_shift
#print axioms CategoryTheory.SerreFunctor.IsPseudoprojectiveObject.not_isZero
#print axioms CategoryTheory.SerreFunctor.IsPseudoprojectiveObject.finrank_inRange
#print axioms CategoryTheory.SerreFunctor.IsPseudoprojectiveObject.finrank_hom_eq_zero
#print axioms CategoryTheory.SerreFunctor.IsPseudoprojectiveObject.of_iso
#print axioms CategoryTheory.SerreFunctor.IsPseudoprojectiveObject.not_isSphericalObject
#print axioms CategoryTheory.SerreFunctor.isSphericalObject_one_iff_isPseudoprojectiveObject_one

#print axioms CategoryTheory.SerreFunctor.EnriquesCategoryData
#print axioms CategoryTheory.SerreFunctor.EnriquesCategoryData.toSerreCategoryData
#print axioms CategoryTheory.SerreFunctor.EnriquesCategoryData.squareShift
#print axioms CategoryTheory.SerreFunctor.EnriquesCategoryData.mk.inj
#print axioms CategoryTheory.SerreFunctor.EnriquesCategoryData.mk.sizeOf_spec
#print axioms CategoryTheory.SerreFunctor.TwoEnriquesCategoryData
#print axioms CategoryTheory.SerreFunctor.EnriquesCategoryData.dimension
#print axioms CategoryTheory.SerreFunctor.EnriquesCategoryData.serreSquareIso
#print axioms CategoryTheory.SerreFunctor.EnriquesCategoryData.serreSquareObjIso
#print axioms CategoryTheory.SerreFunctor.EnriquesCategoryData.hasSerreEquivalence
#print axioms CategoryTheory.SerreFunctor.no_exceptional_of_serre_iso_shift

#print axioms CategoryTheory.SerreFunctor.IsShiftOf
#print axioms CategoryTheory.SerreFunctor.IsShiftOf.refl
#print axioms CategoryTheory.SerreFunctor.IsShiftOf.symm
#print axioms CategoryTheory.SerreFunctor.IsShiftOf.trans
#print axioms CategoryTheory.SerreFunctor.IsShiftOf.of_iso_left
#print axioms CategoryTheory.SerreFunctor.IsShiftOf.of_iso_right
#print axioms CategoryTheory.SerreFunctor.IsGradedOrthogonal
#print axioms CategoryTheory.SerreFunctor.not_isShiftOf_of_isGradedOrthogonal
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.candidate
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.candidate_spherical
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.pairwise_orthogonal
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.complete
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.mk.inj
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.mk.sizeOf_spec
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.candidate_not_isShiftOf
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.exists_candidate_shift
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.blockLength
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.candidate
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.spherical_of_length_one
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.pseudoprojective_of_two_le
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.pairwise_orthogonal
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.spherical_complete
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.pseudoprojective_complete
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.mk.inj
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.mk.sizeOf_spec
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.candidate_spherical
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.candidate_pseudoprojective
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.spherical_candidate_not_isShiftOf
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.pseudoprojective_candidate_not_isShiftOf
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.spherical_iff
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.pseudoprojective_iff

-- Completeness and separation make the candidate matching across a
-- Serre-compatible equivalence canonical.  The inverse classification proves
-- bijectivity; the mixed version also preserves singleton/longer block kind.
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.matchIndex
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.matchIndex_spec
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.matchIndex_injective
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.reverse_matchIndex_injective
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.matchingEquiv
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.matchingEquiv_apply
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.matchingEquiv_spec
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchIndex
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchIndex_length_eq_one
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchIndex_length_two_le
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchIndex_spec
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchIndex_injective
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchingEquiv
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchingEquiv_apply
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchingEquiv_length_eq_one_iff
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchingEquiv_length_two_le_iff
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.matchingEquiv_spec

-- Classification constructors whose candidates are the actual right
-- projections of first objects of orthogonal exceptional blocks.
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.ofResidualProjections
#print axioms CategoryTheory.SerreFunctor.SphericalClassificationData.ofResidualProjections_candidate
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.ofResidualProjections
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.ofResidualProjections_blockLength
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.ofResidualProjections_candidate
#print axioms CategoryTheory.SerreFunctor.MixedClassificationData.residualProjection_candidate_dichotomy

-- Ext computations are kept separate from the Serre-shift input.  A
-- Serre-compatible equivalence carries comparison data in both directions,
-- so spherical and pseudoprojective status is preserved and reflected.
#print axioms CategoryTheory.SerreFunctor.SphericalExtProfile
#print axioms CategoryTheory.SerreFunctor.SphericalExtProfile.vanishing
#print axioms CategoryTheory.SerreFunctor.SphericalExtProfile.end_one
#print axioms CategoryTheory.SerreFunctor.SphericalExtProfile.top_one
#print axioms CategoryTheory.SerreFunctor.SphericalExtProfile.toIsSphericalObject
#print axioms CategoryTheory.SerreFunctor.SphericalExtProfile.map
#print axioms CategoryTheory.SerreFunctor.PseudoprojectiveExtProfile
#print axioms CategoryTheory.SerreFunctor.PseudoprojectiveExtProfile.inRange_one
#print axioms CategoryTheory.SerreFunctor.PseudoprojectiveExtProfile.vanishing
#print axioms CategoryTheory.SerreFunctor.PseudoprojectiveExtProfile.toIsPseudoprojectiveObject
#print axioms CategoryTheory.SerreFunctor.PseudoprojectiveExtProfile.map
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.equiv
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.functorAdditive
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.functorLinear
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.functorCommShift
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.serreIso
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.inverseAdditive
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.inverseLinear
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.inverseCommShift
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.inverseSerreIso
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.mk.inj
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.mk.sizeOf_spec
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.symm
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.mapSpherical
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.mapPseudoprojective
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.spherical_iff
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.pseudoprojective_iff
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.mapIsShiftOf
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.isShiftOf_iff
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.mapIsGradedOrthogonal
#print axioms CategoryTheory.SerreFunctor.SerreCompatibleEquivalence.isGradedOrthogonal_iff

/-! ## Uniqueness of the Serre functor (#896)

Any two Serre functors on the same k-linear category are naturally isomorphic, and the isomorphism
compatible with both duality isomorphisms is unique. The argument is Yoneda.

THE REPRESENTABILITY STEP IS PUBLIC API, not a private step: `isoOfLinearYonedaIso` is stated on
`linearYoneda` alone and proved without reference to `SerreFunctorData`, because a downstream lane
needs it on a functor that is not a Serre functor. It is `Functor.preimageIso` against Mathlib's
`full_linearYoneda` and `faithful_linearYoneda`, so representability is not hand-rolled.

TRAP, recorded in the module docstring: WHICH VARIABLE the Yoneda argument runs in. Hom is
contravariant in the first and covariant in the second variable, and the dual flips both, so
`Dual (A ⟶ B)` is covariant in A and contravariant in B, matching `Hom(B, S A)`. The argument runs
in B with A fixed, which is why the functor is `linearYoneda` and NOT `linearCoyoneda` -- in this
repository `(linearCoyoneda k C).obj (op X)` is the COVARIANT Hom(X, -), and running the argument
there yields a statement that typechecks against the opposite functor and proves nothing about S.

The two naturalities come from two different fields for two different reasons: `yonedaIso` is
natural in B by `naturality_right`, and `uniqueIso` is natural in A by `naturality_left`. -/

#print axioms CategoryTheory.SerreFunctor.isoOfLinearYonedaIso
#print axioms CategoryTheory.SerreFunctor.map_isoOfLinearYonedaIso
#print axioms CategoryTheory.SerreFunctor.hom_ext_of_linearYoneda
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.compareEquiv
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.compareEquiv_apply
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.compareEquiv_naturality_right
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.yonedaIso
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIsoApp
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.comp_uniqueIsoApp_hom
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIsoApp_hom_eq
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIsoApp_naturality
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIso
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIso_hom_app
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIso_compat
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIso_unique
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIso_refl
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIso_trans
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.uniqueIso_symm
#print axioms CategoryTheory.SerreFunctor.SerreFunctorData.exists_uniqueIso
