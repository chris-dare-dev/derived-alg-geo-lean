/-
Projective-variety slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Ample
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward
import DerivedAlgGeo.AlgebraicGeometry.Morphisms.Projective
import DerivedAlgGeo.AlgebraicGeometry.Morphisms.RelativelyAmple
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpace
import DerivedAlgGeo.AlgebraicGeometry.ProjectiveSpectrum.Modules.MapPullback
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective
open AlgebraicGeometry

-- The base field is the degree-zero part of the standard graded polynomial ring. The
-- identification is constructed from `C` and `constantCoeff`, so `Proj.toSpecZero`'s target can be
-- named as `Spec k` without a defeq coincidence.
#print axioms AlgebraicGeometry.homogeneousZeroRingEquiv
#print axioms AlgebraicGeometry.homogeneousZeroRingEquiv_apply_coe
#print axioms AlgebraicGeometry.isScalarTower_homogeneousZero
#print axioms AlgebraicGeometry.finiteType_homogeneousZero

-- Projective space and its structure morphism to the base field, with properness derived from
-- Mathlib's `IsProper (Proj.toSpecZero 𝒜)` rather than assumed.
#print axioms AlgebraicGeometry.projectiveSpace
#print axioms AlgebraicGeometry.projectiveSpaceToSpec
#print axioms AlgebraicGeometry.isProper_projectiveSpaceToSpec

-- A presentation is genuine projective data on one fixed variety; projectivity forgets the
-- chosen embedding, and properness follows from the resulting proposition.
#print axioms AlgebraicGeometry.ProjectivePresentation
#print axioms AlgebraicGeometry.ProjectivePresentation.instFiniteIndex
#print axioms AlgebraicGeometry.ProjectivePresentation.instIsClosedImmersionEmbedding
#print axioms AlgebraicGeometry.ProjectivePresentation.isProper_structureMorphism
#print axioms AlgebraicGeometry.Variety.IsProjective
#print axioms AlgebraicGeometry.Variety.IsProjective.ofPresentation
#print axioms AlgebraicGeometry.Variety.isProper_of_isProjective

-- The presentation's fields and elaborator artifacts. Listed rather than left to the ceiling:
-- the fields *are* the trust boundary here — `embedding`, `isClosedImmersion` and `overBase` are
-- what "projective" means in this repository — so they should be visible in the audit alongside
-- the theorems that consume them.
#print axioms AlgebraicGeometry.ProjectivePresentation.index
#print axioms AlgebraicGeometry.ProjectivePresentation.finiteIndex
#print axioms AlgebraicGeometry.ProjectivePresentation.embedding
#print axioms AlgebraicGeometry.ProjectivePresentation.isClosedImmersion
#print axioms AlgebraicGeometry.ProjectivePresentation.overBase
#print axioms AlgebraicGeometry.ProjectivePresentation.mk.inj
#print axioms AlgebraicGeometry.ProjectivePresentation.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Variety.IsProjective.presentation

-- Step 2 of #572, affine case: coherence survives pushforward along `Spec.map` of a surjection.
-- The tilde identification is the content; the finiteness is a tower argument.
#print axioms AlgebraicGeometry.gammaPushforwardIso
#print axioms AlgebraicGeometry.moduleFinite_gammaPushforward_of_finite
#print axioms AlgebraicGeometry.moduleFinite_gammaPushforward
#print axioms AlgebraicGeometry.isCoherent_pushforward_of_finite
#print axioms AlgebraicGeometry.isCoherent_pushforward_of_surjective

/-! ## Pushforward along an isomorphism (#572 step 2)

The transport that lets `isCoherent_pushforward_of_surjective`, stated about `Spec.map`,
reach a member of an affine open cover, which is an affine *scheme*.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.restrictEquiv
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrict
#print axioms AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_iso

/-! ## Coherent pushforward along a finite morphism (#572 step 2, generalised)

Coherence along a finite morphism, stated once for finite morphisms since a closed immersion is
finite, and the functor `Coh.pushforward : Coh X ⥤ Coh Y` with its exactness and additivity:
left exactness and additivity reflected through the fully faithful `Coh.ι`, right exactness from
affine-pushforward exactness on quasi-coherent sheaves.
-/

#print axioms AlgebraicGeometry.Scheme.isCoherent_pushforward_affine
#print axioms AlgebraicGeometry.Scheme.isCoherent_restrict_chart
#print axioms AlgebraicGeometry.Scheme.isCoherent_pushforward
#print axioms AlgebraicGeometry.Coh.pushforward
#print axioms AlgebraicGeometry.Coh.pushforwardCompι
#print axioms AlgebraicGeometry.Coh.pushforward_preservesFiniteLimits
#print axioms AlgebraicGeometry.Coh.pushforward_additive
#print axioms AlgebraicGeometry.Coh.pushforward_preservesEpimorphisms
#print axioms AlgebraicGeometry.Coh.pushforward_preservesFiniteColimits

/-! ## Base change of graded algebras and of `Proj`

The graded inclusion `a ↦ 1 ⊗ a` into the base change, the irrelevant-ideal hypotheses `Proj.map`
asks of it and of a bijective graded map, and homogeneous localization commuting with base change
without flatness. On `Proj`, the base-change square is cartesian (Stacks 01N2).
-/

#print axioms GradedRingHom.includeRight
#print axioms GradedRingHom.includeRight_apply
#print axioms GradedRingHom.irrelevant_baseChange_le_map
#print axioms GradedRingHom.symmOfBijective
#print axioms GradedRingHom.symmOfBijective_apply_apply
#print axioms GradedRingHom.apply_symmOfBijective_apply
#print axioms GradedRingHom.bijective_symmOfBijective
#print axioms GradedRingHom.irrelevant_le_map_of_bijective
#print axioms HomogeneousLocalization.Away.isPushout_baseChange
#print axioms AlgebraicGeometry.Proj.map_toSpecZero
#print axioms AlgebraicGeometry.Proj.map_toSpecZero_assoc
#print axioms AlgebraicGeometry.Proj.isIso_map_of_bijective
#print axioms AlgebraicGeometry.Proj.isPullback_map_baseChange

/-! ## Projective space over a base scheme

`ℙ(n; S) := S ×_ℤ Proj ℤ[n]` (Stacks 01NF), its structure morphism, properness for finite `n`,
base change in `S`, the comparison `ℙ(n; Spec R) ≅ Proj R[n]` with the field-level model, and the
twisting sheaves pulled back from `Proj ℤ[n]`.
-/

#print axioms AlgebraicGeometry.ProjectiveSpace
#print axioms AlgebraicGeometry.«termℙ(_;_)»
#print axioms AlgebraicGeometry.ProjectiveSpace.over
#print axioms AlgebraicGeometry.ProjectiveSpace.over_over
#print axioms AlgebraicGeometry.ProjectiveSpace.toProj
#print axioms AlgebraicGeometry.ProjectiveSpace.isProper
#print axioms AlgebraicGeometry.ProjectiveSpace.map
#print axioms AlgebraicGeometry.ProjectiveSpace.map_over
#print axioms AlgebraicGeometry.ProjectiveSpace.map_over_assoc
#print axioms AlgebraicGeometry.ProjectiveSpace.map_toProj
#print axioms AlgebraicGeometry.ProjectiveSpace.map_toProj_assoc
#print axioms AlgebraicGeometry.ProjectiveSpace.isPullback_map
#print axioms AlgebraicGeometry.ProjectiveSpace.SpecIso
#print axioms AlgebraicGeometry.ProjectiveSpace.SpecIso_hom_toSpecZero
#print axioms AlgebraicGeometry.ProjectiveSpace.SpecIso_hom_toSpecZero_assoc
#print axioms AlgebraicGeometry.ProjectiveSpace.SpecIso_hom_comp_projectiveSpaceToSpec
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSheaf
#print axioms AlgebraicGeometry.ProjectiveSpace.isInvertible_twistingSheaf
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSheafTensorIso
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSheafSpecIso

/-! ## Twisting sheaves along `Proj.map`

Degree-zero localizations along a graded ring map, the map `M̃ ⟶ (Proj.map ψ)_* Ñ` it induces, and
the adjoint comparison `θ : (Proj.map ψ)^* 𝒪(d) ⟶ 𝒪(d)` (Stacks 01MY), an isomorphism once the
source is generated in degree one.
-/

#print axioms GradedModule.localizedMapOfRingHom
#print axioms GradedModule.localizedMapOfRingHom_mk
#print axioms GradedModule.NumDenSameDeg.mapOfRingHom
#print axioms GradedModule.DegreeZeroLocalization.mapOfRingHom
#print axioms GradedModule.DegreeZeroLocalization.coe_mapOfRingHom
#print axioms GradedModule.DegreeZeroLocalization.mapOfRingHom_mk
#print axioms GradedModule.DegreeZeroLocalization.mapOfRingHom_smul
#print axioms AlgebraicGeometry.Proj.primeCompl_comap_le
#print axioms AlgebraicGeometry.Proj.fiberMapOfRingHom
#print axioms AlgebraicGeometry.Proj.sectionMapOfRingHom
#print axioms AlgebraicGeometry.Proj.sectionMapOfRingHom_apply
#print axioms AlgebraicGeometry.Proj.associatedPresheafMapOfRingHom
#print axioms AlgebraicGeometry.Proj.associatedSheafMapOfRingHom
#print axioms AlgebraicGeometry.Proj.associatedSheafMapOfRingHom_app
#print axioms AlgebraicGeometry.Proj.map_mem_intShift
#print axioms AlgebraicGeometry.Proj.twistingSheafMapOfRingHom
#print axioms AlgebraicGeometry.Proj.mapPullbackTwistingSheaf
#print axioms AlgebraicGeometry.Proj.mapPullbackTwistingSheaf_app_unit
#print axioms AlgebraicGeometry.Proj.isIso_mapPullbackTwistingSheaf
#print axioms AlgebraicGeometry.Proj.mapPullbackTwistingSheafIso
#print axioms AlgebraicGeometry.Proj.mapPullbackTwistingSheafIso_hom

/-! ## Ample invertible sheaves

The non-vanishing locus `X_s` of a section of an invertible sheaf, defined through stalks (Stacks
01CY) and pulled back to `Y_{f^* s}` (Stacks 0H78); ampleness (Stacks 01PS), stable under positive
tensor powers (Stacks 01PT) and pullback along affine morphisms, in particular to closed
subschemes (Stacks 01PU); the extension of sections from a basic open (Stacks 01PW); and
separatedness of a scheme with an ample sheaf.
-/
#print axioms AlgebraicGeometry.Scheme.Modules.IsAmple
#print axioms AlgebraicGeometry.Scheme.Modules.IsAmple.isSeparated
#print axioms AlgebraicGeometry.Scheme.Modules.IsAmple.of_iso
#print axioms AlgebraicGeometry.Scheme.Modules.IsAmple.pullback
#print axioms AlgebraicGeometry.Scheme.Modules.IsAmple.pullback_of_isClosedImmersion
#print axioms AlgebraicGeometry.Scheme.Modules.IsAmpleOn
#print axioms AlgebraicGeometry.Scheme.Modules.IsAmpleOn.of_iso
#print axioms AlgebraicGeometry.Scheme.Modules.IsAmpleOn.of_sections
#print axioms AlgebraicGeometry.Scheme.Modules.IsAmpleOn.pullback
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalBasis
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalBasis.bijective_stalk
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalBasis.coeff
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalBasis.coeff_smul
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalBasis.nonvanishingLocus_eq
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalBasis.res
#print axioms AlgebraicGeometry.Scheme.Modules.IsLocalBasis.smul_left_injective
#print axioms AlgebraicGeometry.Scheme.Modules.PicardClass.mk_tensorPow
#print axioms AlgebraicGeometry.Scheme.Modules.bijective_toSpanSingleton_extendScalars
#print axioms AlgebraicGeometry.Scheme.Modules.bijective_toSpanSingleton_of_span_eq_top
#print axioms AlgebraicGeometry.Scheme.Modules.bijective_toSpanSingleton_tmul
#print axioms AlgebraicGeometry.Scheme.Modules.exists_bijective_stalk
#print axioms AlgebraicGeometry.Scheme.Modules.exists_germ_eq
#print axioms AlgebraicGeometry.Scheme.Modules.exists_isLocalBasis
#print axioms AlgebraicGeometry.Scheme.Modules.exists_pow_smul_eq_res
#print axioms AlgebraicGeometry.Scheme.Modules.exists_res_eq_of_germ_eq
#print axioms AlgebraicGeometry.Scheme.Modules.extendScalars_tmul_smul
#print axioms AlgebraicGeometry.Scheme.Modules.fixedLeftTensorStalkIso_hom_app_germ_tmul
#print axioms AlgebraicGeometry.Scheme.Modules.germ
#print axioms AlgebraicGeometry.Scheme.Modules.germ_add
#print axioms AlgebraicGeometry.Scheme.Modules.germ_app
#print axioms AlgebraicGeometry.Scheme.Modules.germ_res
#print axioms AlgebraicGeometry.Scheme.Modules.germ_smul
#print axioms AlgebraicGeometry.Scheme.Modules.germ_zero
#print axioms AlgebraicGeometry.Scheme.Modules.isAmpleOn_of_forall_isAmpleOn_basicOpen
#print axioms AlgebraicGeometry.Scheme.Modules.isAmpleOn_tensorPow_iff
#print axioms AlgebraicGeometry.Scheme.Modules.isAmple_iff_isAmpleOn_top
#print axioms AlgebraicGeometry.Scheme.Modules.isAmple_restrict_iff
#print axioms AlgebraicGeometry.Scheme.Modules.isAmple_tensorPow_iff
#print axioms AlgebraicGeometry.Scheme.Modules.isInvertible_restrict
#print axioms AlgebraicGeometry.Scheme.Modules.isInvertible_tensorPow
#print axioms AlgebraicGeometry.Scheme.Modules.isInvertible_unit
#print axioms AlgebraicGeometry.Scheme.Modules.isLocalBasis_of_le_nonvanishingLocus
#print axioms AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iff
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_eq_basicOpen
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_le
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_map_eqToHom
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_one
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_pullbackSection
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_res
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_restrict
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_smul
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection
#print axioms AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackSection
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso
#print axioms AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback_hom_app_app
#print axioms AlgebraicGeometry.Scheme.Modules.restrictTensorPowIso
#print axioms AlgebraicGeometry.Scheme.Modules.section_ext
#print axioms AlgebraicGeometry.Scheme.Modules.span_germ_eq_top_iff_mem_basicOpen
#print axioms AlgebraicGeometry.Scheme.Modules.span_germ_eq_top_iff_mem_basicOpen_coeff
#print axioms AlgebraicGeometry.Scheme.Modules.span_germ_pullbackSection_eq_top_iff
#print axioms AlgebraicGeometry.Scheme.Modules.span_germ_tmulSection_eq_top_iff
#print axioms AlgebraicGeometry.Scheme.Modules.span_one_tmul_eq_top_iff
#print axioms AlgebraicGeometry.Scheme.Modules.span_singleton_eq_top_iff_isUnit
#print axioms AlgebraicGeometry.Scheme.Modules.span_singleton_map_equiv_eq_top_iff
#print axioms AlgebraicGeometry.Scheme.Modules.span_smul_eq_top_iff
#print axioms AlgebraicGeometry.Scheme.Modules.span_smul_eq_top_iff_isUnit
#print axioms AlgebraicGeometry.Scheme.Modules.span_tmul_eq_top_iff
#print axioms AlgebraicGeometry.Scheme.Modules.tensorPow
#print axioms AlgebraicGeometry.Scheme.Modules.tensorPowAddIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorPowCommIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorPowIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorPowMulIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorPowSection
#print axioms AlgebraicGeometry.Scheme.Modules.tensorPow_succ
#print axioms AlgebraicGeometry.Scheme.Modules.tensorPow_zero

/-! ## Relatively ample invertible sheaves

Relative ampleness (Stacks 01VH), its tensor powers (Stacks 02NN), the affine base (Stacks 01VK),
separatedness (Stacks 01VI), pullback along affine morphisms and closed immersions, and base change
(Stacks 0893).
-/
#print axioms AlgebraicGeometry.IsRelativelyAmple
#print axioms AlgebraicGeometry.IsRelativelyAmple.comp_of_isAffineHom
#print axioms AlgebraicGeometry.IsRelativelyAmple.isAmpleOn
#print axioms AlgebraicGeometry.IsRelativelyAmple.isSeparated
#print axioms AlgebraicGeometry.IsRelativelyAmple.of_isClosedImmersion
#print axioms AlgebraicGeometry.IsRelativelyAmple.of_isPullback
#print axioms AlgebraicGeometry.IsRelativelyAmple.of_iso
#print axioms AlgebraicGeometry.IsRelativelyAmple.pullback
#print axioms AlgebraicGeometry.IsRelativelyAmple.quasiCompact
#print axioms AlgebraicGeometry.isRelativelyAmple_iff_isAmple
#print axioms AlgebraicGeometry.isRelativelyAmple_iff_isAmpleOn
#print axioms AlgebraicGeometry.isRelativelyAmple_tensorPow_iff

/-! ## H-projective and locally projective morphisms

H-projective and locally projective morphisms (Stacks 01W8, 01WB), their properness (Stacks 01W9,
01WC) and base change (Stacks 01WF, 02V6); `X_{f/1} = D₊(f)` for the degree-one sections of `𝒪(1)`
on `Proj`; relative ampleness of `𝒪(1)` on `ℙ(n; S)` and of its restriction along a closed
immersion; and the comparison of `Variety.IsProjective` with H-projectivity.
-/
#print axioms AlgebraicGeometry.IsHProjective
#print axioms AlgebraicGeometry.IsHProjective.exists_closedImmersion
#print axioms AlgebraicGeometry.IsHProjective.isLocallyProjective
#print axioms AlgebraicGeometry.IsHProjective.isProper
#print axioms AlgebraicGeometry.IsHProjective.isStableUnderBaseChange
#print axioms AlgebraicGeometry.IsHProjective.morphismRestrict
#print axioms AlgebraicGeometry.IsLocallyProjective
#print axioms AlgebraicGeometry.IsLocallyProjective.exists_cover
#print axioms AlgebraicGeometry.IsLocallyProjective.isProper
#print axioms AlgebraicGeometry.IsLocallyProjective.isStableUnderBaseChange
#print axioms AlgebraicGeometry.Proj.basicOpen_fracSection
#print axioms AlgebraicGeometry.Proj.isLocalBasis_sectionOfMem_one
#print axioms AlgebraicGeometry.Proj.isUnit_frac_iff
#print axioms AlgebraicGeometry.Proj.isUnit_germ_iff
#print axioms AlgebraicGeometry.Proj.nonvanishingLocus_sectionOfMem_one
#print axioms AlgebraicGeometry.Proj.nonvanishingLocus_sectionOfMem_one_inf
#print axioms AlgebraicGeometry.Proj.nonvanishingLocus_sectionOfMem_one_of_le
#print axioms AlgebraicGeometry.ProjectiveSpace.isAffineOpen_preimage_inf_preimage
#print axioms AlgebraicGeometry.ProjectiveSpace.isRelativelyAmple_pullback_twistingSheaf_one
#print axioms AlgebraicGeometry.ProjectiveSpace.isRelativelyAmple_twistingSheaf_one
#print axioms AlgebraicGeometry.Variety.isProjective_iff_isHProjective
#print axioms AlgebraicGeometry.isHProjective_iff
#print axioms AlgebraicGeometry.isLocallyProjective_iff
