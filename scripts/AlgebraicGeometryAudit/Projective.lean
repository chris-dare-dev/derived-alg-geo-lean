/-
Projective-variety slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Coherent.Pushforward
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
