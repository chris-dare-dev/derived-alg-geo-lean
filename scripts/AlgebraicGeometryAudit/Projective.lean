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
#print axioms AlgebraicGeometry.ProjectiveVariety
#print axioms AlgebraicGeometry.ProjectiveVariety.toVariety
#print axioms AlgebraicGeometry.ProjectiveVariety.instIsProjective
#print axioms AlgebraicGeometry.ProjectiveVariety.ofPresentation

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
#print axioms AlgebraicGeometry.moduleFinite_gammaPushforward
#print axioms AlgebraicGeometry.isCoherent_pushforward_of_surjective

-- The restriction square on opens (#572 step 2, base-change half).
#print axioms AlgebraicGeometry.restrictSquareOpensIso

-- The same square on MODULE sheaves, which is what #572 step 2 actually consumes: pushing forward
-- along f and restricting to U is restricting to f^-1 U and pushing forward along f | U.
--
-- isCoherent_iff_restrict_affineOpenCover asks for IsFinitePresentation of the restriction, and
-- that transfers along an isomorphism, so the OBJECT-level statement suffices. The functor-level
-- one is not built, and going through it is not merely more work: it means letting unification
-- discover the two site functors underneath Scheme.Modules.pushforward and restrictFunctor, which
-- runs whnf past 200000 heartbeats -- the same failure ChartExtension.lean records for
-- fromTildeGamma.
--
-- restrictSquareSections_smul is the equality of sheaf-of-rings data that the first version of
-- BaseChange.lean left open. Both sides' scalar actions unfold by rfl to actions through
-- Scheme.Hom.app; Scheme.Opens.ι_appIso removes the open immersion's appIso and is the one step
-- that is NOT definitional; Scheme.Modules.map_smul gives semilinearity over X's structure sheaf;
-- and morphismRestrict_app says the two structure-sheaf maps differ by exactly the transport
-- being compared, eqToHom direction included.
--
-- presheaf_map_square_eq is stated separately because in a clean context its rewrites fire, while
-- the naturality goal it discharges carries the instances-transparency defect and admits only
-- exact. It is applied at its four opens morphisms SPELLED OUT, and that is why this file needs no
-- maxHeartbeats raise: left as _, those morphisms are metavariables solved by unifying against the
-- defective goal, which costs over twenty times the default budget and buys nothing, since they are
-- determined and can be written down. The bump that a first attempt reached for meant the statement
-- was underspecified, not that the proof was hard.
#print axioms AlgebraicGeometry.restrictSquareSections
#print axioms AlgebraicGeometry.restrictSquareSectionsInv
#print axioms AlgebraicGeometry.restrictSquareSectionsInv_restrictSquareSections
#print axioms AlgebraicGeometry.restrictSquareSections_restrictSquareSectionsInv
#print axioms AlgebraicGeometry.restrictSquareSections_smul
#print axioms AlgebraicGeometry.Scheme.Modules.presheaf_map_square_eq
#print axioms AlgebraicGeometry.restrictSquareSectionsEquiv
#print axioms AlgebraicGeometry.pushforwardRestrictIso

/-! ## Pushforward along an isomorphism (#572 step 2)

The transport that lets `isCoherent_pushforward_of_surjective`, stated about `Spec.map`,
reach a member of an affine open cover, which is an affine *scheme*.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.restrictEquiv
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardIsoRestrict
#print axioms AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_iso

/-! ## Pushforward along a closed immersion (#572 step 2)

The globalisation itself: `isCoherent_pushforward`.
-/

#print axioms AlgebraicGeometry.Scheme.isCoherent_pushforward_affine
#print axioms AlgebraicGeometry.Scheme.isCoherent_restrict_chart
#print axioms AlgebraicGeometry.Scheme.isCoherent_pushforward
