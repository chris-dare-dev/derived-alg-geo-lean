/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.Autoequivalence.Stability.ClassMap
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Symmetry.GLTilde.Action.Slicing
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Chambers
import DerivedAlgGeo.LinearAlgebra.QuadraticForm
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Mukai.Orientation
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.Integral
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Quadratic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Mukai.Chart

/-!
# Historical names for restating immutable reviews

The canonical declarations live in the Bridgeland strong-child namespace
`CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction`.
The aliases below are deliberately outside the `DerivedAlgGeo` library and are
imported only by the restatement executable. They let the exact, immutable
statement payloads in `attest/review.yaml` elaborate without exposing the
retired namespace to library consumers or the declaration emitter.

Do not import this module from library code, add aliases, or use these names in
new review payloads. Review-to-declaration joins survive renames by statement
digest; this bridge exists only because the stored pretty-printed statements
must still resolve the names that the reviewer originally read.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.GroupAction

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.GLTilde
  (since := "2026-08-30")]
alias GLTilde :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.GLTilde

namespace GLTilde

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.GLTilde.group
  (since := "2026-08-30")]
alias group :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.GLTilde.group

end GLTilde

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot
  (since := "2026-08-30")]
alias AutPairQuot :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot

namespace AutPairQuot

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot.group
  (since := "2026-08-30")]
alias group :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot.group

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot.mulAction
  (since := "2026-08-30")]
alias mulAction :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot.mulAction

end AutPairQuot

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.gltildeSlicingMulAction
  (since := "2026-08-30")]
alias gltildeSlicingMulAction :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.gltildeSlicingMulAction

end CategoryTheory.Triangulated.StabilityCondition.GroupAction

/-! ## MO1.03 carrier and locus cutover

These aliases preserve the spellings recorded before the positive-plane,
positive-frame, orthogonality, determinant-alignment, signed-ray, and
charge-zero owners were separated. They remain executable-only: new library
code must use the names on the right. -/

namespace PeriodDomain

@[deprecated orthogonalityLocus (since := "2026-09-14")]
alias wall := orthogonalityLocus
@[deprecated positivePlanes (since := "2026-09-14")]
alias periodDomain := positivePlanes
@[deprecated positivePlanesAway (since := "2026-09-14")]
alias periodDomain₀ := positivePlanesAway
@[deprecated positivePlanesAway_sphericalClasses_univ_eq_empty (since := "2026-09-14")]
alias periodDomain₀_sphericalClasses_univ_eq_empty :=
  positivePlanesAway_sphericalClasses_univ_eq_empty
@[deprecated mem_orthogonalityLocus_iff_mem_orthogonal (since := "2026-09-14")]
alias mem_wall_iff_mem_orthogonal := mem_orthogonalityLocus_iff_mem_orthogonal
@[deprecated positivePlanes_nonempty (since := "2026-09-14")]
alias periodDomain_nonempty := positivePlanes_nonempty
@[deprecated finite_orthogonalityLoci_through (since := "2026-09-14")]
alias finite_walls_through := finite_orthogonalityLoci_through

namespace PlaneRegion

@[deprecated orthogonalClasses (since := "2026-09-14")]
alias wallClasses := orthogonalClasses
@[deprecated isBounded_orthogonalClasses (since := "2026-09-14")]
alias isBounded_wallClasses := isBounded_orthogonalClasses
@[deprecated finite_orthogonalClasses_inter (since := "2026-09-14")]
alias finite_wallClasses_inter := finite_orthogonalClasses_inter

end PlaneRegion

@[deprecated IsPositiveFrame (since := "2026-09-14")]
alias IsPositivePair := IsPositiveFrame
@[deprecated isPositivePlane_framePlane (since := "2026-09-14")]
alias isPositivePlane_pairSpan := isPositivePlane_framePlane
@[deprecated positiveFramesPlus (since := "2026-09-14")]
alias periodDomainPlus := positiveFramesPlus
@[deprecated positiveFramesMinus (since := "2026-09-14")]
alias periodDomainMinus := positiveFramesMinus
@[deprecated disjoint_positiveFramesPlus_minus (since := "2026-09-14")]
alias disjoint_periodDomainPlus_minus := disjoint_positiveFramesPlus_minus
@[deprecated union_positiveFramesPlus_minus (since := "2026-09-14")]
alias union_periodDomainPlus_minus := union_positiveFramesPlus_minus
@[deprecated swap_mem_of_mem_positiveFramesPlus (since := "2026-09-14")]
alias swap_mem_of_mem_periodDomainPlus := swap_mem_of_mem_positiveFramesPlus
@[deprecated isPositiveFrame_iff (since := "2026-09-14")]
alias isPositivePair_iff := isPositiveFrame_iff
@[deprecated isOpen_setOf_isPositiveFrame (since := "2026-09-14")]
alias isOpen_setOf_isPositivePair := isOpen_setOf_isPositiveFrame
@[deprecated exists_isPositiveFrame (since := "2026-09-14")]
alias exists_isPositivePair := exists_isPositiveFrame
@[deprecated orthogonalityPairs (since := "2026-09-14")]
alias wallPairs := orthogonalityPairs
@[deprecated mem_orthogonalityPairs_iff (since := "2026-09-14")]
alias mem_wallPairs_iff := mem_orthogonalityPairs_iff
@[deprecated orthogonalityPairs_ne_top (since := "2026-09-14")]
alias wallPairs_ne_top := orthogonalityPairs_ne_top
@[deprecated dense_compl_orthogonalityPairs (since := "2026-09-14")]
alias dense_compl_wallPairs := dense_compl_orthogonalityPairs
@[deprecated nonempty_positivePlanesAway (since := "2026-09-14")]
alias nonempty_periodDomain₀ := nonempty_positivePlanesAway
@[deprecated isPositiveFrame_iff_forall_combination (since := "2026-09-14")]
alias isPositivePair_iff_forall_combination := isPositiveFrame_iff_forall_combination
@[deprecated isPositiveFrame_interp (since := "2026-09-14")]
alias isPositivePair_interp := isPositiveFrame_interp

end PeriodDomain

namespace Mukai

@[deprecated isPositiveFrame_exp (since := "2026-09-14")]
alias isPositivePair_exp := isPositiveFrame_exp
@[deprecated mem_positiveFramesPlus_exp (since := "2026-09-14")]
alias mem_periodDomainPlus_exp := mem_positiveFramesPlus_exp
@[deprecated mem_positiveFramesPlus_exp_of_sameCone (since := "2026-09-14")]
alias mem_periodDomainPlus_exp_of_sameCone := mem_positiveFramesPlus_exp_of_sameCone
@[deprecated mem_positiveFramesPlus_exp_of_sameCone_of_sigPos (since := "2026-09-14")]
alias mem_periodDomainPlus_exp_of_sameCone_of_sigPos :=
  mem_positiveFramesPlus_exp_of_sameCone_of_sigPos
@[deprecated finite_orthogonalClasses_integralExtension (since := "2026-09-14")]
alias finite_wallClasses_integralExtension := finite_orthogonalClasses_integralExtension
@[deprecated mem_orthogonalityLocus_iff_expCharge_eq_zero (since := "2026-09-14")]
alias mem_wall_iff_expCharge_eq_zero := mem_orthogonalityLocus_iff_expCharge_eq_zero
@[deprecated mem_positivePlanesAway_iff_expCharge_ne_zero (since := "2026-09-14")]
alias mem_periodDomain₀_iff_expCharge_ne_zero := mem_positivePlanesAway_iff_expCharge_ne_zero

end Mukai

namespace PeriodDomain

@[deprecated mem_orthogonalityLocus_iff_centralCharge_eq_zero (since := "2026-09-14")]
alias mem_wall_iff_centralCharge_eq_zero :=
  mem_orthogonalityLocus_iff_centralCharge_eq_zero
@[deprecated mem_positivePlanesAway_iff_centralCharge_ne_zero (since := "2026-09-14")]
alias mem_periodDomain₀_iff_centralCharge_ne_zero :=
  mem_positivePlanesAway_iff_centralCharge_ne_zero

end PeriodDomain

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily

@[deprecated alignmentValue (since := "2026-09-14")]
alias wallValue := alignmentValue
@[deprecated alignmentLocus (since := "2026-09-14")]
alias wall := alignmentLocus
@[deprecated mem_alignmentLocus (since := "2026-09-14")]
alias mem_wall := mem_alignmentLocus
@[deprecated alignmentValue_eq_neg_im_mul_conj (since := "2026-09-14")]
alias wallValue_eq_neg_im_mul_conj := alignmentValue_eq_neg_im_mul_conj
@[deprecated alignmentValue_self (since := "2026-09-14")]
alias wallValue_self := alignmentValue_self
@[deprecated alignmentLocus_self (since := "2026-09-14")]
alias wall_self := alignmentLocus_self
@[deprecated alignmentValue_swap (since := "2026-09-14")]
alias wallValue_swap := alignmentValue_swap
@[deprecated alignmentLocus_swap (since := "2026-09-14")]
alias wall_swap := alignmentLocus_swap
@[deprecated alignmentValue_zero_left (since := "2026-09-14")]
alias wallValue_zero_left := alignmentValue_zero_left
@[deprecated alignmentValue_zero_right (since := "2026-09-14")]
alias wallValue_zero_right := alignmentValue_zero_right
@[deprecated alignmentValue_add_left (since := "2026-09-14")]
alias wallValue_add_left := alignmentValue_add_left
@[deprecated alignmentValue_add_right (since := "2026-09-14")]
alias wallValue_add_right := alignmentValue_add_right
@[deprecated alignmentValue_neg_left (since := "2026-09-14")]
alias wallValue_neg_left := alignmentValue_neg_left
@[deprecated alignmentValue_neg_right (since := "2026-09-14")]
alias wallValue_neg_right := alignmentValue_neg_right
@[deprecated alignmentValue_zsmul_right (since := "2026-09-14")]
alias wallValue_zsmul_right := alignmentValue_zsmul_right
@[deprecated alignmentValue_add_zsmul_right (since := "2026-09-14")]
alias wallValue_add_zsmul_right := alignmentValue_add_zsmul_right
@[deprecated alignmentLocus_add_zsmul_right (since := "2026-09-14")]
alias wall_add_zsmul_right := alignmentLocus_add_zsmul_right
@[deprecated alignmentValue_add_nsmul_right (since := "2026-09-14")]
alias wallValue_add_nsmul_right := alignmentValue_add_nsmul_right
@[deprecated alignmentValue_linearAct (since := "2026-09-14")]
alias wallValue_linearAct := alignmentValue_linearAct
@[deprecated alignmentLocus_linearAct (since := "2026-09-14")]
alias wall_linearAct := alignmentLocus_linearAct
@[deprecated alignmentValue_smul (since := "2026-09-14")]
alias wallValue_smul := alignmentValue_smul
@[deprecated alignmentLocus_smul (since := "2026-09-14")]
alias wall_smul := alignmentLocus_smul
@[deprecated reindex_alignmentLocus (since := "2026-09-14")]
alias reindex_wall := reindex_alignmentLocus
@[deprecated pullback_alignmentValue (since := "2026-09-14")]
alias pullback_wallValue := pullback_alignmentValue
@[deprecated pullback_alignmentLocus (since := "2026-09-14")]
alias pullback_wall := pullback_alignmentLocus

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical

@[deprecated nonpositiveRayLocus (since := "2026-09-14")]
alias wall := nonpositiveRayLocus
@[deprecated mem_nonpositiveRayLocus_iff (since := "2026-09-14")]
alias mem_wall_iff := mem_nonpositiveRayLocus_iff
@[deprecated signedRayRegularLocus (since := "2026-09-14")]
alias chamber := signedRayRegularLocus
@[deprecated mem_signedRayRegularLocus_iff (since := "2026-09-14")]
alias mem_chamber_iff := mem_signedRayRegularLocus_iff
@[deprecated signedRayRegularLocus_antitone (since := "2026-09-14")]
alias chamber_antitone := signedRayRegularLocus_antitone
@[deprecated signedRayRegularLocus_eq_compl_iUnion (since := "2026-09-14")]
alias chamber_eq_compl_iUnion := signedRayRegularLocus_eq_compl_iUnion
@[deprecated mem_nonpositiveRayLocus_iff_of_isSpherical (since := "2026-09-14")]
alias mem_wall_iff_of_isSpherical := mem_nonpositiveRayLocus_iff_of_isSpherical
@[deprecated rayCandidates (since := "2026-09-14")]
alias wallCandidates := rayCandidates

namespace BoundedRegion

@[deprecated BoundedRegion.rayCandidates_subset (since := "2026-09-14")]
alias wallCandidates_subset := BoundedRegion.rayCandidates_subset
@[deprecated BoundedRegion.finite_rayCandidates (since := "2026-09-14")]
alias finite_wallCandidates := BoundedRegion.finite_rayCandidates

end BoundedRegion

@[deprecated signedRayRegularLocus_inter_carrier (since := "2026-09-14")]
alias chamber_inter_carrier := signedRayRegularLocus_inter_carrier
@[deprecated rayCandidates_subset_latticeSpherical (since := "2026-09-14")]
alias wallCandidates_subset_latticeSpherical := rayCandidates_subset_latticeSpherical
@[deprecated signedRayRegularLocus_inter_ofDivisorSpace (since := "2026-09-14")]
alias chamber_inter_ofDivisorSpace := signedRayRegularLocus_inter_ofDivisorSpace
@[deprecated finite_rayCandidates_ofDivisorSpace (since := "2026-09-14")]
alias finite_wallCandidates_ofDivisorSpace := finite_rayCandidates_ofDivisorSpace
@[deprecated mem_chartPlane_orthogonalityLocus_iff (since := "2026-09-14")]
alias mem_periodDomainWall_iff := mem_chartPlane_orthogonalityLocus_iff
@[deprecated mem_orthogonalityLocus_iff_mem_nonpositiveRayLocus (since := "2026-09-14")]
alias mem_periodDomainWall_iff_mem_wall :=
  mem_orthogonalityLocus_iff_mem_nonpositiveRayLocus
@[deprecated mem_nonpositiveRayLocus_of_mem_orthogonalityLocus (since := "2026-09-14")]
alias mem_wall_of_mem_periodDomainWall :=
  mem_nonpositiveRayLocus_of_mem_orthogonalityLocus
@[deprecated not_mem_orthogonalityLocus_of_mem_signedRayRegularLocus (since := "2026-09-14")]
alias not_mem_periodDomainWall_of_mem_chamber :=
  not_mem_orthogonalityLocus_of_mem_signedRayRegularLocus

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeZeroLocus
  (since := "2026-09-14")]
alias stabWall :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeZeroLocus
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.mem_chargeZeroLocus_iff
  (since := "2026-09-14")]
alias mem_stabWall_iff :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.mem_chargeZeroLocus_iff
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeRegularLocus
  (since := "2026-09-14")]
alias stabRegular :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeRegularLocus
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.mem_chargeRegularLocus_iff
  (since := "2026-09-14")]
alias mem_stabRegular_iff :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.mem_chargeRegularLocus_iff
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeRegularLocus_antitone
  (since := "2026-09-14")]
alias stabRegular_antitone :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeRegularLocus_antitone
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeRegularLocus_univ
  (since := "2026-09-14")]
alias stabRegular_univ :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeRegularLocus_univ
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeRegularLocus_eq_compl_iUnion
  (since := "2026-09-14")]
alias stabRegular_eq_compl_iUnion :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeRegularLocus_eq_compl_iUnion
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.combined_smul_mem_chargeZeroLocus_iff
  (since := "2026-09-14")]
alias combined_smul_mem_stabWall_iff :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.combined_smul_mem_chargeZeroLocus_iff
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.image_chargeZeroLocus_smul
  (since := "2026-09-14")]
alias image_stabWall_smul :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.image_chargeZeroLocus_smul
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.image_chargeZeroLocus_gltilde
  (since := "2026-09-14")]
alias image_stabWall_gltilde :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.image_chargeZeroLocus_gltilde
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.combined_smul_mem_chargeRegularLocus_iff
  (since := "2026-09-14")]
alias combined_smul_mem_stabRegular_iff :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.combined_smul_mem_chargeRegularLocus_iff
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.image_chargeRegularLocus_smul
  (since := "2026-09-14")]
alias image_stabRegular_smul :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.image_chargeRegularLocus_smul
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.ChargeChamber
  (since := "2026-09-14")]
alias StabChamber :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.ChargeChamber
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeChamberOf
  (since := "2026-09-14")]
alias chamberOf :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.chargeChamberOf
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.continuous_chargeAt_of_mem_range
  (since := "2026-09-14")]
alias continuous_chargeAt_of_mem_range :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.continuous_chargeAt_of_mem_range
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.continuous_chargeAt
  (since := "2026-09-14")]
alias continuous_chargeAt :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.continuous_chargeAt
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.isClosed_chargeZeroLocus
  (since := "2026-09-14")]
alias isClosed_stabWall :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.isClosed_chargeZeroLocus
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.isOpen_chargeRegularLocus
  (since := "2026-09-14")]
alias isOpen_stabRegular :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.isOpen_chargeRegularLocus
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.IsAutStable
  (since := "2026-09-14")]
alias IsAutStable :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.IsAutStable
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.isAutStable_univ
  (since := "2026-09-14")]
alias isAutStable_univ :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.isAutStable_univ

namespace IsAutStable

@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.IsAutStable.inter
  (since := "2026-09-14")]
alias inter :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.IsAutStable.inter
@[deprecated
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.IsAutStable.image_lam
  (since := "2026-09-14")]
alias image_lam :=
  CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.ChargeZero.IsAutStable.image_lam

end IsAutStable

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.StabWall

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

@[deprecated chargeRegularLocusMulAction (since := "2026-09-14")]
alias stabRegularMulAction := chargeRegularLocusMulAction
@[deprecated chargeRegularLocusContinuousConstSMul (since := "2026-09-14")]
alias stabRegularContinuousConstSMul := chargeRegularLocusContinuousConstSMul

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

@[deprecated mem_stChargeFamily_alignmentLocus (since := "2026-09-14")]
alias mem_stChargeFamily_wall := mem_stChargeFamily_alignmentLocus
@[deprecated stChargeFamily_alignmentValue (since := "2026-09-14")]
alias stChargeFamily_wallValue := stChargeFamily_alignmentValue

namespace Divisorial.OrthogonalSlice

@[deprecated alignmentLocus (since := "2026-09-14")]
alias wall := alignmentLocus
@[deprecated alignmentValue_eq (since := "2026-09-14")]
alias wallValue_eq := alignmentValue_eq
@[deprecated alignmentValue_ofST (since := "2026-09-14")]
alias wallValue_ofST := alignmentValue_ofST
@[deprecated alignmentLocus_ofST_circle_eq (since := "2026-09-14")]
alias wall_ofST_circle_eq := alignmentLocus_ofST_circle_eq
@[deprecated alignmentLocus_ofST_iff_circle (since := "2026-09-14")]
alias wall_ofST_iff_circle := alignmentLocus_ofST_iff_circle
@[deprecated alignmentLocus_ofST_line_eq (since := "2026-09-14")]
alias wall_ofST_line_eq := alignmentLocus_ofST_line_eq

end Divisorial.OrthogonalSlice

namespace Divisorial.ChargeCoordinates

@[deprecated stWallFamily_alignmentValue (since := "2026-09-14")]
alias stWallFamily_wallValue := stWallFamily_alignmentValue

end Divisorial.ChargeCoordinates

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
