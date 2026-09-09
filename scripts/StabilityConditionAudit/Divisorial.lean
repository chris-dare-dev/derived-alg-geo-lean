/-
Divisorial slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.

This subtree is the uncompressed counterpart of Walls/Numerical/: the same
central-charge arithmetic, carried out on a real divisor space with a symmetric
intersection form instead of on three compressed real coordinates. It contains
NO scheme, sheaf, numerical intersection ring, heart, slicing, or stability
condition, and it proves neither a Bogomolov inequality nor a Hodge index
theorem; both of those are proposition-valued certificates supplied by the
caller. Its geometric adapters live under AlgebraicGeometry/Numerical/Stability/
and are audited in the AlgebraicGeometry lane.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls
open CategoryTheory.Triangulated

/-! ## Compressed charge coordinates

ChargeCoordinates holds only rank, the H-degree of ch_1^B, the integral of
ch_2^B, and H^2: the lossy rank-one view. centralCharge a is the polynomial
-ch_2^B + (a^2/2) H^2 ch_0 + i a H.ch_1^B with omega = a H, twistByScalar is the
scalar twist B = b H, and centralCharge_twistByScalar_apply is the identity with
the exponential presentation -exp(-(b + i a) H) ch. Pullback is a
coordinate-preserving additive map between two presentations; nothing asserts
that either is a K-group. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.centralCharge_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.centralCharge_twistByScalar_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.chTwo_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.degree_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.hyperplaneSquare_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.map
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.rank_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.Pullback.twistByScalar
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.centralCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.centralCharge_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.centralCharge_im
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.centralCharge_re
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.centralCharge_twistByScalar_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.centralCharge_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.degree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.hyperplaneSquare
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.rank
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.twistByScalar
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.twistByScalar_chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.twistByScalar_degree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.twistByScalar_hyperplaneSquare
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.twistByScalar_rank

/-! ## The intrinsic divisorial charge

DivisorSpace is a real vector space with a symmetric bilinear form: no basis, no
Picard-rank bound, no nondegeneracy, no signature. ChernCharacter keeps the full
first Chern class in that space rather than its degree against one class.
StabilityParameters are independent B and omega with no positivity;
DivisorialParameters attaches a supplied ample-cone predicate, and positive
square is deliberately NOT used as the definition of ampleness. centralCharge is
-ch_2^B + (omega^2/2) ch_0 + i omega.ch_1^B; centralCharge_apply is its untwisted
expansion and centralCharge_eq_realPairing its Mukai-pairing form, whose third
slot is ch_2 and NOT the Todd-corrected s = ch_2 + rank.
centralCharge_rankOne_eq recovers the compressed API on B = beta H,
omega = alpha H. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.centralCharge_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.chOne_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.chTwo_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.chargeCoordinates
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.coordinatesAt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.map
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.rank_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.Pullback.twist
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.centralCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.centralCharge_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.centralCharge_apply_twisted
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.centralCharge_eq_realPairing
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.centralCharge_rankOne_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.chOne
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.chargeCoordinates
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.chargeCoordinates_chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.chargeCoordinates_degree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.chargeCoordinates_hyperplaneSquare
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.chargeCoordinates_rank
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.coordinatesAt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.coordinatesAt_chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.coordinatesAt_degree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.coordinatesAt_hyperplaneSquare
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.coordinatesAt_rank
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.rank
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.toRealExtension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.toRealExtension_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.twist
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.twist_chOne
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.twist_chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.twist_rank
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.intersection
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.intersection_symm
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.pair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.pair_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.pair_comm
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorialParameters
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorialParameters.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorialParameters.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorialParameters.omega_ample
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorialParameters.toStabilityParameters
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.StabilityParameters
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.StabilityParameters.B
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.StabilityParameters.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.StabilityParameters.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.StabilityParameters.omega
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.StabilityParameters.orthogonalSlice
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.StabilityParameters.rankOne

/-! ## Wall families and orthogonal slices

fullChargeFamily is the arbitrary-(B, omega) child of Wall.ChargeFamily.
OrthogonalSlice parameterizes B = s H + G(u), omega = t H with an arbitrary real
transverse space U, and chargeFamily is literally a reindexing of the parent.
exists_fullOrthogonal_coordinates needs only H^2 nonzero. IsHodge and
IsGeometric are proposition-valued certificates NOT required to define the
charge family or its walls. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.chargeFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.chargeFamily_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.fullChargeFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.fullChargeFamily_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.B_pair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.B_square
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.H
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.IsGeometric
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.IsGeometric.H_ample
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.IsGeometric.toIsHodge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.IsHodge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.IsHodge.H_square_pos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.IsHodge.transverse_square_neg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.Point
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.Point.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.Point.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.Point.rankOne
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.Point.s
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.Point.t
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.Point.u
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.centralCharge_eq_formula
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.chargeFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.charge_im
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.charge_re
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.exists_fullOrthogonal_coordinates
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.fullOrthogonal
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.imFormula
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.mk.inj
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.omega_B
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.omega_pair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.omega_square
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.orthogonal
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.orthogonalSubspace
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.parameters
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.parameters_B
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.parameters_omega
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.rankOne
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.reFormula
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.transverse
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.wall
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.wallValue_eq

/-! ## Discriminants and the Hodge index certificate

discriminant is (ch_1)^2 - 2 ch_0 ch_2 with the square taken in the divisor
space, and discriminant_twist says it does not see B. barDiscriminant and
discriminantC are the two forms of Macri--Schmidt Definition 6.12;
omega_square_mul_discriminant_le_barDiscriminant is the step from Bogomolov's
Delta >= 0 to the (alpha, beta)-plane support form, under a Hodge index at
omega. DivisorSpace.HodgeIndex is the certificate H^2 > 0 together with
H^2 . x^2 <= (H . x)^2 for EVERY real class; it is not proved for any surface.
The rank-one slice is Hodge from H^2 > 0 alone. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.discr
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.barDiscriminant
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.barDiscriminant_nonneg_of_discriminant_nonneg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.barDiscriminant_rankOne
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.discriminant
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.discriminantC
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.discriminant_le_discriminantC
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.discriminant_twist
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.omega_square_mul_discriminant_le_barDiscriminant
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeIndex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeIndex.H_square_pos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeIndex.index_le
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeIndex.pair_self_neg_of_orthogonal
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.DivisorSpace.HodgeIndex.pair_self_nonpos_of_orthogonal
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.H_pair_B
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.IsHodge.index_le_B
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.isHodge_of_hodgeIndex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.rankOne_isHodge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.transverse_square_nonpos_of_hodgeIndex

/-! ## Every fixed-u slice is the (s,t) model

toNumClass is the degree-weighted triple (H^2 . rank, H . ch_1, ch_2), and
stCharge_toNumClass identifies the (s,t) charge of that triple with the
scalar-twisted charge. centralCharge_twist is exp(-B_0) exp(-B) =
exp(-(B_0+B)) on the charge, which lets a slice absorb its transverse direction
into the character. chargeFamily_reindex_ofST is the main statement: reindexing
the divisorial family to a fixed u IS the (s,t) model pulled back along that
triple, so the circle, line, disjointness and nesting theorems of
Walls/Numerical/ transport unchanged. discr_sliceCoordinates records that the
walls genuinely move with u, and barDiscriminant_parameters discharges the
0 <= discr hypothesis from supplied data. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.discr_toNumClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.stCharge_toNumClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.stWallFamily
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.stWallFamily_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.stWallFamily_wallValue
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.toNumClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.toNumClassHom
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.toNumClassHom_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.toNumClass_ch2
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.toNumClass_deg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.toNumClass_rk
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChernCharacter.centralCharge_twist
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.Point.ofST
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.barDiscriminant_parameters
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.chargeFamily_reindex_ofST
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.discr_sliceCoordinates
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.discr_sliceCoordinates_nonneg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.discr_toNumClass_sliceCoordinates_nonneg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.parameters_ofST
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.sliceCoordinates
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.sliceCoordinates_chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.sliceCoordinates_degree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.sliceCoordinates_hyperplaneSquare
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.sliceCoordinates_rank
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.wallValue_ofST
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.wall_ofST_circle_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.wall_ofST_iff_circle
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.OrthogonalSlice.wall_ofST_line_eq
