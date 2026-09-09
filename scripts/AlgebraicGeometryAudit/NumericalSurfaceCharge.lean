/-
NumericalSurfaceCharge slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.

Everything recorded here is arithmetic on numerical presentations: additive
maps into the reals or the complex numbers, real divisor spaces with a symmetric
bilinear form, rational graded rings, and their scalar extensions. NO stability
condition, heart, slicing, support property, Bogomolov inequality, or geometric
class map from a Grothendieck group is constructed or assumed anywhere in this
slice. The projective plane and smooth quadric are explicit numerical models,
not schemes.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface

/-! ## Arbitrary numerical B-fields

BField is an arbitrary rational codimension-one class with no positivity;
chBComp is the degree-wise expansion of ch^B = exp(-B) ch, with
ch_1^B = ch_1 - B ch_0 and ch_2^B = ch_2 - B ch_1 + (B^2/2) ch_0 proved as
component identities. chBComp_along_eq_chBetaComp identifies the notation
B = beta H with the pre-existing scalar twist. Rationality of B comes from the
rational intersection ring, not from the mathematics. -/

#print axioms AlgebraicGeometry.Numerical.BField
#print axioms AlgebraicGeometry.Numerical.BField.along
#print axioms AlgebraicGeometry.Numerical.BField.along_cls
#print axioms AlgebraicGeometry.Numerical.BField.cls
#print axioms AlgebraicGeometry.Numerical.BField.cls_mem
#print axioms AlgebraicGeometry.Numerical.BField.mk.inj
#print axioms AlgebraicGeometry.Numerical.BField.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Numerical.BField.pow_mem
#print axioms AlgebraicGeometry.Numerical.chBComp
#print axioms AlgebraicGeometry.Numerical.chBComp_add
#print axioms AlgebraicGeometry.Numerical.chBComp_along_eq_chBetaComp
#print axioms AlgebraicGeometry.Numerical.chBComp_eq
#print axioms AlgebraicGeometry.Numerical.chBComp_mem
#print axioms AlgebraicGeometry.Numerical.chBComp_one
#print axioms AlgebraicGeometry.Numerical.chBComp_two
#print axioms AlgebraicGeometry.Numerical.chBComp_zero
#print axioms AlgebraicGeometry.Numerical.twist_algebraMap_mul

/-! ## Compressed coordinates from a numerical presentation

ofNumericalData and ofNumericalDataB read the compressed coordinates off an
explicit NumericalVarietyData 2, a Polarization, and an arbitrary rational
BField. The along theorems show the general notation agrees with the
scalar-twist notation at B = beta H. No presentation is selected by instance.

These adapters are declared into the moved type's own namespace,
Wall.Divisorial.ChargeCoordinates, which is what keeps dot notation working on
the coordinates they produce; the placement rule permits a geometric file to
keep the interface's namespace for exactly that reason. Their module is still
under AlgebraicGeometry/, which is why they are audited in this lane. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.centralCharge_ofNumericalDataB_along_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.chTwoBHom
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.chTwoBHom_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.chTwoHom
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.chTwoHom_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.degreeBHom
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.degreeBHom_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.degreeHom
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.degreeHom_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalData
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalDataB
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalDataB_along_chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalDataB_along_degree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalDataB_chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalDataB_degree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalDataB_hyperplaneSquare
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalDataB_rank
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalData_chTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalData_degree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalData_hyperplaneSquare
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.ofNumericalData_rank
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.rankHom
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial.ChargeCoordinates.rankHom_apply

/-! ## Realizing a rational ring in a real divisor space

NumericalRealization sends the rational codimension-one piece of a
NumericalRingData 2 additively into a real DivisorSpace, respects rational
scalars through an explicit field rather than a rational module instance, and
matches multiplication-then-degree with the real intersection form.
chernCharacter is the induced full real Chern character, and
centralCharge_eq_ofNumericalDataB identifies the intrinsic charge with the
compressed numerical-ring charge for every rational B and real scale. -/

#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.centralCharge_eq_ofNumericalDataB
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.chOneClassHom
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.chernCharacter
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.chernCharacter_chOne
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.chernCharacter_chTwo
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.chernCharacter_rank
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.divisorClass
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.divisorSpace
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.intersection_eq
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.map_rat_smul
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.mk.inj
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.parameters
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.parameters_omega_square
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.parameters_pair_twist_chOne
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.realizeBField
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.realizePolarization
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.twist_chOne_eq
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.twist_chTwo_eq

/-! ## The canonical real scalar extension

RealDivisorClass S is the real tensor product of the rational codimension-one
piece, with the base-changed intersection form. extendDivisorClass is the unique
real-linear extension of a realization (extendDivisorClass_unique) and preserves
the whole real form (pair_extendDivisorClass). centralCharge_eq_realization says
arbitrary real B, omega at the ring level give the same charge after transport
to any concrete realization. No basis and no Picard-rank hypothesis appear. -/

#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.extendDivisorClass
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.extendDivisorClass_ofRational
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.extendDivisorClass_tmul
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.extendDivisorClass_unique
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.pair_extendDivisorClass
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.realizeParameters
#print axioms AlgebraicGeometry.Numerical.Surface.RationalDivisorClass
#print axioms AlgebraicGeometry.Numerical.Surface.RationalDivisorClass.intersection
#print axioms AlgebraicGeometry.Numerical.Surface.RationalDivisorClass.intersection_symm
#print axioms AlgebraicGeometry.Numerical.Surface.RealDivisorClass
#print axioms AlgebraicGeometry.Numerical.Surface.RealDivisorClass.divisorSpace
#print axioms AlgebraicGeometry.Numerical.Surface.RealDivisorClass.intersection
#print axioms AlgebraicGeometry.Numerical.Surface.RealDivisorClass.ofRational
#print axioms AlgebraicGeometry.Numerical.Surface.RealDivisorClass.pair_ofRational
#print axioms AlgebraicGeometry.Numerical.Surface.RealDivisorClass.pair_tmul
#print axioms AlgebraicGeometry.Numerical.Surface.ScalarExtension.centralCharge_eq_realization
#print axioms AlgebraicGeometry.Numerical.Surface.ScalarExtension.chernCharacter
#print axioms AlgebraicGeometry.Numerical.Surface.ScalarExtension.chernCharacter_chOne
#print axioms AlgebraicGeometry.Numerical.Surface.ScalarExtension.chernCharacter_chTwo
#print axioms AlgebraicGeometry.Numerical.Surface.ScalarExtension.chernCharacter_rank
#print axioms AlgebraicGeometry.Numerical.Surface.ScalarExtension.map_chernCharacter_chOne
#print axioms AlgebraicGeometry.Numerical.Surface.scalarExtensionRealization

/-! ## The (s,t) transport as a charge-family pullback

toNumClassHom bundles the degree-weighted transport additively and
wallChargeFamily pulls the generic (s,t) family back along it;
wallChargeFamily_wallValue is the established wallExpr. This is the H-slice:
c_1 is compressed to its H-degree. k3WallChargeFamily is the rank-one K3 model
in ORDINARY Chern coordinates, not the Mukai charge. -/

#print axioms AlgebraicGeometry.Numerical.Examples.k3WallChargeFamily
#print axioms AlgebraicGeometry.Numerical.Examples.k3WallChargeFamily_charge
#print axioms AlgebraicGeometry.Numerical.Surface.toNumClassHom
#print axioms AlgebraicGeometry.Numerical.Surface.toNumClassHom_apply
#print axioms AlgebraicGeometry.Numerical.Surface.wallChargeFamily
#print axioms AlgebraicGeometry.Numerical.Surface.wallChargeFamily_charge
#print axioms AlgebraicGeometry.Numerical.Surface.wallChargeFamily_wallValue

/-! ## The two branches of the wall hierarchy agree

For any NumericalRealization, wallChargeFamily_eq_rankOne_reindex proves that
the compressed (s,t) family IS the reindexing of the intrinsic divisorial family
along B = s H, omega = t H, and wallChargeFamily_wall_eq identifies the wall
loci. Without this the hierarchy was a forest with two formula owners (reZ and
imZ on one side, ChernCharacter.centralCharge on the other). -/

#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.pair_realizePolarization_chOne
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.pair_realizePolarization_self
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.rankOneParameters
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.rankOneParameters_B
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.rankOneParameters_omega
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.wallChargeFamily_charge_eq_centralCharge
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.wallChargeFamily_eq_rankOne_reindex
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.wallChargeFamily_wall_eq

/-! ## The projective plane as a rank-one child

P2ProjectiveCoordinates is a placeholder integral (r, c, v) carrier with the
SAME coordinates as SurfaceNum (ch_2 = c/2 + v on both); it is not Li's image
lattice. p2ProjectiveCharge_eq_surfaceCharge is the parent comparison theorem
applied to an identity-on-coordinates witness, and p2ProjectiveCharge_apply is
the exponential presentation -exp(-(b + i a) H) ch at H^2 = 1. Nothing here is
the Grothendieck group of the plane, a stability condition, a heart, or a
slicing. -/

#print axioms AlgebraicGeometry.Numerical.Examples.P2Divisor
#print axioms AlgebraicGeometry.Numerical.Examples.P2ProjectiveCoordinates
#print axioms AlgebraicGeometry.Numerical.Examples.p2BField
#print axioms AlgebraicGeometry.Numerical.Examples.p2BField_cls
#print axioms AlgebraicGeometry.Numerical.Examples.p2ChargePullback
#print axioms AlgebraicGeometry.Numerical.Examples.p2ChernCharacterPullback
#print axioms AlgebraicGeometry.Numerical.Examples.p2DivisorClass
#print axioms AlgebraicGeometry.Numerical.Examples.p2DivisorClass_intersection
#print axioms AlgebraicGeometry.Numerical.Examples.p2DivisorClass_map_rat_smul
#print axioms AlgebraicGeometry.Numerical.Examples.p2DivisorIndex
#print axioms AlgebraicGeometry.Numerical.Examples.p2DivisorSpace
#print axioms AlgebraicGeometry.Numerical.Examples.p2Hyperplane
#print axioms AlgebraicGeometry.Numerical.Examples.p2Hyperplane_square
#print axioms AlgebraicGeometry.Numerical.Examples.p2IntersectionForm
#print axioms AlgebraicGeometry.Numerical.Examples.p2NumericalRealization
#print axioms AlgebraicGeometry.Numerical.Examples.p2NumericalRealization_BField
#print axioms AlgebraicGeometry.Numerical.Examples.p2NumericalRealization_divisorSpace
#print axioms AlgebraicGeometry.Numerical.Examples.p2NumericalRealization_polarization
#print axioms AlgebraicGeometry.Numerical.Examples.p2Parameters
#print axioms AlgebraicGeometry.Numerical.Examples.p2Polarization
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveCharge
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveChargeCoordinates
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveChargeCoordinates_chTwo
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveChargeCoordinates_degree
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveChargeCoordinates_hyperplaneSquare
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveChargeCoordinates_rank
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveCharge_apply
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveCharge_eq_surfaceCharge
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveCharge_im
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveCharge_re
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveCharge_zero
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveChernCharacter
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveToSurface
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveWallFamily
#print axioms AlgebraicGeometry.Numerical.Examples.p2ProjectiveWallFamily_charge
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceCharge
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceChargeCoordinates
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceChargeCoordinates_chTwo
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceChargeCoordinates_degree
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceChargeCoordinates_hyperplaneSquare
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceChargeCoordinates_rank
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceCharge_eq_BFieldCharge
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceCharge_zero
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceChernCharacter
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceChernCharacter_chOne
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceChernCharacter_chTwo
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceChernCharacter_rank
#print axioms AlgebraicGeometry.Numerical.Examples.p2SurfaceCoordinatesPullback
#print axioms AlgebraicGeometry.Numerical.Examples.p2WallSlice
#print axioms AlgebraicGeometry.Numerical.Examples.surfacePieceOne_eq_span_H
#print axioms AlgebraicGeometry.Numerical.Examples.surfaceWeightOneBasis

/-! ## Numerical data of the smooth quadric

The rational ring Q[f1, f2]/(f1^2, f2^2) as iterated dual numbers with weights
0, 1, 1, 2, integral of f1 f2 equal to 1, Todd class (1 + f1)(1 + f2), integral
(r, c, d, v) classes with chi = r + c + d + v, and a proved HRR witness. The real
divisor realization in ruling coordinates recovers the form
(c, d).(c', d') = c d' + d c'. Ampleness is recorded as h1, h2 > 0 separately
from Polarization, whose only field is H^2 > 0. -/

#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.Divisor
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.NumericalClass
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.Ring
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.bField
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.basis
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.basis_mul_mem
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.basis_one
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.basis_three
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.basis_two
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.basis_zero
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.chComp
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.chComp_add
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.chComp_mem
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.ch_sum
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.chernCharacter
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.chernCharacter_chOne
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.chernCharacter_chTwo
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.chernCharacter_rank
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.chi
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.coordEquiv
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree_basis_of_ne
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree_mul
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree_one
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree_pointQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree_polarizationClass_sq
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree_rulingOneQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree_rulingTwoQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree_ruling_product
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.degree_segreQ_sq
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.divisorClass
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.divisorClass_intersection
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.divisorClass_map_rat_smul
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.divisorSpace
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.intersectionForm
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.intersectionForm_apply
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.numericalRealization
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.numericalRealization_bField
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.numericalRealization_polarization
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.numericalRealization_segre
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.numericalRing
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.numericalVariety
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.numericalVariety_satisfiesHRR
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.pieceOne_eq_span_rulings
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.pointQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.pointQ_mem
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.pointQ_mul_rulingOneQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.pointQ_mul_rulingTwoQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.pointQ_mul_self
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.pointQ_sq
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.polarization
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.polarizationClass
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.polarizationClass_mem
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingOne
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingOneQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingOneQ_mem
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingOneQ_mul_pointQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingOneQ_mul_rulingTwoQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingOneQ_mul_self
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingOneQ_sq
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingOne_pair_rulingTwo
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingOne_sq
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingTwo
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingTwoQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingTwoQ_mem
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingTwoQ_mul_pointQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingTwoQ_mul_rulingOneQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingTwoQ_mul_self
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingTwoQ_sq
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.rulingTwo_sq
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.segre
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.segrePolarization
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.segreQ
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.segreQ_eq
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.segreQ_mem
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.toddComp
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.toddComp_mem
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.todd_sum
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.weight
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.weightOneBasis
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.weight_le_two
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.weight_one
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.weight_three
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.weight_two
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.weight_zero

/-! ## The smooth quadric as a rank-two child

The divisorial charge in ruling coordinates, its scalar-extension and
rational-B compatibilities, the actual ample cone as a supplied set, and the
anti-diagonal slice H = f1 + f2, G(u) = u (f1 - f2) with H^2 = 2.
antiDiagonal_not_rankOne records that a scalar B = beta H misses these
directions. -/

#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.ampleCone
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.antiDiagonal
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.antiDiagonalMap
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.antiDiagonal_not_rankOne
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.centralCharge_apply
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.charge
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.charge_eq_numericalBField
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.charge_eq_scalarExtension
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.divisorialParameters
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.extendDivisorClass_surjective
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.omega_square
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.omega_square_pos
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.parameters
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.realize_scalarExtendedDivisor
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.realize_scalarExtendedParameters
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.scalarExtendedDivisor
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.scalarExtendedParameters
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.segre_pair_antiDiagonal
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.wallChargeFamily
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.wallChargeFamily_charge
#print axioms AlgebraicGeometry.Numerical.Examples.SmoothQuadric.wallSlice
