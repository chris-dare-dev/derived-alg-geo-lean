/-
NumericalDivisorialWallCircle slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.

Everything here is arithmetic. The circle, line, disjointness and nesting facts
are NOT reproved: they are the theorems of Walls/Numerical/ about the three
real coordinates, reached because a fixed transverse parameter turns a
divisorial slice into exactly that model. No sheaf, no heart, no stability
condition, and no Bogomolov or Hodge index inequality is proved anywhere below.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability

/-! ## Compressed coordinates as a point of the (s,t) wall plane

toNumClass is the degree-weighted triple (H^2 . rank, H . ch_1, ch_2) of any
ChargeCoordinates, bundled additively as toNumClassHom. stCharge_toNumClass is
the identity making the whole (s,t) development available to any compressed
coordinates: the (s,t) charge of the triple is the scalar-twisted charge.
stWallFamily is the resulting pullback family, discr_toNumClass identifies the
wall-plane discriminant with the compressed one, and
toNumClass_eq_ofNumericalData records that the polarised-surface transport of
WallTransport.lean is this construction applied to the coordinates it reads. -/

#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.discr_toNumClass
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.stCharge_toNumClass
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.stWallFamily
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.stWallFamily_charge
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.stWallFamily_wallValue
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.toNumClass
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.toNumClassHom
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.toNumClassHom_apply
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.toNumClass_ch2
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.toNumClass_deg
#print axioms AlgebraicGeometry.Numerical.Surface.ChargeCoordinates.toNumClass_rk
#print axioms AlgebraicGeometry.Numerical.Surface.toNumClass_eq_ofNumericalData

/-! ## Twisting the character moves the B-field

centralCharge_twist is exp(-B_0) exp(-B) = exp(-(B_0+B)) read on the central
charge. It is what lets a slice absorb its transverse direction into the
character, and it is proved from the charge expansion, not assumed. -/

#print axioms AlgebraicGeometry.Numerical.Surface.ChernCharacter.centralCharge_twist

/-! ## A fixed transverse parameter gives an (s,t) half plane

sliceCoordinates is the G(u)-twisted character compressed at H; its degree
does not see G(u), because H . G(u) = 0, while its ch_2 and hence its
discriminant do (discr_sliceCoordinates), so the walls genuinely move with u.
chargeFamily_reindex_ofST is the main statement: reindexing the divisorial
family to a fixed u IS the (s,t) model pulled back along that triple. The three
wall_ofST_* theorems are the circle, cleared-form circle, and vertical-line
cases transported from Walls/Numerical/Basic.lean; nothing is reproved.
barDiscriminant_parameters computes the Macri--Schmidt bar-discriminant at a
slice point as t^2 times the slice discriminant, the s-dependence cancelling,
and the two nonneg theorems use it to discharge the 0 <= discr hypothesis of
the disjointness and nesting theorems from SUPPLIED Bogomolov and Hodge data. -/

#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.Point.ofST
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.barDiscriminant_parameters
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.chargeFamily_reindex_ofST
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.discr_sliceCoordinates
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.discr_sliceCoordinates_nonneg
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.discr_toNumClass_sliceCoordinates_nonneg
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.parameters_ofST
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.sliceCoordinates
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.sliceCoordinates_chTwo
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.sliceCoordinates_degree
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.sliceCoordinates_hyperplaneSquare
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.sliceCoordinates_rank
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.wallValue_ofST
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.wall_ofST_circle_eq
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.wall_ofST_iff_circle
#print axioms AlgebraicGeometry.Numerical.Surface.OrthogonalSlice.wall_ofST_line_eq
