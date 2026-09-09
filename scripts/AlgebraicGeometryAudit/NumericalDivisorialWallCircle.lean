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

#print axioms AlgebraicGeometry.Numerical.Surface.toNumClass_eq_ofNumericalData

