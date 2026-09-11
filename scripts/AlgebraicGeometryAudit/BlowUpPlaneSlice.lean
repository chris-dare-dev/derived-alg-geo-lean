/-
BlowUpPlaneSlice slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface

/-! ## A nontrivial orthogonal slice, and the first IsGeometric witness

Walls/Divisorial/Slice attaches two certificates to an orthogonal slice:
IsHodge, which asks the distinguished direction to have positive square and
every nonzero transverse direction negative square, and IsGeometric, which adds
that the direction is ample. Before this the tree had two slices and one and a
half certificates: the rank-one slice has transverse space Fin 0 -> R, so it is
the classical (s,t) plane and rankOne_isHodge is VACUOUS in its second clause;
SmoothQuadricCharge.wallSlice has a line but no certificate; and IsGeometric had
NO WITNESS AT ALL, because no model exposed its ample cone as a subset of the
real divisor space.

antiCanonicalSlice is the first slice whose transverse space is a PLANE. -K has
square 7 and its orthogonal complement in the rank-three space is
3x_0 + x_1 + x_2 = 0, spanned by E_1 - E_2 and H - E_1 - 2E_2.
antiCanonicalSlice_isHodge is therefore not vacuous, and it is discharged by
hodgeDefinite, which this model PROVES rather than assumes;
transverseMap_injective is what turns u non-zero into transverse u non-zero.

ampleCone is a SUPPLIED SET, not a theorem about a surface. It is the real cone
matching the classical description for a two-point blow-up, and
mem_ampleCone_of_isAmpleCoefficients ties it to the rational IsAmpleCoefficients
the model already carried, so the file does not introduce a second unrelated
notion of ampleness. Nothing proves it IS the ample cone of a geometric surface;
IsGeometric asks only that the direction lie in the supplied set.

wall_ofST_iff_circle records that the circle description of walls fires on this
slice: for each fixed transverse parameter the wall is a circle or a line in the
(s,t) half-plane. On the rank-one slice that is one half-plane; here it is a
plane's worth. No scheme and no ample line bundle appear. -/

#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.ampleCone
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.antiCanonicalSlice
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.antiCanonicalSlice_H
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.antiCanonicalSlice_isGeometric
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.antiCanonicalSlice_isHodge
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.antiCanonical_mem_ampleCone
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.mem_ampleCone_iff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.mem_ampleCone_of_isAmpleCoefficients
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pair_antiCanonical_transverse
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.sliceChargeFamily
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.sliceChargeFamily_charge
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.transverseMap
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.transverseMap_apply
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.transverseMap_injective
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.wall_ofST_iff_circle
