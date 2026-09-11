/-
Bilinear-HRR slice of the AlgebraicGeometry audit, split out so concurrent branches append to
different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.AlgebraicGeometry.Surface.SphericalMukai

/-! ## `EulerRealization` from a named bilinear-HRR statement (#910)

`BilinearRiemannRochStatement` is supplied, not proved: its `chi₂_eq` field is bilinear
Hirzebruch--Riemann--Roch on pairs concentrated in degrees `0`--`2`, with the amplitude condition
a per-pair hypothesis rather than a field (as a field it is refutable). `toEulerRealization` is
its restriction to the diagonal along spherical objects; `euler` is the two-variable `selfEuler`,
and the diagonal identity is `rfl`. -/

#print axioms AlgebraicGeometry.K3Surface.euler
#print axioms AlgebraicGeometry.K3Surface.selfEuler_eq_euler_self
#print axioms AlgebraicGeometry.K3Surface.BilinearRiemannRochStatement
#print axioms AlgebraicGeometry.K3Surface.BilinearRiemannRochStatement.cls
#print axioms AlgebraicGeometry.K3Surface.BilinearRiemannRochStatement.chi₂_eq
#print axioms AlgebraicGeometry.K3Surface.BilinearRiemannRochStatement.mk.inj
#print axioms AlgebraicGeometry.K3Surface.BilinearRiemannRochStatement.mk.sizeOf_spec
#print axioms AlgebraicGeometry.K3Surface.BilinearRiemannRochStatement.toEulerRealization
#print axioms AlgebraicGeometry.K3Surface.SphericalExtProfile.isSpherical_mukaiVector_of_statement
