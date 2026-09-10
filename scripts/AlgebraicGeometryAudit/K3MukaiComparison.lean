/-
K3MukaiComparison slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface

/-! ## The integral and real Mukai structures of the K3 model agree

The degree-2d K3 model carried two Mukai structures with nothing relating them.
K3Mukai builds the INTEGRAL one on the lattice Z with form 2d.x.y;
RankOneRealization builds the REAL one on the divisor line R, which is where
every wall statement of Divisorial/Signature and Divisorial/Region lives.

Mukai/IntegralBridge had carried the general comparison for some time, waiting
on a lattice map respecting both forms. k3LatticeMap is that map -- the
inclusion of Z into R -- and k3LatticeMap_pairing is the hypothesis, which on
this model is a cast.

k3_mukaiVector_eq_extendMap is the identification that carries the rest: the
real Mukai vector of a numerical class IS the integral one, extended.
k3_isSphericalClass_of_isSpherical then turns integral sphericality into real
sphericality, the -2 reading the same on both sides because of the halving
convention in Mukai/RealForm.

k3_finite_integral_spherical_walls is the payoff: the wall finiteness over the
parameter box, said over Mukai.MukaiLattice Z rather than over the real
extension. The classes counted are those with self-pairing -2 in the INTEGRAL
lattice, which isSpherical_mukaiVector_iff reads off chi_2. Only d > 0 and
t0 > 0 are assumed; no Riemann--Roch input is added here.

Nothing identifies either carrier with K_num(X) for a geometric K3. -/

#print axioms AlgebraicGeometry.Numerical.Examples.extendMap_k3LatticeMap_injective
#print axioms AlgebraicGeometry.Numerical.Examples.k3LatticeMap
#print axioms AlgebraicGeometry.Numerical.Examples.k3LatticeMap_apply
#print axioms AlgebraicGeometry.Numerical.Examples.k3LatticeMap_pairing
#print axioms AlgebraicGeometry.Numerical.Examples.k3_extendMap_mem_integralExtension
#print axioms AlgebraicGeometry.Numerical.Examples.k3_finite_integral_spherical_walls
#print axioms AlgebraicGeometry.Numerical.Examples.k3_isSphericalClass_mukaiVector
#print axioms AlgebraicGeometry.Numerical.Examples.k3_isSphericalClass_of_isSpherical
#print axioms AlgebraicGeometry.Numerical.Examples.k3_mukaiVector_eq_extendMap
#print axioms AlgebraicGeometry.Numerical.Examples.k3_realPairing_extendMap
