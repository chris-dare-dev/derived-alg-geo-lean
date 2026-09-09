/-
NumericalDivisorialMukai slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability

/-! ## sqrt(td_X) read off a numerical realization, and Bridgeland's K3 charge

sqrtTodd supplies the abstract SqrtTodd datum from the sqrtToddComp of
Numerical/Mukai/SqrtTodd.lean rather than by hand. sqrtTodd_eq_k3 is the formal
content of sqrt(td) = 1 + [pt] on a K3; it rests on K3.sqrtToddComp_one and
K3.degree_sqrtToddComp_two, both already proved from IsK3, so nothing new is
assumed. mukaiVector_snd_snd_of_isK3 identifies the third coordinate with the
repository's existing K3.mukaiS = rank + integral of ch_2, and
mukaiVector_snd_snd_eq_mukaiSInt with the integer K3.mukaiSInt = chi - rank once
HRR is supplied; those two are what stop the library carrying two unrelated
notions of Mukai vector. mukaiCharge_of_isK3 is Bridgeland's charge as the
ordinary divisorial charge minus the rank.

NOT here: a numerical realization for the K3 model of Examples/Surface/K3.lean,
and any comparison between the real Mukai extension used here and the integral
Mukai.MukaiLattice of GrothendieckGroup/MukaiVector.lean. The latter needs a
realization of the integral lattice inside the real divisor space. -/

#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.mukaiCharge_of_isK3
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.mukaiVector_of_isK3
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.mukaiVector_snd_snd_eq_mukaiSInt
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.mukaiVector_snd_snd_of_isK3
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.sqrtTodd
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.sqrtTodd_divisor
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.sqrtTodd_eq_k3
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.sqrtTodd_number
