/-
MukaiWitness slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.K3Mukai

/-! ## The Mukai data of the rank-one K3 model — the first inhabitants

MukaiVector.lean states in its own "What this file does not assert" section
that nothing constructs an IntegralMukaiData and nothing constructs an
AdditiveMukaiData. These are those constructions, so every consumer that took
one as a hypothesis is now a statement about an object that exists -- without a
line changing in any of them.

The Mukai-vector computations are EVALUATIONS on the model, not consequences of
Riemann-Roch, so they hold for every d including the degenerate d = 0. Only
mukaiPairing_k3 crosses to mukaiPairing and therefore spends SatisfiesHRR,
IsK3 and d /= 0. Carrying that hypothesis on the others would be a hypothesis
nothing uses.

isSpherical_structureSheaf_k3 and isIsotropic_point_k3 are the first
inhabitants of Mukai.IsSpherical and Mukai.IsIsotropic arising from a variety
rather than from a hand-built lattice vector. -/

#print axioms AlgebraicGeometry.Numerical.Examples.k3MukaiForm
#print axioms AlgebraicGeometry.Numerical.Examples.k3MukaiForm_apply
#print axioms AlgebraicGeometry.Numerical.Examples.k3IntegralMukaiData
#print axioms AlgebraicGeometry.Numerical.Examples.k3AdditiveMukaiData
#print axioms AlgebraicGeometry.Numerical.Examples.mukaiVector_k3
#print axioms AlgebraicGeometry.Numerical.Examples.pairing_mukaiVector_k3
#print axioms AlgebraicGeometry.Numerical.Examples.mukaiPairing_k3
#print axioms AlgebraicGeometry.Numerical.Examples.isSpherical_structureSheaf_k3
#print axioms AlgebraicGeometry.Numerical.Examples.isIsotropic_point_k3
