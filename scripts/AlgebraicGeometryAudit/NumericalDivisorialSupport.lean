/-
NumericalDivisorialSupport slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability

/-! ## Bogomolov--Gieseker as the nonnegativity half of a support property

The support property needs two halves. Negativity on the kernel of the charge
is proved in Walls/Divisorial/Support.lean from a supplied HodgeDefinite.
Nonnegativity on the locus is Bogomolov--Gieseker, which this repository does
NOT prove: BogomolovGiesekerData is the supplied datum, and
discriminantC_nonneg_of_semistable only upgrades it through
discriminant_le_discriminantC, which needs C >= 0. Both support-property
records therefore carry two supplied hypotheses and assert nothing about
sheaves. hodgeIndexStatement_of_hodgeDefinite records that the strict
certificate sits above the numerical HodgeIndexStatement in the same
one-directional ladder. Nothing here says the charge is a Bridgeland stability
condition or that the semistable locus is the semistable set of a heart. -/

#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.discriminantC_nonneg_of_semistable
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.hasQuadraticSupportProperty_semistable
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.hasSupportProperty_semistable
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.hodgeIndexStatement_of_hodgeDefinite
