/-
NumericalThreefoldWallTransport slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability

/-! ## Transporting a polarised threefold class to the (alpha, beta) plane

toNumClass is the four H-degrees of a NumericalVarietyData 3 against a
Polarization, with the rank slot weighted by H^3; toNumClassHom bundles it
additively and wallChargeFamily pulls the generic threefold child back along it.

degH1Beta_eq, degH2Beta_eq and deg3Beta_eq expand the truncated exponential in
codimensions one, two and three; they are the only real computation in the
module. betaTwist_toNumClass is what they are for: the four-coordinate twist of
Walls/Threefold/ agrees with the twisted degrees BMT.lean reads off chBetaComp.
Q_toNumClass and nu_toNumClass then identify the compressed Bayer--Macri--Toda
quantity and tilt slope with the ones BMT.lean already defines, so the library
has one Q rather than two.

Q_toNumClass_nonneg TRANSPORTS the conjecture and does not prove it. BMTData is
supplied data that is false for some threefolds; nothing here makes it more
true than it was. -/

#print axioms AlgebraicGeometry.Numerical.Threefold.Q_toNumClass
#print axioms AlgebraicGeometry.Numerical.Threefold.Q_toNumClass_nonneg
#print axioms AlgebraicGeometry.Numerical.Threefold.betaTwist_toNumClass
#print axioms AlgebraicGeometry.Numerical.Threefold.deg3Beta_eq
#print axioms AlgebraicGeometry.Numerical.Threefold.degH1Beta_eq
#print axioms AlgebraicGeometry.Numerical.Threefold.degH2Beta_eq
#print axioms AlgebraicGeometry.Numerical.Threefold.discr_betaTwist_toNumClass
#print axioms AlgebraicGeometry.Numerical.Threefold.nu_toNumClass
#print axioms AlgebraicGeometry.Numerical.Threefold.toNumClass
#print axioms AlgebraicGeometry.Numerical.Threefold.toNumClassHom
#print axioms AlgebraicGeometry.Numerical.Threefold.toNumClassHom_apply
#print axioms AlgebraicGeometry.Numerical.Threefold.toNumClass_add
#print axioms AlgebraicGeometry.Numerical.Threefold.toNumClass_deg0
#print axioms AlgebraicGeometry.Numerical.Threefold.toNumClass_deg1
#print axioms AlgebraicGeometry.Numerical.Threefold.toNumClass_deg2
#print axioms AlgebraicGeometry.Numerical.Threefold.toNumClass_deg3
#print axioms AlgebraicGeometry.Numerical.Threefold.wallChargeFamily
#print axioms AlgebraicGeometry.Numerical.Threefold.wallChargeFamily_charge
