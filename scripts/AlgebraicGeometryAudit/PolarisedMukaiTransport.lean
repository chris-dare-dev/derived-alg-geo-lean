/-
Polarised-Mukai slice of the AlgebraicGeometry audit. The correction slot of the
polarised transport, inhabited at sqrt(td) and compared to the existing Mukai charge.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.PolarisedMukaiTransport

/-! ## The correction slot at sqrt(td)

PolarisedWallTransport carries kappa as a parameter and says kappa = 1 gives the
plain Chern character while kappa = sqrt(td) gives the Mukai vector. ONLY THE
FIRST HAD AN INHABITANT. corrComp_sqrtToddComp proved the CLASS MAP at sqrt(td)
is mukaiComp by rfl, but nothing tied the resulting CHARGE to the Mukai charge
already in the tree, so the kappa = sqrt(td) claim rested on a docstring.

wallChargeFamily_sqrtToddComp_eq_mukaiCharge is that comparison, proved for an
ARBITRARY SURFACE REALIZATION WITH NO K3 HYPOTHESIS. The K3 statement is the
corollary wallChargeFamily_sqrtToddComp_eq_mukaiCharge_k3, through
mukaiCharge_of_isK3, and it reads: on a K3 the sqrt(td) transport is the
ordinary divisorial charge MINUS THE RANK.

THE COMPARISON IS POINTWISE BY NECESSITY, NOT BY WEAKNESS OF PROOF. No equality
of ChargeFamily is statable: Polarised.wallChargeFamily is indexed by the
complex numbers and mukaiCharge by StabilityParameters, a pair of independent
divisor classes, and the carriers sit over different data bundles. The map
between the parameter spaces exists only on the rank-one slice B = sH, omega =
tH, which is rankOneParameters. The kappa = 1 case is stated the same way, at
wallChargeFamily_charge_eq_centralCharge.

realizePolarization is used throughout; no local duplicate of it appears here.
pair_realizePolarization_divisorClass generalizes the existing chOne case
because sqrt(td)_1 needs the same fact and is not a Chern component.

KAPPA = 1 AND KAPPA = SQRT(TD) ARE TWO PULLBACKS, NOT ONE FAMILY, and
wallChargeFamily_sqrtToddComp_sub_unitCorr_k3 is the proof: on a K3 they differ
by the rank, an additive term linear in the class, so their walls genuinely
differ. That statement needs NO realization -- both sides are built from V and P
-- and it uses exactly two K3 inputs, sqrtToddComp_one and
degree_sqrtToddComp_two.

SqrtTodd is the IMAGE of kappa under a realization, not a truncation of it. The
forgetful map is lossy on slot 0 and above slot 2; slot 0 reappears in
hDegrees_sqrtToddComp_eq_mukaiVector as the int H^2 weight and nowhere else.

No scheme, sheaf, heart, or stable object appears. -/

#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.pair_realizePolarization_divisorClass
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.pair_realizePolarization_add_smul
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.hDegrees_sqrtToddComp_eq_mukaiVector
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.wallChargeFamily_sqrtToddComp_eq_mukaiCharge
#print axioms AlgebraicGeometry.Numerical.Surface.NumericalRealization.wallChargeFamily_sqrtToddComp_eq_mukaiCharge_k3
#print axioms AlgebraicGeometry.Numerical.Surface.hDegrees_sqrtToddComp_k3
#print axioms AlgebraicGeometry.Numerical.Surface.wallChargeFamily_sqrtToddComp_sub_unitCorr_k3
