/-
NumericalStability slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability

/-! ## Polarised numerical data — definitions only

A polarisation is explicit data hanging off `NumericalRingData`, never an
instance. `degree_pow_pos` is a supplied field standing for the ample-class fact
`∫H^n > 0`; nothing here proves it and nothing relates `Polarization` to
Mathlib's `IsAmple`.

NO inequality is proved or axiomatised in this lane. In particular
Bogomolov-Gieseker is absent, the Hodge index inequality is absent, and
`0 <= discrH` is neither stated nor assumed.

The two H-discriminants are DIFFERENT quantities and the audit records both:
`discDegH` is the integral of the discriminant twisted by `H^(n-2)`, while
`Surface.discrH` weights the rank slot by `∫H²` because the (s, t) charge
formula requires it. They agree only when `∫H² = 1`. -/

#print axioms AlgebraicGeometry.Numerical.Polarization
#print axioms AlgebraicGeometry.Numerical.Polarization.cls
#print axioms AlgebraicGeometry.Numerical.Polarization.cls_mem
#print axioms AlgebraicGeometry.Numerical.Polarization.degree_pow_pos
#print axioms AlgebraicGeometry.Numerical.Polarization.mk.inj
#print axioms AlgebraicGeometry.Numerical.Polarization.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Numerical.Polarization.pow_mem
#print axioms AlgebraicGeometry.Numerical.degH
#print axioms AlgebraicGeometry.Numerical.degH_add
#print axioms AlgebraicGeometry.Numerical.degHHom
#print axioms AlgebraicGeometry.Numerical.degHHom_apply
#print axioms AlgebraicGeometry.Numerical.slopeH
#print axioms AlgebraicGeometry.Numerical.slopeH_eq
#print axioms AlgebraicGeometry.Numerical.discDegH
#print axioms AlgebraicGeometry.Numerical.discDegH_mul_mem
#print axioms AlgebraicGeometry.Numerical.Surface.discDegH_eq
#print axioms AlgebraicGeometry.Numerical.Surface.discrH
#print axioms AlgebraicGeometry.Numerical.Surface.discrH_eq
#print axioms AlgebraicGeometry.Numerical.Examples.k3Polarization
#print axioms AlgebraicGeometry.Numerical.Examples.degH_k3

/-! ## Bogomolov-Gieseker and Hodge index — supplied, not proved

Both inequalities are FIELDS of supplied-data structures, not theorems. The
classical Bogomolov-Gieseker proof runs through restriction to curves
(Mehta-Ramanathan, Flenner, Langer) and the Hodge index theorem for surfaces
is absent; neither exists in this repository or in Mathlib at the pin.

`Semistable` is an OPAQUE predicate on `N`, never on an object of a category:
semistability quantifies over subsheaves and this layer has no subobjects.
No sheaf appears in this lane.

The rank-<=-1 Lemma 5.1 results below are conditional on the supplied datum.
They RELOCATE the gap #332 records rather than closing it. What is genuinely
new is that, given the hypothesis, the rank-<=-1 case needs no Ext and no
Serre duality -- mukaiSelfPairing_eq plus rank^2 <= 1 is the whole proof. The
|r| >= 2 case is NOT proved and belongs to #740.

HodgeIndexStatement is Prop-valued, so unlike BogomolovGiesekerData it
generates no mk.inj and no mk.sizeOf_spec. -/

#print axioms AlgebraicGeometry.Numerical.BogomolovGiesekerData
#print axioms AlgebraicGeometry.Numerical.BogomolovGiesekerData.Semistable
#print axioms AlgebraicGeometry.Numerical.BogomolovGiesekerData.nonneg
#print axioms AlgebraicGeometry.Numerical.BogomolovGiesekerData.mk.inj
#print axioms AlgebraicGeometry.Numerical.BogomolovGiesekerData.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Numerical.HodgeIndexStatement
#print axioms AlgebraicGeometry.Numerical.HodgeIndexStatement.index_le
#print axioms AlgebraicGeometry.Numerical.Surface.nonneg_degree_discriminant
#print axioms AlgebraicGeometry.Numerical.Surface.discrH_nonneg
#print axioms AlgebraicGeometry.Numerical.K3.chi₂_self_le
#print axioms AlgebraicGeometry.Numerical.K3.mukaiSelfPairing_ge
#print axioms AlgebraicGeometry.Numerical.K3.neg_two_le_mukaiSelfPairing_of_rank_le_one
#print axioms AlgebraicGeometry.Numerical.K3.chi₂_self_le_two_of_rank_le_one
#print axioms AlgebraicGeometry.Numerical.K3.neg_two_le_selfPairing_mukaiVector_of_rank_le_one
#print axioms AlgebraicGeometry.Numerical.Examples.k3HodgeIndex
#print axioms AlgebraicGeometry.Numerical.Examples.k3BogomolovSanity
