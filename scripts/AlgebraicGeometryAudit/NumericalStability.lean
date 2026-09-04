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
