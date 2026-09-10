/-
BlowUpPlane slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface

/-! ## The first model of Picard rank three

X = Bl_{p,q} P^2, with N^1(X) = ZH + ZE_1 + ZE_2 and intersection form
diag(1,-1,-1). The ring is a bespoke five-field carrier because the graded
basis 1,H,E_1,E_2,pt then holds pair by pair, and because the nested dual
numbers of SmoothQuadric produce a hyperbolic form, which diag(1,-1,-1) is
not. ch_2 is a half-integer, so the coordinates record ch_2 = (a+b+c)/2 + v,
the same device ProjectivePlane uses; that is what makes chi integral, and
numericalVariety_satisfiesHRR checks it.

hodgeDefinite is the record that matters. It is the reverse Cauchy-Schwarz
inequality for diag(1,-1,-1): omega^2 > 0 forces the form to be negative
definite on the PLANE omega-perp. Unlike the rank-one models it is not vacuous,
and it is PROVED, not supplied. Consequently hasQuadraticSupportProperty and
hasSupportProperty carry exactly one supplied hypothesis, a
BogomolovGiesekerData, rather than two.

Nothing here identifies the carrier with K_num(X) for a geometric blow-up, and
no Chern-character map from coherent sheaves is constructed. IsAmpleCoefficients
records the ample cone for the reader; no theorem uses it. -/

#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Divisor
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.IsAmpleCoefficients
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.NumericalClass
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.add_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.add_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.add_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.add_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.add_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.algebraMap_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.algebraMap_eq
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.algebraMap_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.algebraMap_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.algebraMap_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.algebraMap_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.ext
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.ext_iff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.instAdd
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.instAlgebraRat
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.instCommRing
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.instMul
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.instNeg
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.instOne
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.instZero
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.mk.inj
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.mul_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.mul_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.mul_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.mul_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.mul_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.neg_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.neg_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.neg_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.neg_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.neg_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.ofRat
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.one_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.one_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.one_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.one_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.one_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.smul_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.smul_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.smul_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.smul_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.smul_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.sub_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.sub_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.sub_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.sub_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.sub_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.zero_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.zero_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.zero_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.zero_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.Ring.zero_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.antiCanonicalPolarization
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.basis
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.basis_four
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.basis_mul_mem
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.basis_one
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.basis_three
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.basis_two
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.basis_zero
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.chComp
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.chComp_add
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.chComp_mem
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.ch_sum
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.chi
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.const_eq_zero_of_mem_pieceOne
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.coordEquiv
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.degree
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.degree_apply
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.degree_basis_of_ne
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.degree_polarizationClass_sq
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.divisorClass
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.divisorClass_apply
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.divisorClass_intersection
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.divisorClass_map_rat_smul
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.divisorSpace
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.divisorSpace_pair
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_mem
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_mul_e₁Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_mul_e₂Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_mul_hQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_mul_pointQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₁Q_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_mem
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_mul_e₁Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_mul_e₂Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_mul_hQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_mul_pointQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.e₂Q_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_mem
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_mul_e₁Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_mul_e₂Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_mul_hQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_mul_pointQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hQ_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hasQuadraticSupportProperty
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hasSignatureTwo
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hasSupportProperty
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hodgeDefinite
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.hodgeDefinite_antiCanonical
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.intersectionForm
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.intersectionForm_apply
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.numericalRealization
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.numericalRealization_divisorSpace
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.numericalRealization_polarization
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.numericalRing
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.numericalVariety
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.numericalVariety_satisfiesHRR
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.one_mem
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pieceOne_eq_span
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_const
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_e₁Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_e₂Coeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_hCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_mem
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_mul_e₁Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_mul_e₂Q
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_mul_hQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_mul_pointQ
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.pointQ_ptCoeff
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.polarization
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.polarizationClass
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.polarizationClass_mem
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.toddComp
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.toddComp_mem
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.todd_sum
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.weight
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.weightOne_preimage
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.weight_four
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.weight_le_two
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.weight_one
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.weight_three
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.weight_two
#print axioms AlgebraicGeometry.Numerical.Examples.BlowUpPlane.weight_zero
