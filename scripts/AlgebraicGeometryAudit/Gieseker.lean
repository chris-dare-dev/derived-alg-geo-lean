/-
Gieseker slice of the AlgebraicGeometry audit: the Hilbert function of a coherent sheaf against a
supplied polarization and the slope theory built from it (#900, #901). Split out so
concurrent branches append to different files; see the umbrella file for the contract and reading
guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker


/-! ## The Hilbert function against a supplied polarization (#900)

`PolarizedVarietyData` is supplied-not-proved input: a Picard class that is NOT asserted ample,
finite coherent cohomology with a linear connecting system, a dimension, and a `TwistContext` for
every coherent sheaf. Everything below it is proved: the Hilbert function is Snapper's
one-variable Euler function, agrees with the Picard-level `eulerPic` at `L ^ n`, is invariant
under isomorphism, additive on short exact sequences (a theorem, through `Coh.shortExact_map_ι`,
`shortExact_map_tensorLeft_of_invertible` and `eulerCharacteristic_additive_modules`), factors
through `K₀Ab (Coh X)`, and has finite-difference degree at most the supplied dimension. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.C
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.D
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.L
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.dim
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.fwdDiff_hilbertFunction
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertFunction
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertFunction_additive
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertFunction_apply
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertFunction_degreeLE
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertFunction_eq_eulerCharacteristic_tensor
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertFunction_eq_eulerPic
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertFunction_eq_of_iso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertHom
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertHom_of
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.isCoherent_tensor_linePower
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.mk
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.mk.inj
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.picardMonomial_fin_one
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.twistFamily
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.twistModules_fin_one
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.twists

/-! ## Hilbert coefficients, multiplicity and degree (#901)

The Newton coefficients of the Hilbert function, the top two of them as homomorphisms out of the
Grothendieck group, and the Gregory-Newton representation that makes comparison at infinity
possible. Nothing here is supplied: additivity comes from #900's additivity, and the vanishing
above `P.dim` from Snapper's bound. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.degreeHom
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.degreeHom_of
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertCoefficient
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertCoefficient_additive
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertCoefficient_eq_fwdDiff
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertCoefficient_eq_of_iso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertCoefficient_eq_zero_of_lt
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertCoefficient_of_isZero
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertDegreeCoefficient
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertDegreeCoefficient_eq_of_iso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertFunction_eq_sum_choose
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertFunction_of_isZero
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicity
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicityHom
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicityHom_of
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicity_eq_of_iso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicity_of_isZero
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.reducedHilbert
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.reducedHilbert_apply
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.reducedHilbert_eq_sum_choose
