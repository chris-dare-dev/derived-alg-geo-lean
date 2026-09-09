/-
Gieseker slice of the AlgebraicGeometry audit: the Hilbert function of a coherent sheaf against a
supplied polarization and the slope theory built from it (#900, #901, #902, #903, #904). Split out so
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

/-! ## Purity, the Gieseker order and (semi)stability (#902)

The subject-neutral numerical core first: an integer binomial sum is eventually nonnegative
exactly when its coefficient vector is lexicographically nonnegative from the top, proved by
induction on the top index through a forward difference, using integrality to turn "eventually
increasing" into "eventually positive". Then purity, the eventual order on reduced Hilbert
functions, the lexicographic criterion, totality at positive multiplicity, and the two stability
predicates. Gieseker stability is deliberately NOT a `StabilityFunctionOn`: it is ordered by a
polynomial, not by the argument of a complex charge. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.CoeffLexLE
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.GiesekerLE
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.GiesekerLT
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsGiesekerSemistable
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsGiesekerSemistable.isPure
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsGiesekerSemistable.multiplicity_pos
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsGiesekerSemistable.not_isZero
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsGiesekerSemistable.of_iso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsGiesekerStable
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsGiesekerStable.isGiesekerSemistable
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsGiesekerStable.of_iso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsPure
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsPure.multiplicity_pos
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsPure.not_isZero
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsPure.of_iso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerLE_iff_coeffLexLE
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerLE_of_iso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerLE_refl
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerLE_total
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerLE_trans
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerLT_irrefl
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerLT_trans
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.lexDiff
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.lexDiff_swap
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.normalizedCoefficient
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.normalizedCoefficient_dim
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.normalizedCoefficient_eq_iff
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.normalizedCoefficient_le_iff
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.normalizedCoefficient_lt_iff
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.normalizedCoefficient_pred_le_of_giesekerLE
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.not_isGiesekerSemistable_of_isZero
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.not_isGiesekerStable_of_isZero
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.reducedHilbert_eq_of_iso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.reducedHilbert_le_iff_sum
#print axioms AlgebraicGeometry.Stability.Gieseker.eventually_nonneg_binomial_iff
#print axioms AlgebraicGeometry.Stability.Gieseker.eventually_nonneg_binomial_total
#print axioms AlgebraicGeometry.Stability.Gieseker.eventually_pos_binomial_of_top_pos
#print axioms AlgebraicGeometry.Stability.Gieseker.eventually_pos_of_succ_le
#print axioms AlgebraicGeometry.Stability.Gieseker.exists_top_ne_zero
#print axioms AlgebraicGeometry.Stability.Gieseker.sum_binomial_eq_of_vanishing
#print axioms AlgebraicGeometry.Stability.Gieseker.sum_binomial_succ_sub

/-! ## The weak slope datum on `Coh X` (#903)

`MuPositivityData` is the supplied geometric input, two consequences of ampleness that this pin
cannot prove. Everything else is an instantiation of the existing abstract slope theory: the
multiplicity homomorphism is `rankHom` verbatim, the degree coefficient is composed with
`Int.castAddHom ℝ` because `WeakSlopeData.degreeHom` is real-valued, and the slope, charge and
`WithTop ℝ` honest slope are read off in both the positive-multiplicity and the zero regimes. The
comparison with Gieseker semistability is delivered in one direction only, and its proof uses
purity to rule out the multiplicity-zero subobject that would otherwise have slope `⊤`. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.MuCurvePositivityData
#print axioms AlgebraicGeometry.Stability.Gieseker.MuCurvePositivityData.degree_pos_of_multiplicity_zero
#print axioms AlgebraicGeometry.Stability.Gieseker.MuCurvePositivityData.multiplicity_nonneg
#print axioms AlgebraicGeometry.Stability.Gieseker.MuCurvePositivityData.toMuPositivityData
#print axioms AlgebraicGeometry.Stability.Gieseker.MuPositivityData
#print axioms AlgebraicGeometry.Stability.Gieseker.MuPositivityData.degree_nonneg_of_multiplicity_zero
#print axioms AlgebraicGeometry.Stability.Gieseker.MuPositivityData.multiplicity_nonneg
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_implies_muSemistable
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.slopeData
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.slopeData_charge
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.slopeData_degree
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.slopeData_rank
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.slopeData_slope
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.toWeakSlopeData_slopeData
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.topSlope_le_of_giesekerLE
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_charge
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_degree
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_rank
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_slope
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_slope_eq_normalizedCoefficient
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_topSlope_eq_normalizedCoefficient
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_topSlope_of_multiplicity_pos
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.weakSlopeData_topSlope_of_multiplicity_zero

/-! ## The maximal destabilizing subobject (#904)

`MuHNInput` supplies the two facts sheaf-level Harder-Narasimhan theory needs and this pin
cannot prove: termination of ascending subobject chains, and Grothendieck's boundedness lemma.
Neither the maximal destabilizing subobject nor `HasHNProperty` is a field. The boundedness
field takes a REAL bound rather than one in `WithTop`, because a `WithTop` bound is satisfied
vacuously by the top element. That the bounded slope is actually attained needs no third input:
multiplicity is additive and nonnegative, so subobject multiplicities are bounded by that of the
ambient sheaf, every slope is a multiple of one over its factorial, and such a set bounded above
has a greatest element. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.MuHNInput
#print axioms AlgebraicGeometry.Stability.Gieseker.MuHNInput.noetherian
#print axioms AlgebraicGeometry.Stability.Gieseker.MuHNInput.slope_bddAbove
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicity_le_of_mono
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicity_subobject_le
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.exists_slopeMax
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.IsMaximalDestabilizing
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.exists_maximalDestabilizing
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.maximalDestabilizing_isSemistable
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.topSlope_maximalDestabilizing_eq_top_iff

/-! ## The see-saw inequality (groundwork for #905)

Additivity of multiplicity and of the degree coefficient on a short exact sequence, and the
mediant inequality they give: a sub of slope at most the quotient has slope at most the whole.
The abstract weak-slope theory has no such inequality, and this one is not abstract — its
multiplicity-zero case is decided by the geometric input in `MuPositivityData`. The
Harder-Narasimhan recursion of #905 consumes it to prove that the slope drops strictly on the
quotient by the maximal destabilizing subobject. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicity_shortExact
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hilbertDegreeCoefficient_shortExact
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.topSlope_le_of_shortExact
