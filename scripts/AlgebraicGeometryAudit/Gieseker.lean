/-
Gieseker slice of the AlgebraicGeometry audit: the Hilbert function of a coherent sheaf against a
supplied polarization and the slope theory built from it (#900, #901, #902, #903, #904, #905). Split out so
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

/-! ## The strict slope drop past the maximal destabilizing subobject (#905 core)

Every nonzero subobject of the quotient by the maximal destabilizing subobject has strictly
smaller slope. The proof uses the see-saw inequality together with BOTH clauses of
`IsMaximalDestabilizing`: the slope-maximality bounds the extension from above, and the
order-maximality among slope-attaining subobjects rules out equality. Two consequences follow at
once, and they are the two things the Harder-Narasimhan recursion needs: successive factor slopes
strictly decrease, and the quotient is pure, so its own maximal destabilizing subobject has
positive multiplicity and the next quotient has strictly smaller multiplicity. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.not_isZero_of_le
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.topSlope_lt_of_maximalDestabilizing
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicity_pos_of_maximalDestabilizing

/-! ## Lifting a filtration through the subobject correspondence (#905 splice)

Lattice-level facts, none of them about slopes, that the Harder-Narasimhan splice consumes: the
bottom of the quotient pulls back to the subobject itself, so a spliced chain really begins
`bot < B`; a strict inclusion has a nonzero successive quotient, and therefore pulls back to a
strict inclusion, which is what makes the spliced chain strictly monotone; and the first
successive quotient of a spliced chain is the subobject itself, which is how the first factor
inherits its slope and semistability from the maximal destabilizing subobject. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.pullback_bot
#print axioms AlgebraicGeometry.Stability.Gieseker.ofLE_bot_eq_zero
#print axioms AlgebraicGeometry.Stability.Gieseker.cokernelOfLEBotIso
#print axioms AlgebraicGeometry.Stability.Gieseker.cokernel_not_isZero_of_lt
#print axioms AlgebraicGeometry.Stability.Gieseker.pullback_lt_of_lt

/-! ## The spliced chain (#905 splice, continued)

The chain of the spliced filtration and the facts the structure's fields need: it starts at
bottom, its first step is the maximal destabilizing subobject, it is strictly monotone, it ends
at the top, its first successive quotient is that subobject, and each later one is the
corresponding quotient downstairs. Strict monotonicity reduces to adjacent steps by the `Fin`
criterion, so only two cases arise: the opening `bot < B`, and a pullback of a strict step. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.cokernelOfLECongr
#print axioms AlgebraicGeometry.Stability.Gieseker.spliceChain
#print axioms AlgebraicGeometry.Stability.Gieseker.spliceChain_zero
#print axioms AlgebraicGeometry.Stability.Gieseker.spliceChain_succ
#print axioms AlgebraicGeometry.Stability.Gieseker.spliceChain_strictMono
#print axioms AlgebraicGeometry.Stability.Gieseker.spliceChain_top
#print axioms AlgebraicGeometry.Stability.Gieseker.spliceFactorZeroIso
#print axioms AlgebraicGeometry.Stability.Gieseker.spliceFactorSuccIso

/-! ## The spliced filtration (#905)

Prepending the maximal destabilizing subobject to a filtration of the quotient. `firstFactorIso`
identifies a filtration's opening successive quotient with its first chain step, which is what
turns the strict drop -- a statement about SUBOBJECTS of the quotient -- into `muZero_lt_topSlope`,
a statement about the FACTORS of a filtration of it. `splice` then assembles all seven fields.
Strict antitonicity is proved directly rather than through the adjacent-step criterion: that
criterion indexes by `Fin G.n` with `G.n` opaque, which cannot be case-split. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.firstFactorIso
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.muZero_lt_topSlope
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.splice

/-! ## The recursion, and the weak HN property (#905)

`hasHNProperty` is the payoff of the lane: the abstract engine has never before been run on a
geometric category. Termination is NOT the chain condition of `MuHNInput`, as #905 states -- that
condition makes the maximal destabilizing subobject exist at each step. What descends is
multiplicity, and a single induction on it fails, because multiplicity is additive and a torsion
maximal destabilizing subobject has multiplicity zero. That step happens at most once, since
`isPure_cokernel` makes the quotient pure, so the recursion is staged:
`exists_filtration_of_pure` inducts on multiplicity and `exists_filtration` splits off the single
torsion step first. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.isSemistable_of_maximalDestabilizing_eq_top
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.not_isZero_cokernel_of_ne_top
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.multiplicity_cokernel
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.isPure_cokernel
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.exists_filtration_of_pure
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.exists_filtration
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hasHNProperty

/-! ## What the HN property unlocks (#905, items 4-6)

Pure application of the abstract API to the filtration above: no re-proof. `hnFiltration` picks
one of the filtrations with choice, so `muPlus` and `muMinus` are about that choice; the one
statement with mathematical content, `filtration_muPlus_ne_top_of_isPure`, is proved for an
arbitrary filtration and only then specialized. The `hnTors`/`hnFree` splitting comes verbatim
from `Foundation/StabilityFunction/WeakSplitting.lean`. -/

#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.hnFiltration
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.muPlus
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.muMinus
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.muMinus_le_muPlus
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.muPlus_eq_topSlope_chain_one
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.not_isZero_chain_one
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.filtration_muPlus_ne_top_of_isPure
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.muPlus_ne_top_of_isPure
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_implies_hn_trivial
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_hn_trivial_n
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_hn_trivial_muPlus
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.giesekerSemistable_hn_trivial_muMinus
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.exists_subobject_hnTors_cokernel_hnFree
#print axioms AlgebraicGeometry.Stability.Gieseker.PolarizedVarietyData.exists_shortExact_hnTors_hnFree
