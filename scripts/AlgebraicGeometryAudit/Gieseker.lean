/-
Gieseker slice of the AlgebraicGeometry audit: the eventual order on reduced Hilbert functions and
the two stability predicates built from it (#902). The shared Hilbert data these rest on is in
`SheafStability.lean`, the mu-slope theory in `SheafSlope.lean`, and every statement relating the
two in `SheafStabilityComparison.lean`. Split out so concurrent branches append to different
files; see the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker

/-! ## The Gieseker order and (semi)stability (#902)

The subject-neutral numerical core first: an integer binomial sum is eventually nonnegative
exactly when its coefficient vector is lexicographically nonnegative from the top, proved by
induction on the top index through a forward difference, using integrality to turn "eventually
increasing" into "eventually positive". Then the eventual order on reduced Hilbert functions, the
lexicographic criterion, totality at positive multiplicity, and the two stability predicates.
Gieseker stability is deliberately NOT a `StabilityFunctionOn`: it is ordered by a polynomial, not
by the argument of a complex charge. Purity is a conjunct of both predicates and is audited with
the shared data it is defined from. -/

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
