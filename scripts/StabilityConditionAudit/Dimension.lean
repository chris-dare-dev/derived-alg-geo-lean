/-
Dimension slice of the StabilityCondition audit, split out so concurrent branches append to
different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.Dimension

/-! ## Generation time (#917)

The `ℕ∞`-valued least number of extension steps from one object property to another, on top of
Mathlib's `triangEnvelopeIter`. No `ContainsZero` or `Nonempty` hypothesis anywhere; the bridges
reduce Mathlib's strong and classical triangulated generators to finiteness of
`generationTime P ⊤`. -/

#print axioms CategoryTheory.ObjectProperty.generationTime
#print axioms CategoryTheory.ObjectProperty.generationTime_le_coe_iff
#print axioms CategoryTheory.ObjectProperty.generationTime_antitone_left
#print axioms CategoryTheory.ObjectProperty.generationTime_mono_right
#print axioms CategoryTheory.ObjectProperty.generationTime_eq_zero_iff
#print axioms CategoryTheory.ObjectProperty.generationTime_eq_zero_iff'
#print axioms CategoryTheory.ObjectProperty.generationTime_self
#print axioms CategoryTheory.ObjectProperty.generationTime_eq_top_iff
#print axioms CategoryTheory.ObjectProperty.isStrongTriangulatedGenerator_iff_generationTime_ne_top
#print axioms CategoryTheory.ObjectProperty.isClassicalTriangulatedGenerator_of_generationTime_ne_top

/-! ## Rouquier dimension (#919)

The infimum over singleton generation times and its finite, strong-generator,
classical-generator, and zero-stage characterisations.
-/

#print axioms CategoryTheory.Triangulated.rouquierDim
#print axioms CategoryTheory.Triangulated.rouquierDim_le_coe_iff
#print axioms CategoryTheory.Triangulated.rouquierDim_ne_top_iff_exists_strong
#print axioms CategoryTheory.Triangulated.exists_isClassicalTriangulatedGenerator_of_rouquierDim_ne_top
#print axioms CategoryTheory.Triangulated.rouquierDim_eq_zero_iff
