/-
Generic limit-preservation slice of the StabilityCondition audit. Despite the
audit's historical name, this slice covers category-theoretic infrastructure.
-/
import DerivedAlgGeo.CategoryTheory.Limits

/-! ## Preservation through composition and reflective targets -/

#print axioms CategoryTheory.Limits.Sigma.sum_π_ι_eq_id_of_isZero
#print axioms CategoryTheory.Limits.Sigma.isZero_of_sum_π_ι_eq_id_of_not_mem
#print axioms CategoryTheory.Limits.Sigma.sum_π_ι_eq_id_iff_isZero
#print axioms CategoryTheory.Limits.Sigma.sum_π_ι_eq_id_of_isZero_all
#print axioms CategoryTheory.Limits.Sigma.isZero_of_sum_π_ι_eq_id_of_not_mem_all
#print axioms CategoryTheory.Limits.Sigma.sum_π_ι_eq_id_iff_isZero_all
#print axioms CategoryTheory.Limits.Sigma.hom_ext_of_finite_support
#print axioms CategoryTheory.Limits.Sigma.hom_eq_zero_of_finite_support
#print axioms CategoryTheory.Limits.preservesColimit_comp_left
#print axioms CategoryTheory.preservesColimitIso_naturality
#print axioms CategoryTheory.preservesColimitIso_naturality_assoc
#print axioms CategoryTheory.Adjunction.preservesColimitsOfShape_of_comp_left
