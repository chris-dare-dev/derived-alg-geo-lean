import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.LineBundleExt

/-!
# Linear line-bundle Ext and cohomology audit

This slice audits the ambient-module-sheaf bridge
`Extⁿ(L, N) ≃ₗ[k] Hⁿ(X, L⁻¹ ⊗ N)`. It deliberately does not identify these groups with Ext in
`Coh X`; that remains the `CoherentExtComparison` boundary.
-/

/-! ## Linear unit-Ext/cohomology comparison -/

#print axioms AlgebraicGeometry.Scheme.Modules.extUnitAddEquivDerivedH_smul
#print axioms AlgebraicGeometry.Scheme.Modules.extUnitLinearEquivCoherentH
#print axioms AlgebraicGeometry.Scheme.Modules.extUnitLinearEquivCoherentH_apply

/-! ## Linear line-bundle Ext comparison -/

#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.extLineLinearEquivCoherentH

/-! ## Projective finiteness and amplitude -/

#print axioms AlgebraicGeometry.ProjectivePresentation.module_finite_lineBundleExt
#print axioms AlgebraicGeometry.ProjectivePresentation.lineBundleExt_subsingleton_of_bound_lt
#print axioms AlgebraicGeometry.ProjectivePresentation.lineBundleExt_finrankSupport_subset_range
#print axioms AlgebraicGeometry.ProjectivePresentation.lineBundleExt_finrankSupport_finite
