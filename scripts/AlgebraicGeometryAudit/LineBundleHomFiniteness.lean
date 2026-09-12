import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.Hom

/-!
# Linear line-bundle Hom and finiteness audit

This slice audits the formal bridge from a linear adjunction through the canonical linear
`H⁰`/sections comparison to finite-dimensional Hom from a line bundle. The final projective
theorem retains `IsCoherent (L⁻¹ ⊗ N)` as an explicit hypothesis: no tensor-coherence theorem,
boundedness principle, or Mukai-class realization is supplied here.
-/

/-! ## Generic linear adjunction -/

#print axioms CategoryTheory.Adjunction.homLinearEquiv

/-! ## Linear degree-zero cohomology and global sections -/

#print axioms AlgebraicGeometry.Cohomology.globalSectionsModule
#print axioms AlgebraicGeometry.Cohomology.linearGlobalSectionsObj
#print axioms AlgebraicGeometry.Cohomology.coherentHZeroSectionsAddEquiv
#print axioms AlgebraicGeometry.Cohomology.coherentHZeroSectionsAddEquiv_naturality
#print axioms AlgebraicGeometry.Cohomology.coherentHZeroSectionsAddEquiv_smul
#print axioms AlgebraicGeometry.Cohomology.coherentHZeroSectionsLinearEquiv
#print axioms AlgebraicGeometry.Cohomology.module_finite_linearGlobalSectionsObj

/-! ## Linear line-bundle Hom comparisons -/

#print axioms AlgebraicGeometry.Scheme.Modules.unitHomTopLinearEquiv
#print axioms AlgebraicGeometry.Scheme.Modules.unitHomTopLinearEquivOver
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.tensorLeftHomLinearEquiv
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.lineHomTopLinearEquiv
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.lineHomTopLinearEquivOver

/-! ## Hom-finiteness reduction and projective endpoint -/

#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.module_finite_hom_of_finiteHZero
#print axioms AlgebraicGeometry.ProjectivePresentation.module_finite_lineBundleHom
