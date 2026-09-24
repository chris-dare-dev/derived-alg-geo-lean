/-
Generic module-localization slice of the AlgebraicGeometry audit. Despite the
audit's historical name, `EnumDecls` routes the repository's `Algebra` root to
this audit.
-/
import DerivedAlgGeo.Algebra.Module.Localization

/-! ## Localization and kernels of modules -/

#print axioms LinearMap.kerMap
#print axioms IsLocalizedModule.kerMap
#print axioms IsLocalizedModule.kernelMap
#print axioms IsLocalizedModule.kernelNatTrans

/-! ## Finite module descent through localization -/

#print axioms Module.exists_finite_submodule_of_isLocalization
#print axioms Module.exists_finitely_presented_submodule_of_isLocalization
#print axioms Module.exists_finite_submodule_of_isLocalization_containing
#print axioms Module.exists_finitely_presented_submodule_of_isLocalization_containing
#print axioms Module.exists_finite_submodules_of_isLocalization_map
#print axioms Module.exists_finite_submodules_of_isLocalization_two_maps

/-! ## Cohomology of a localized three-term complex -/

#print axioms IsLocalizedModule.boundaryToCycles
#print axioms IsLocalizedModule.localizedDifferential
#print axioms IsLocalizedModule.localizedCyclesMap
#print axioms IsLocalizedModule.localizedBoundaryToCycles
#print axioms IsLocalizedModule.cohomologyMap
#print axioms IsLocalizedModule.cohomologyMap_isLocalized
