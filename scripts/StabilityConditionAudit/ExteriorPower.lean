/-
Generic exterior-power slice of the StabilityCondition audit. Despite the
audit's historical name, this slice covers linear algebra and categorical
presheaf infrastructure independent of schemes.
-/
import DerivedAlgGeo.Algebra.Category.ModuleCat.Sheaf.ExteriorPower
import DerivedAlgGeo.LinearAlgebra.ExteriorPower

/-! ## Semilinear exterior powers -/

#print axioms LinearMap.exteriorPower
#print axioms LinearMap.exteriorPower_ιMulti

/-! ## Exterior powers of presheaves of modules -/

#print axioms PresheafOfModules.exteriorPower
#print axioms PresheafOfModules.exteriorPower_obj
#print axioms PresheafOfModules.exteriorPower.map
#print axioms PresheafOfModules.exteriorPower.map_app_ιMulti
#print axioms PresheafOfModules.exteriorPower.map_id
#print axioms PresheafOfModules.exteriorPower.map_comp
#print axioms PresheafOfModules.exteriorPower.mapIso
#print axioms PresheafOfModules.exteriorPowerFunctor

/-! ## Top exterior powers -/

#print axioms Module.topExteriorPower
#print axioms Module.finrank_topExteriorPower
#print axioms Module.topPowerset
#print axioms Module.topExteriorFreeEquiv
#print axioms Module.topExteriorFreeEquiv_ιMulti
