import DerivedAlgGeo.AlgebraicGeometry.Modules.Pullback.Stalk

#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkRingCocone
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkRingIsColimit
#print axioms AlgebraicGeometry.Scheme.Modules.neighborhoodModuleStalkFunctor
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleStalkFunctor
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleStalkToSheafificationApp
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleStalkToSheafificationApp_isIso
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleStalkSheafificationIso
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkForgetIso
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor_preservesColimitsOfShape
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor_preservesFiniteLimits
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkFunctors_jointlyReflectIsomorphisms
#print axioms AlgebraicGeometry.Scheme.Modules.preservesFiniteLimits_of_stalkwise
#print axioms AlgebraicGeometry.Scheme.Modules.neighborhoodRingHom
#print axioms AlgebraicGeometry.Scheme.Modules.neighborhoodModulePullback
#print axioms AlgebraicGeometry.Scheme.Modules.neighborhoodRingHom_comp_stalkCocone
#print axioms AlgebraicGeometry.Scheme.Modules.constNeighborhoodPushforwardIsoApp
#print axioms AlgebraicGeometry.Scheme.Modules.constNeighborhoodPushforwardIso
#print axioms AlgebraicGeometry.Scheme.Modules.neighborhoodModulePullbackStalkIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackStalkPresheafIso
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModulePullbackStalkIso
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackStalkIso

/-! ## Germs, and the germ of the unit (issue #1664)

`presheafModuleGerm`, `moduleStalkGerm` are the germ maps into the module stalks, and the inverse of
the pullback stalk isomorphism sends `1 ⊗ germ m` to the germ of the unit image of `m`.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleGerm
#print axioms AlgebraicGeometry.Scheme.Modules.moduleStalkGerm
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModuleStalkFunctor_map_germ
#print axioms AlgebraicGeometry.Scheme.Modules.presheafModulePullbackStalkIso_inv_app_one_tmul_germ
#print axioms AlgebraicGeometry.Scheme.Modules.pullbackStalkIso_inv_app_one_tmul_germ
