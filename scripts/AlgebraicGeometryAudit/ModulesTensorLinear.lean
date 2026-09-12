import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Linear

/-!
# Linear scheme-module tensor audit

The sheafified tensor product is additive, linear over global functions, and linear over the base
field after restricting scalars.  These are categorical compatibility results only: none asserts
Hom-finiteness or any geometric boundedness theorem.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.modulesMonoidalPreadditive
#print axioms AlgebraicGeometry.Scheme.Modules.unitorConj_globalSectionSmul
#print axioms AlgebraicGeometry.Scheme.Modules.tensorHom_id_globalSectionSmul
#print axioms AlgebraicGeometry.Scheme.Modules.modulesMonoidalLinearGlobal
#print axioms AlgebraicGeometry.Variety.modulesMonoidalLinear
