/-
Pushforward of module sheaves is lax monoidal, a slice of the AlgebraicGeometry audit (issue #1664,
DQ1.2a).
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules.Pushforward.Monoidal

/-! # Lax monoidal pushforward

`pushforwardLaxMonoidal` is the instance `(pushforward f).LaxMonoidal`; its tensorator multiplies
sections and every coherence equation is checked on pure tensors.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardTensorData
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardTensorHom
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardTensorHom_app_tmulSection
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardUnitHom
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardUnitHom_app
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardLaxMonoidal
