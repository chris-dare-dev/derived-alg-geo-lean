/-
Neutral exact functors used by Appendix B.2 filtrations.  The records live at the module-sheaf
root rather than in divisor or stability-condition consumers.
-/
import DerivedAlgGeo.AlgebraicGeometry.Modules

#print axioms AlgebraicGeometry.Scheme.Modules.reflectsEpimorphisms_toSheaf
#print axioms AlgebraicGeometry.Scheme.Modules.tensorLeftFunctor_preservesFiniteLimits
#print axioms AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj_left_of_isInvertible
#print axioms AlgebraicGeometry.Scheme.Modules.pushforward_preservesEpimorphisms_of_isClosedImmersion
#print axioms AlgebraicGeometry.Scheme.Modules.pushforward_preservesHomology_of_isClosedImmersion
#print axioms AlgebraicGeometry.Scheme.Modules.pushforward_preservesFiniteColimits_of_isClosedImmersion
#print axioms AlgebraicGeometry.Scheme.Modules.shortExact_map_pushforward_of_isClosedImmersion

/-! ## Pushforward along an affine morphism preserves epimorphisms of quasi-coherent sheaves -/

#print axioms AlgebraicGeometry.gammaPushforwardIso
#print axioms AlgebraicGeometry.gammaPushforwardNatIso
#print axioms AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_SpecMap
#print axioms AlgebraicGeometry.Scheme.Modules.pushforward_map_epi_of_isAffineHom
