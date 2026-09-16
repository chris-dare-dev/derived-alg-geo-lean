/-
NumericalMukaiIntegral slice of the AlgebraicGeometry audit, split out so
concurrent branches append to different files (#480). See the umbrella file for
the contract and reading guide.

These records were in `StabilityConditionAudit/Lattice.lean` and
`Foundation.lean` until MO1.04's chart row (#1315). The declarations did not
change; their module did. `Mukai/IntegralBridge.lean` left
`LinearAlgebra/Lattice/` for `AlgebraicGeometry/Numerical/Mukai/Integral.lean`,
and `scripts/EnumDecls.lean` routes a declaration to an audit by module path, so
the sweep now counts them against this library. A record left behind in the
other audit would have made them read as unaudited here and as missing there.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Mukai.Integral

/-! ## The integral Mukai lattice inside the real extension

The `ℤ`-span of the extended basis is the integral Mukai extension, and the two
pairings agree under a map of middles — so wall finiteness is a statement about
integral classes rather than about an abstract `ZSpan`. -/

#print axioms Mukai.extendBasis
#print axioms Mukai.integralExtension
#print axioms Mukai.span_range_extendBasis
#print axioms Mukai.extendMap
#print axioms Mukai.realPairing_extendMap
#print axioms Mukai.isSphericalClass_extendMap
#print axioms Mukai.finite_sphericalOrthogonal_integralExtension
#print axioms Mukai.finite_orthogonalClasses_integralExtension

/-! ## `extendMap`, bundled

The Mukai-lattice leg of the charge chain was additive and unbundled like the
numerical leg. -/

#print axioms Mukai.extendMap_add
#print axioms Mukai.extendMapHom
