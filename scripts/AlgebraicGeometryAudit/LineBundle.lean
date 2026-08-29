import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundle

/-!
# Neutral line-bundle root audit

This slice deliberately imports only the scheme-module owner. Line-bundle data and its tensor
operations must remain available without importing determinant, exterior-power, divisor, or
Picard-group leaves.
-/

#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.unit
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.dual
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.tensor
