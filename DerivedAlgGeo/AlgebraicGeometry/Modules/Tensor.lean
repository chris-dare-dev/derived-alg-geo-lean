import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Picard
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Basic
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundle
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.LineBundleLinear
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Monoidal
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Stalk
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Colimits
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Flat
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Complex
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.ComplexColimits
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Invertible
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Linear

/-!
# Tensor products of module sheaves

The ordinary sheafified tensor, its linear and colimit properties, and its
literal total on cochain complexes live in the children of this umbrella.

## Main definitions

This umbrella introduces no definitions. `Tensor/Complex.lean` defines the
literal `AlgebraicGeometry.Scheme.Modules.totalTensor` on cochain complexes.

## Main results

`Tensor/Colimits.lean` proves ordinary sheaf tensor preserves colimits in
either slot. `Tensor/ComplexColimits.lean` transfers site-universe and
small-shape colimit preservation to either fixed-input slot of the literal
complex total; sequential diagrams are a specialization.
`Tensor/Flat.lean` gives the termwise homology-preservation input for flat
module sheaves.
`Tensor/Stalk.lean` compares the sheafified tensor with the tensor of module
stalks, naturally in the variable right factor.

## Implementation notes

The complex-total colimit result uses the generic two-slot total theorem in
`DerivedAlgGeo.Algebra.Homology.Bifunctor`; it does not require a K-flat
complex or assert the existence of a derived tensor product. Derived-category
consumers import these geometric inputs downstream.

## References

The canonical construction is in `Tensor/Complex.lean`; ordinary colimit
preservation is in `Tensor/Colimits.lean`, and the complex adapter is in
`Tensor/ComplexColimits.lean`.

## Tags

scheme-module sheaf, tensor, total complex, flatness, colimit
-/
