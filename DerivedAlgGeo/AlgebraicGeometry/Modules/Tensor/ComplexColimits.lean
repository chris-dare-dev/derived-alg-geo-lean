/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Bifunctor
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Colimits
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Complex

/-!
# Sequential colimits of complex tensor on scheme-module sheaves

Ordinary sheaf tensor preserves colimits in either slot. The generic
literal-total theorem transfers this to the two fixed-input slots of
`AlgebraicGeometry.Scheme.Modules.totalTensor` for diagrams indexed by `ℕ`.

## Main definitions

This module introduces no definitions. It studies the existing
`AlgebraicGeometry.Scheme.Modules.totalTensor`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.preservesColimitsOfShape_totalTensor_obj_nat`
  preserves sequential colimits with the first complex fixed.
* `AlgebraicGeometry.Scheme.Modules.preservesColimitsOfShape_totalTensor_flip_obj_nat`
  preserves sequential colimits with the second complex fixed.

## Implementation notes

The sheaf tensor colimit theorems supply the partial-functor hypotheses at
each term of the fixed complex. The generic cochain-total theorem handles
the diagonal coproducts and the comparison to Mathlib's literal total.
The size-change instances connect the site-universe theorem to the
small `ℕ` diagram shape.

## References

The inputs are
`AlgebraicGeometry.Scheme.Modules.tensorLeft_preservesColimitsOfShape`,
`AlgebraicGeometry.Scheme.Modules.tensorRight_preservesColimitsOfShape`, and the generic
`CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_obj`
and flipped-slot counterpart.

## Tags

scheme-module sheaf, total tensor, cochain complex, sequential colimit
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

/-- Literal total tensor preserves sequential colimits in the second complex
when the first is fixed. This uses ordinary tensor colimit preservation at
each term, without flatness or exactness. -/
theorem preservesColimitsOfShape_totalTensor_obj_nat
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    PreservesColimitsOfShape ℕ ((totalTensor X).obj K) := by
  letI (L : X.Modules) : PreservesColimitsOfSize.{u,u} (tensorLeft L) := by
    constructor
    exact tensorLeft_preservesColimitsOfShape L _
  letI (L : X.Modules) : PreservesColimitsOfSize.{0,0} (tensorLeft L) :=
    preservesSmallestColimits_of_preservesColimits (tensorLeft L)
  exact CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_obj
    (curriedTensor X.Modules) K

/-- Literal total tensor preserves sequential colimits in the first complex
when the second is fixed. The generic flipped-slot theorem keeps the original
bicomplex degree order. -/
theorem preservesColimitsOfShape_totalTensor_flip_obj_nat
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    PreservesColimitsOfShape ℕ ((totalTensor X).flip.obj K) := by
  letI (L : X.Modules) : PreservesColimitsOfSize.{u,u} (tensorRight L) := by
    constructor
    exact tensorRight_preservesColimitsOfShape L _
  letI (L : X.Modules) : PreservesColimitsOfSize.{0,0} (tensorRight L) :=
    preservesSmallestColimits_of_preservesColimits (tensorRight L)
  exact CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_flip_obj
    (curriedTensor X.Modules) K

end

end AlgebraicGeometry.Scheme.Modules
