/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.Bifunctor
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Colimits
import DerivedAlgGeo.AlgebraicGeometry.Modules.Tensor.Complex

/-!
# Diagram colimits of complex tensor on scheme-module sheaves

Ordinary sheaf tensor preserves colimits in either slot. The generic
literal-total theorem transfers this to the two fixed-input slots of
`AlgebraicGeometry.Scheme.Modules.totalTensor` for site-universe and small
diagram categories. Sequential diagrams are a specialization.

## Main definitions

This module introduces no definitions. It studies the existing
`AlgebraicGeometry.Scheme.Modules.totalTensor`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.preservesColimitsOfShape_totalTensor_obj_site`
  and its flipped-slot counterpart preserve site-universe diagram colimits.
* `AlgebraicGeometry.Scheme.Modules.preservesColimitsOfShape_totalTensor_obj_small`
  and its flipped-slot counterpart preserve small diagram colimits.
* `AlgebraicGeometry.Scheme.Modules.preservesColimitsOfShape_totalTensor_obj_nat`
  and its flipped-slot counterpart preserve sequential colimits.

## Implementation notes

The sheaf tensor colimit theorems supply the partial-functor hypotheses at
each term of the fixed complex. The generic cochain-total theorem handles
the diagonal coproducts and the comparison to Mathlib's literal total.
The site-universe theorem uses ordinary sheaf tensor preservation directly.
Size-change instances supply small-shape preservation; the sequential
corollaries then specialize to `ℕ`.

## References

The inputs are
`AlgebraicGeometry.Scheme.Modules.tensorLeft_preservesColimitsOfShape`,
`AlgebraicGeometry.Scheme.Modules.tensorRight_preservesColimitsOfShape`, and the generic
`CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_obj`
and flipped-slot counterpart.

## Tags

scheme-module sheaf, total tensor, cochain complex, diagram colimit
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

/-- Literal total tensor preserves site-universe diagram colimits in the
second complex when the first is fixed. No flatness or exactness is needed. -/
theorem preservesColimitsOfShape_totalTensor_obj_site
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J ((totalTensor X).obj K) := by
  letI (L : X.Modules) : PreservesColimitsOfShape J (tensorLeft L) :=
    tensorLeft_preservesColimitsOfShape L J
  exact CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_obj
    (curriedTensor X.Modules) K

/-- Literal total tensor preserves site-universe diagram colimits in the
first complex when the second is fixed. The bicomplex degree order is retained. -/
theorem preservesColimitsOfShape_totalTensor_flip_obj_site
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (J : Type u) [Category.{u} J] :
    PreservesColimitsOfShape J ((totalTensor X).flip.obj K) := by
  letI (L : X.Modules) : PreservesColimitsOfShape J (tensorRight L) :=
    tensorRight_preservesColimitsOfShape L J
  exact CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_flip_obj
    (curriedTensor X.Modules) K

/-- Literal total tensor preserves colimits of any small diagram in the
second complex with the first complex fixed. The size-change instances
transfer ordinary sheaf tensor preservation to small shapes. -/
theorem preservesColimitsOfShape_totalTensor_obj_small
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (J : Type) [Category.{0} J] :
    PreservesColimitsOfShape J ((totalTensor X).obj K) := by
  letI (L : X.Modules) : PreservesColimitsOfSize.{u,u} (tensorLeft L) := by
    constructor
    exact tensorLeft_preservesColimitsOfShape L _
  letI (L : X.Modules) : PreservesColimitsOfSize.{0,0} (tensorLeft L) :=
    preservesSmallestColimits_of_preservesColimits (tensorLeft L)
  exact CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_obj
    (curriedTensor X.Modules) K

/-- Literal total tensor preserves colimits of any small diagram in the
first complex with the second complex fixed. The bicomplex degree order is
retained. -/
theorem preservesColimitsOfShape_totalTensor_flip_obj_small
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ)
    (J : Type) [Category.{0} J] :
    PreservesColimitsOfShape J ((totalTensor X).flip.obj K) := by
  letI (L : X.Modules) : PreservesColimitsOfSize.{u,u} (tensorRight L) := by
    constructor
    exact tensorRight_preservesColimitsOfShape L _
  letI (L : X.Modules) : PreservesColimitsOfSize.{0,0} (tensorRight L) :=
    preservesSmallestColimits_of_preservesColimits (tensorRight L)
  exact CategoryTheory.Functor.preservesColimitsOfShape_map₂CochainComplex_flip_obj
    (curriedTensor X.Modules) K

/-- The small-shape theorem at the sequential diagram category. -/
theorem preservesColimitsOfShape_totalTensor_obj_nat
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    PreservesColimitsOfShape ℕ ((totalTensor X).obj K) :=
  preservesColimitsOfShape_totalTensor_obj_small X K ℕ

/-- The flipped small-shape theorem at the sequential diagram category. -/
theorem preservesColimitsOfShape_totalTensor_flip_obj_nat
    (X : Scheme.{u}) (K : CochainComplex X.Modules ℤ) :
    PreservesColimitsOfShape ℕ ((totalTensor X).flip.obj K) :=
  preservesColimitsOfShape_totalTensor_flip_obj_small X K ℕ

end

end AlgebraicGeometry.Scheme.Modules
