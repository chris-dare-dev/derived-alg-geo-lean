/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import DerivedAlgGeo.CategoryTheory.Triangulated.ExactFunctorFamily

/-!
# Monoidal structures compatible with triangulation

A monoidal category and a triangulated category are independent structures.
This file records their compatibility: the tensor bifunctor is exact in both
variables, with one coherent two-variable choice of shift comparisons.

The class is deliberately separate from `MonoidalCategory`. Not every
monoidal category is triangulated, and not every triangulated category is
monoidal. It is also separate from dg enrichment: enrichment uses a monoidal
*base* category, while a monoidal dg category asks for additional compatibility
between its enrichment and its tensor product.
-/

namespace CategoryTheory.MonoidalCategory

open CategoryTheory CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [MonoidalCategory C]

/-- Compatibility between a monoidal structure and a pretriangulated
structure.  The complete tensor bifunctor is exact in both variables.

Using `Functor.ExactBifunctor` here is stronger than listing exactness of every
left tensor twist independently.  Besides the right tensor twists, it records
naturality of all shift comparisons in the fixed variable and Mathlib's
Koszul compatibility between the two shift directions.

This is the generic parent interface for concrete exact tensor products such
as a derived tensor product on `Dᵇ(Coh X)`. -/
class IsCompatibleWithTriangulation where
  /-- Exactness and coherent shift behavior of tensor in both slots. -/
  tensorExact : Functor.ExactBifunctor (curriedTensor C)

namespace IsCompatibleWithTriangulation

variable [IsCompatibleWithTriangulation C]

/-- The exact-bifunctor witness carried by the compatibility root. -/
def exactBifunctor : Functor.ExactBifunctor (curriedTensor C) :=
  IsCompatibleWithTriangulation.tensorExact

/-- A left tensor twist commutes with shifts.  Retained as a projection-style
API for consumers of the earlier one-slot interface. -/
@[reducible] def tensorCommShift (K : C) :
    ((curriedTensor C).obj K).CommShift ℤ :=
  exactBifunctor C |>.secondCommShift K

/-- A left tensor twist is triangulated. -/
theorem tensorIsTriangulated (K : C) :
    letI : ((curriedTensor C).obj K).CommShift ℤ := tensorCommShift C K
    ((curriedTensor C).obj K).IsTriangulated :=
  exactBifunctor C |>.secondTriangulated K

/-- A left tensor twist is additive. -/
theorem tensorAdditive (K : C) : ((curriedTensor C).obj K).Additive := by
  letI : ((curriedTensor C).obj K).CommShift ℤ := tensorCommShift C K
  letI : ((curriedTensor C).obj K).IsTriangulated := tensorIsTriangulated C K
  infer_instance

/-- A right tensor twist commutes with shifts. -/
@[reducible] def tensorFlipCommShift (K : C) :
    ((curriedTensor C).flip.obj K).CommShift ℤ :=
  exactBifunctor C |>.firstCommShift K

/-- A right tensor twist is triangulated. -/
theorem tensorFlipIsTriangulated (K : C) :
    letI : ((curriedTensor C).flip.obj K).CommShift ℤ := tensorFlipCommShift C K
    ((curriedTensor C).flip.obj K).IsTriangulated :=
  exactBifunctor C |>.firstTriangulated K

/-- A right tensor twist is additive. -/
theorem tensorFlipAdditive (K : C) :
    ((curriedTensor C).flip.obj K).Additive := by
  letI : ((curriedTensor C).flip.obj K).CommShift ℤ := tensorFlipCommShift C K
  letI : ((curriedTensor C).flip.obj K).IsTriangulated :=
    tensorFlipIsTriangulated C K
  infer_instance

end IsCompatibleWithTriangulation

end CategoryTheory.MonoidalCategory
