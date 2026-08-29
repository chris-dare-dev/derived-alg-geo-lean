/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Monoidal structures compatible with triangulation

A monoidal category and a triangulated category are independent structures.
This file records their compatibility: tensoring on the left is additive,
commutes with the shift, and preserves distinguished triangles.

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
structure. Each left tensor functor is additive, commutes with shifts, and is
triangulated.

This is the generic parent interface for concrete exact tensor products such
as a derived tensor product on `Dᵇ(Coh X)`. -/
class IsCompatibleWithTriangulation where
  /-- Tensoring on the left is additive. -/
  tensorAdditive : ∀ K, ((curriedTensor C).obj K).Additive
  /-- Tensoring on the left commutes with the triangulated shift. -/
  tensorCommShift : ∀ K, ((curriedTensor C).obj K).CommShift ℤ
  /-- Tensoring on the left preserves distinguished triangles. -/
  tensorIsTriangulated : ∀ K, ((curriedTensor C).obj K).IsTriangulated

end CategoryTheory.MonoidalCategory
