/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.Existence
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.AisleProjection

/-!
# Projections onto compactly generated aisles

The t-structure assembled from a compact-generator approximation has
`Coprod(G)` as its zero aisle.  This file turns its truncation functor into
chosen right-projection data onto `Coprod(G)`.

Right admissibility is automatic when `G` is triangulated.  Preservation of
small coproducts is deliberately stated in terms of the corresponding
truncation functor: this is the precise continuity input needed later for
base-change decompositions, and is not a formal consequence of an arbitrary
t-structure.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe w v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]
  {G : ObjectProperty C}

namespace CompactGeneratorApproximation

variable (h : CompactGeneratorApproximation.{w} G)
include h

/-- The chosen right projection onto the coproduct-and-extension closure of
the generators. -/
noncomputable def rightProjectionData :
    ObjectProperty.RightProjectionData G.coprodClosure.{w} :=
  (h.tStructure.aisleRightProjectionData 0).ofEq h.tStructure_le_zero

/-- A coproduct closure of triangulated generators is right admissible once
the compact-generator approximation has been constructed. -/
theorem coprodClosure_isRightAdmissible [G.IsTriangulated] :
    G.coprodClosure.{w}.IsRightAdmissible :=
  ObjectProperty.RightProjectionData.isRightAdmissible
    (rightProjectionData h) inferInstance

/-- Continuity of zero truncation transfers to the chosen ambient projection
onto `Coprod(G)`. -/
theorem rightProjectionData_preservesSmallCoproducts
    (htrunc : (h.tStructure.truncLE 0).PreservesSmallCoproducts.{w}) :
    h.rightProjectionData.ambientProjection.PreservesSmallCoproducts.{w} := by
  intro κ
  letI : PreservesColimitsOfShape (Discrete κ)
      (h.tStructure.aisleRightProjectionData 0).ambientProjection :=
    h.tStructure.aisleRightProjectionData_preservesSmallCoproducts 0 htrunc κ
  exact preservesColimitsOfShape_of_natIso
    ((h.tStructure.aisleRightProjectionData 0).ofEqAmbientIso
      h.tStructure_le_zero).symm

end CompactGeneratorApproximation

end CategoryTheory.Triangulated.TStructure
