/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.Cohomology.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.ShiftNaturality

/-!
# Heart cohomology commutes with shifts

The truncation--shift comparisons assemble into the natural isomorphism

`H^n_t ≅ [n] ⋙ H^0_t`.

This is the functorial bridge from degree-zero heart cohomology to every
cohomological degree.
-/

namespace CategoryTheory.Triangulated.Tilting

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- The ambient-functor comparison underlying `originalHeartCohShiftNatIso`. -/
noncomputable def originalHeartCohUnderlyingShiftNatIso
    (t : TStructure C) (n : ℤ) :
    t.truncGELE n n ⋙ shiftFunctor C n ≅
      shiftFunctor C n ⋙
        (t.truncGELE (0 : ℤ) 0 ⋙ shiftFunctor C (0 : ℤ)) := by
  simpa only [zero_add] using
    (CategoryTheory.Triangulated.TStructure.truncGELEShiftNatIso t (0 : ℤ) n ≪≫
      (Functor.rightUnitor
        (shiftFunctor C n ⋙ t.truncGELE (0 : ℤ) 0)).symm ≪≫
      Functor.isoWhiskerLeft
        (shiftFunctor C n ⋙ t.truncGELE (0 : ℤ) 0)
        (shiftFunctorZero C ℤ).symm ≪≫
      Functor.associator _ _ _)

/-- Degree-`n` heart cohomology is naturally degree-zero heart cohomology
after shifting the input by `n`. -/
noncomputable def originalHeartCohShiftNatIso
    (t : TStructure C) (n : ℤ) :
    originalHeartCohFunctor t n ≅
      shiftFunctor C n ⋙ originalHeartCohFunctor t 0 :=
  NatIso.ofComponents
    (fun X => ObjectProperty.isoMk _
      ((originalHeartCohUnderlyingShiftNatIso t n).app X))
    (fun {X Y} f => by
      apply ObjectProperty.hom_ext
      exact (originalHeartCohUnderlyingShiftNatIso t n).hom.naturality f)

end CategoryTheory.Triangulated.Tilting
