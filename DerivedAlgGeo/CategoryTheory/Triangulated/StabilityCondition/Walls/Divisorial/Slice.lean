/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Divisorial.Slice
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Alignment

/-!
# Wall equations on orthogonal divisorial charge slices

The orthogonal slice, its charge family, and its real and imaginary formulas
live upstream under `CentralCharge/Divisorial/`.  This file adds exactly the
determinant-alignment locus and its formula.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

universe u v w

variable {D : Type u} [AddCommGroup D] [Module ℝ D]
variable {N : Type v} [AddCommGroup N]
variable {U : Type w} [AddCommGroup U] [Module ℝ U]
variable {S : DivisorSpace D} (T : OrthogonalSlice S U)

namespace OrthogonalSlice

/-- The numerical determinant-alignment alignmentLocus of two classes in an orthogonal
divisor slice. -/
def alignmentLocus (ch : ChernCharacter N D) (v w : N) : Set (Point U) :=
  (T.chargeFamily ch).alignmentLocus v w

/-- The universal determinant equation evaluated using the two divisorial
slice formulas. -/
theorem alignmentValue_eq (ch : ChernCharacter N D) (p : Point U) (v w : N) :
    (T.chargeFamily ch).alignmentValue p v w =
      T.reFormula ch p v * T.imFormula ch p w -
        T.imFormula ch p v * T.reFormula ch p w := by
  simp only [Wall.ChargeFamily.alignmentValue, Wall.ChargeFamily.re,
    Wall.ChargeFamily.im, T.charge_re, T.charge_im]

end OrthogonalSlice

end


end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
