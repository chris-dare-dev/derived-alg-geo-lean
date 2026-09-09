/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialWallTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Circle

/-!
# The polarised-surface transport is the compressed divisorial transport

`Walls/Divisorial/Circle.lean` shows that fixing the transverse parameter of a
divisorial slice gives exactly the `(s,t)` model, pulled back along the
degree-weighted triple `ChargeCoordinates.toNumClass`.  This file records the
one statement in that comparison whose type mentions a numerical variety: the
transport `Surface.toNumClass` of `WallTransport.lean` is that triple, read off
the coordinates `ofNumericalData` extracts.  The two differ only by where the
rational-to-real cast of the product `∫H² · rank` is taken.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

universe u v w

namespace AlgebraicGeometry.Numerical.Surface

noncomputable section

variable {A : Type u} {N : Type v} {D : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable [AddCommGroup D] [Module ℝ D]

/-- The polarised-surface transport of `WallTransport.lean` is the compressed
transport of the coordinates it reads off.  The two differ only by where the
rational-to-real cast of the product `∫H² · rank` is taken. -/
theorem toNumClass_eq_ofNumericalData (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (E : N) :
    Surface.toNumClass V P E =
      (ChargeCoordinates.ofNumericalData V P).toNumClass E := by
  have h : ((V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) : ℚ) : ℝ)
      = ((V.ring.degree (P.cls ^ 2) : ℚ) : ℝ) * ((V.rank E : ℤ) : ℝ) := by
    push_cast
    ring
  simp only [Surface.toNumClass, ChargeCoordinates.toNumClass,
    ChargeCoordinates.ofNumericalData_rank, ChargeCoordinates.ofNumericalData_degree,
    ChargeCoordinates.ofNumericalData_chTwo,
    ChargeCoordinates.ofNumericalData_hyperplaneSquare]
  rw [h]


end

end AlgebraicGeometry.Numerical.Surface
