/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.PolarisedWallTransport
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.ThreefoldWallTransport
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.WallTransport

/-!
# Dimension-specific comparisons for polarised wall transport

This module imports the generic `(n,m,κ)` transport together with its surface
and threefold specializations.  The generic root imports neither specialization.
-/

namespace AlgebraicGeometry.Numerical.Polarised

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

universe u v
variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

theorem surface_toNumClass_eq (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (E : N) :
    Surface.toNumClass V P E =
      (hDegrees V P (unitCorr A) 2 E 0, hDegrees V P (unitCorr A) 2 E 1,
        hDegrees V P (unitCorr A) 2 E 2) := by
  have h0 : hDegrees V P (unitCorr A) 2 E 0 =
      ((V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 0 * P.cls ^ (2 - 0)) : ℚ) : ℝ) = _
    rw [hDegrees_zero V P E, mul_comm]
  have h1 : hDegrees V P (unitCorr A) 2 E 1 = ((degH V P E : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 1 * P.cls ^ (2 - 1)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
    rfl
  have h2 : hDegrees V P (unitCorr A) 2 E 2 =
      ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 2 * P.cls ^ (2 - 2)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
    norm_num
  rw [h0, h1, h2]
  rfl

theorem threefold_toNumClass_eq (V : NumericalVarietyData 3 A N)
    (P : Polarization V.ring) (E : N) :
    Threefold.toNumClass V P E =
      (hDegrees V P (unitCorr A) 3 E 0, hDegrees V P (unitCorr A) 3 E 1,
        hDegrees V P (unitCorr A) 3 E 2, hDegrees V P (unitCorr A) 3 E 3) := by
  have h0 : hDegrees V P (unitCorr A) 3 E 0 =
      ((V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 0 * P.cls ^ (3 - 0)) : ℚ) : ℝ) = _
    rw [hDegrees_zero V P E, mul_comm]
  have h1 : hDegrees V P (unitCorr A) 3 E 1 =
      ((V.ring.degree (V.chComp E 1 * P.cls ^ 2) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 1 * P.cls ^ (3 - 1)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
  have h2 : hDegrees V P (unitCorr A) 3 E 2 =
      ((V.ring.degree (V.chComp E 2 * P.cls) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 2 * P.cls ^ (3 - 2)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
    norm_num
  have h3 : hDegrees V P (unitCorr A) 3 E 3 =
      ((V.ring.degree (V.chComp E 3) : ℚ) : ℝ) := by
    show ((V.ring.degree (corrComp V (unitCorr A) E 3 * P.cls ^ (3 - 3)) : ℚ) : ℝ) = _
    rw [corrComp_unitCorr]
    norm_num
  rw [h0, h1, h2, h3]
  rfl

theorem surfaceVec_toNumClass (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) (E : N) :
    surfaceVec (Surface.toNumClass V P E) = hDegrees V P (unitCorr A) 2 E := by
  funext k
  rw [surface_toNumClass_eq V P E]
  fin_cases k <;> simp [surfaceVec]

theorem surface_wallChargeFamily_eq (V : NumericalVarietyData 2 A N)
    (P : Polarization V.ring) :
    Surface.wallChargeFamily V P =
      (wallChargeFamily V P (unitCorr A) 2).reindex Exp.stChart := by
  apply ChargeFamily.ext
  intro p
  ext E
  rw [Surface.wallChargeFamily_charge, stCharge_eq_exp]
  show _ = Exp.charge 2 (Exp.stChart p) (hDegrees V P (unitCorr A) 2 E)
  rw [← surfaceVec_toNumClass V P E]
  rfl

end AlgebraicGeometry.Numerical.Polarised

#print axioms AlgebraicGeometry.Numerical.Polarised.surface_wallChargeFamily_eq
