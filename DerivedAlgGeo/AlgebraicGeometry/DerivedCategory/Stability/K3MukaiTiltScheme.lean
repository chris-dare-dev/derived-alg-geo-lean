/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Stability.K3MukaiTilt
import DerivedAlgGeo.AlgebraicGeometry.RiemannRoch.Surface.Assembly
import DerivedAlgGeo.AlgebraicGeometry.Surface.K3

/-!
# Scheme-derived K3 specialization of the Mukai tilt stability function

This file specializes `K3MukaiTilt.lean` to the numerical surface assembled
from geometric Todd and reconstruction data.  It is separate so the reusable
numerical adapter does not acquire the full geometric Riemann--Roch import.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

universe u v w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian

namespace AlgebraicGeometry.DerivedCategory.Stability.K3MukaiTilt

open AlgebraicGeometry Numerical
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.IntersectionTheory.ChernCharacter
open AlgebraicGeometry.RiemannRoch
open AlgebraicGeometry.RiemannRoch.Surface
open AlgebraicGeometry.Stability.Gieseker

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [IsSmoothProperVariety k X]
variable {A : Type v} [CommRing A] [Algebra ℚ A]
variable {W : Type w} [AddCommGroup W] [Module ℝ W]
variable {D : FiniteCohomology k X}
variable {C : D.LinearConnectingSystem}
variable {Q : PairingContext D C 2 A}
variable {K : SmoothProperVariety.CanonicalSheafData k X 2}
variable [hK3Surface : SmoothProperVariety.IsK3Surface k X K]
variable [FiniteDimensional ℝ W]

/-- The K3 Mukai tilt stability function for the numerical surface assembled
from geometric Todd and reconstruction data.

`χ(O_X)=2` remains explicit: the current K3 package supplies trivial canonical
class and `H¹(O_X)=0`, but the needed Serre-duality bridge to the Euler
characteristic has not yet been formalized. -/
def schemeTiltStabilityFunction
    (T : ToddData.Data Q K) (Rg : ReconstructionSystem (X := X) (P := Q))
    (RR : Numerical.Surface.NumericalRealization
      (RiemannRoch.Surface.Assembly.toNumericalVariety T Rg).ring (D := W))
    {β ω : W}
    (G : PolarizedVarietyData k X)
    (N : SlopeNormalization (V := RiemannRoch.Surface.Assembly.toNumericalVariety T Rg)
      G RR ω)
    (hμ : MuPositivityData G) (hbounded : SlopeBoundedness G)
    (hchi : Q.intersection.eulerPic 1 = 2)
    (m : K₀ (_root_.DerivedCategory.Bounded (Coh X)) →+ Mukai.RealExtension W)
    (hm : IsAmbientMukaiClass RR m)
    (hHodge : RR.divisorSpace.HodgeDefinite ω)
    (hω : 2 < RR.divisorSpace.pair ω ω)
    (hzero : HasDimensionZeroMukaiClasses RR ω)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition m
      RR.divisorSpace.intersection β ω (N.boundedMukaiSlopeData hμ)) :
    WeakStabilityCondition.StabilityFunction
      ((N.boundedMukaiSlopeData hμ).toWeakStabilityFunction.hnTilt
        (((RR.divisorSpace.intersection β ω : ℝ)) : WithTop ℝ)
        (N.boundedMukaiSlopeData_hasHNProperty hμ (muHNInput hbounded))) :=
  N.tiltStabilityFunction hμ hbounded
    (RiemannRoch.Surface.Assembly.toIsK3 T Rg
      hK3Surface.canonicalClass_eq_one hchi)
    m hm hHodge hω hzero hboundary

@[simp]
theorem schemeTiltStabilityFunction_Z
    (T : ToddData.Data Q K) (Rg : ReconstructionSystem (X := X) (P := Q))
    (RR : Numerical.Surface.NumericalRealization
      (RiemannRoch.Surface.Assembly.toNumericalVariety T Rg).ring (D := W))
    {β ω : W}
    (G : PolarizedVarietyData k X)
    (N : SlopeNormalization (V := RiemannRoch.Surface.Assembly.toNumericalVariety T Rg)
      G RR ω)
    (hμ : MuPositivityData G) (hbounded : SlopeBoundedness G)
    (hchi : Q.intersection.eulerPic 1 = 2)
    (m : K₀ (_root_.DerivedCategory.Bounded (Coh X)) →+ Mukai.RealExtension W)
    (hm : IsAmbientMukaiClass RR m)
    (hHodge : RR.divisorSpace.HodgeDefinite ω)
    (hω : 2 < RR.divisorSpace.pair ω ω)
    (hzero : HasDimensionZeroMukaiClasses RR ω)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition m
      RR.divisorSpace.intersection β ω (N.boundedMukaiSlopeData hμ)) :
    (schemeTiltStabilityFunction T Rg RR G N hμ hbounded hchi m hm hHodge hω
      hzero hboundary).Z =
      MukaiChargeData.ambientChargeHom m RR.divisorSpace.intersection β ω := rfl

/-- The scheme-derived K3 tilt stability function using the canonical
cohomological extension of the coherent Mukai class.  This removes the
separate ambient class map and restriction proof from the geometric input. -/
def canonicalSchemeTiltStabilityFunction
    (T : ToddData.Data Q K) (Rg : ReconstructionSystem (X := X) (P := Q))
    (RR : Numerical.Surface.NumericalRealization
      (RiemannRoch.Surface.Assembly.toNumericalVariety T Rg).ring (D := W))
    {β ω : W}
    (G : PolarizedVarietyData k X)
    (N : SlopeNormalization (V := RiemannRoch.Surface.Assembly.toNumericalVariety T Rg)
      G RR ω)
    (hμ : MuPositivityData G) (hbounded : SlopeBoundedness G)
    (hchi : Q.intersection.eulerPic 1 = 2)
    (hHodge : RR.divisorSpace.HodgeDefinite ω)
    (hω : 2 < RR.divisorSpace.pair ω ω)
    (hzero : HasDimensionZeroMukaiClasses RR ω)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition (derivedMukaiClass RR)
      RR.divisorSpace.intersection β ω (N.boundedMukaiSlopeData hμ)) :
    WeakStabilityCondition.StabilityFunction
      ((N.boundedMukaiSlopeData hμ).toWeakStabilityFunction.hnTilt
        (((RR.divisorSpace.intersection β ω : ℝ)) : WithTop ℝ)
        (N.boundedMukaiSlopeData_hasHNProperty hμ (muHNInput hbounded))) :=
  N.canonicalTiltStabilityFunction hμ hbounded
    (RiemannRoch.Surface.Assembly.toIsK3 T Rg
      hK3Surface.canonicalClass_eq_one hchi)
    hHodge hω hzero hboundary

@[simp]
theorem canonicalSchemeTiltStabilityFunction_Z
    (T : ToddData.Data Q K) (Rg : ReconstructionSystem (X := X) (P := Q))
    (RR : Numerical.Surface.NumericalRealization
      (RiemannRoch.Surface.Assembly.toNumericalVariety T Rg).ring (D := W))
    {β ω : W}
    (G : PolarizedVarietyData k X)
    (N : SlopeNormalization (V := RiemannRoch.Surface.Assembly.toNumericalVariety T Rg)
      G RR ω)
    (hμ : MuPositivityData G) (hbounded : SlopeBoundedness G)
    (hchi : Q.intersection.eulerPic 1 = 2)
    (hHodge : RR.divisorSpace.HodgeDefinite ω)
    (hω : 2 < RR.divisorSpace.pair ω ω)
    (hzero : HasDimensionZeroMukaiClasses RR ω)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition (derivedMukaiClass RR)
      RR.divisorSpace.intersection β ω (N.boundedMukaiSlopeData hμ)) :
    (canonicalSchemeTiltStabilityFunction T Rg RR G N hμ hbounded hchi hHodge hω
      hzero hboundary).Z =
      MukaiChargeData.ambientChargeHom (derivedMukaiClass RR)
        RR.divisorSpace.intersection β ω := rfl

end AlgebraicGeometry.DerivedCategory.Stability.K3MukaiTilt
