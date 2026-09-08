/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mukai.GeometricInput
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.HnTiltStabilityFunction

/-!
# Assemble the Mukai stability function on the HN-tilted heart

This file is the terminal categorical assembly for Bridgeland's four
tilted-heart positivity cases. It consumes the two named geometric contracts
from `Mukai.GeometricInput` and proves positivity for torsion generators,
shifted torsion-free generators, and their extensions. The ambient exponential
Mukai charge is consequently a `StabilityFunction` on the HN-tilted heart.

No Harder--Narasimhan property for the resulting stability function is claimed.
The HN hypothesis below belongs only to the weak slope function used to define
the torsion pair and its tilt.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Triangulated

universe u v

namespace CategoryTheory.Triangulated

attribute [local instance] TStructure.heartFullSubcategoryAbelian

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

namespace MukaiWeakSlopeCompat

open MukaiChargeData WeakStabilityFunctionOn

variable {t : TStructure C}

/-- The complete torsion-generator case, with only the residual
rank-and-degree-zero classification supplied geometrically. -/
theorem mem_semiClosedUpperHalfPlane_of_hnTors
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    {T₀ : t.heart.FullSubcategory} (hT₀ : ¬IsZero T₀)
    (hT : T₀ ∈ hnTors S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ)) :
    ambientCharge m b β ω T₀.obj ∈ semiClosedUpperHalfPlane := by
  rcases lt_or_eq_of_le (S.rank_nonneg T₀) with hrank | hrank
  · exact Cpt.mem_semiClosedUpperHalfPlane_of_hnTors_of_rank_pos
      hb hHN hT₀ hrank hT
  · have hrank0 : S.rank T₀ = 0 := hrank.symm
    rcases lt_or_eq_of_le (S.degree_nonneg_of_rank_zero T₀ hT₀ hrank0) with
      hdegree | hdegree
    · rw [ambientCharge_obj]
      exact mem_semiClosedUpperHalfPlane_of_im_pos (by
        rw [Cpt.im_charge_eq_degree_of_rank_zero hb β hrank0]
        exact_mod_cast hdegree)
    · obtain ⟨s, hs, hclass⟩ := hzero T₀ hT₀ hT hrank0 hdegree.symm
      exact MukaiChargeData.mem_semiClosedUpperHalfPlane_of_ambientCharge_of_dimension_zero
        hb hclass hs

variable [FiniteDimensional ℝ V]

/-- The complete shifted torsion-free generator case. Strictly below the
cutoff is formal slope arithmetic; equality is discharged by the supplied
factorwise Mukai decomposition. -/
theorem mem_semiClosedUpperHalfPlane_of_shift_hnFree
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 2 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition m b β ω S)
    {F₀ : t.heart.FullSubcategory} (hF₀ : ¬IsZero F₀)
    (hF : F₀ ∈ hnFree S.toWeakStabilityFunction
      ((b β ω : ℝ) : WithTop ℝ)) :
    ambientCharge m b β ω (F₀.obj⟦(1 : ℤ)⟧) ∈ semiClosedUpperHalfPlane := by
  have hrank : 0 < S.rank F₀ := S.rank_pos_of_mem_hnFree hHN hF₀ hF
  have hslope : S.slope F₀ ≤ b β ω := by
    have htop := slope_le_of_mem_hnFree hHN hF₀ hF
    rw [show S.toWeakStabilityFunction.slope F₀ = S.topSlope F₀ from rfl,
      S.topSlope_of_rank_pos hrank, WithTop.coe_le_coe] at htop
    exact htop
  rcases hslope.lt_or_eq with hbelow | heq
  · exact Cpt.mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_slope_lt
      hb hHN hF₀ hF hbelow
  · obtain ⟨n, hn, G, hclass, hGrank, hGslope, hGsquare⟩ :=
      hboundary F₀ hF₀ hF heq
    exact Cpt.mem_semiClosedUpperHalfPlane_of_shift_of_boundary_factors
      hb hsigPos hω hn G hclass hGrank hGslope hGsquare

/-- **The exponential Mukai charge is positive on every nonzero object of the
HN-tilted heart.** The generic HRS assembly reduces this to the two Mukai
generator theorems above. -/
theorem mem_semiClosedUpperHalfPlane_of_mem_hnTilt_heart
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 2 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition m b β ω S)
    {X : C}
    (hX : (S.toWeakStabilityFunction.hnTilt
      ((b β ω : ℝ) : WithTop ℝ) hHN).heart X)
    (hX0 : ¬IsZero X) :
    ambientCharge m b β ω X ∈ semiClosedUpperHalfPlane := by
  exact S.toWeakStabilityFunction.mem_semiClosedUpperHalfPlane_of_mem_hnTilt_heart
    ((b β ω : ℝ) : WithTop ℝ) hHN (ambientChargeHom m b β ω)
    (fun _ hT₀ hT ↦ Cpt.mem_semiClosedUpperHalfPlane_of_hnTors
      hb hHN hzero hT₀ hT)
    (fun _ hF₀ hF ↦ Cpt.mem_semiClosedUpperHalfPlane_of_shift_hnFree
      hb hsigPos hω hHN hboundary hF₀ hF)
    hX hX0

/-- **The exponential Mukai charge as a stability function on the tilted
heart.** This is the categorical conclusion of the four-case positivity
argument; it does not assert an HN property for this new stability function. -/
def tiltStabilityFunction
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 2 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition m b β ω S) :
    WeakStabilityCondition.StabilityFunction
      (S.toWeakStabilityFunction.hnTilt ((b β ω : ℝ) : WithTop ℝ) hHN) :=
  S.toWeakStabilityFunction.hnTiltStabilityFunction
    ((b β ω : ℝ) : WithTop ℝ) hHN (ambientChargeHom m b β ω)
    (fun _ hT₀ hT ↦ Cpt.mem_semiClosedUpperHalfPlane_of_hnTors
      hb hHN hzero hT₀ hT)
    (fun _ hF₀ hF ↦ Cpt.mem_semiClosedUpperHalfPlane_of_shift_hnFree
      hb hsigPos hω hHN hboundary hF₀ hF)

@[simp]
theorem tiltStabilityFunction_Z
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 2 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition m b β ω S) :
    (Cpt.tiltStabilityFunction hb hsigPos hω hHN hzero hboundary).Z =
      ambientChargeHom m b β ω := rfl

end MukaiWeakSlopeCompat

end CategoryTheory.Triangulated
