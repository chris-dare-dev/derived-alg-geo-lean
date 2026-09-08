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

The boundary contract and the resulting constructor are parameterized by an
arbitrary factorwise lower bound `realForm ≥ -δ`. The parent assembly needs
only `2δ < ω²`; the historical K3 interface is retained as the specialization
`δ = 1`. Thus the categorical layer does not decide whether the geometric
bound comes from the K3 stable-simple Ext calculation, a stronger abelian
surface result, or another surface realization.

More generally, `tiltStabilityFunctionOfMargin` consumes the exact positive
Hodge margin separately on every factor. `tiltStabilityFunctionOfLowerBound`
derives that contract from a uniform `δ`, and `tiltStabilityFunction` is the
legacy K3-normalized child. None of these constructors chooses between `ch`
and `ch * sqrt(td)`; that choice has already been made by the additive Mukai
class map `m`.

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

/-- The complete shifted torsion-free generator case under the exact
factorwise Hodge margin. Strictly below the cutoff is formal slope arithmetic;
equality is discharged by the broadest boundary decomposition contract. -/
theorem mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_margin
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 0 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecompositionWithMargin m b β ω S)
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
  · obtain ⟨n, hn, G, hclass, hGrank, hGslope, hGmargin⟩ :=
      hboundary F₀ hF₀ hF heq
    exact Cpt.mem_semiClosedUpperHalfPlane_of_shift_of_boundary_factors_of_margin
      hb hsigPos hω hn G hclass hGrank hGslope hGmargin

/-- The complete shifted torsion-free generator case for an arbitrary
factorwise quadratic lower bound. Strictly below the cutoff is formal slope
arithmetic; equality is discharged by the supplied factorwise Mukai
decomposition and the uniform threshold `2δ < ω²`. -/
theorem mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_lower_bound
    (δ : ℝ)
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 0 < b ω ω) (hωδ : 2 * δ < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecompositionWithLowerBound m b β ω S δ)
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
    exact Cpt.mem_semiClosedUpperHalfPlane_of_shift_of_boundary_factors_of_lower_bound
      δ hb hsigPos hω hωδ hn G hclass hGrank hGslope hGsquare

/-- The K3-normalized shifted-free theorem, obtained from the general lower
bound with `δ = 1`. -/
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
  have hω0 : 0 < b ω ω := by linarith
  exact Cpt.mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_lower_bound
    1 hb hsigPos hω0 (by simpa using hω) hHN hboundary hF₀ hF

/-- **The exponential Mukai charge is positive on every nonzero object of the
HN-tilted heart under the exact factorwise Hodge margin.** This is the broadest
whole-heart result; lower-bound variants are convenience specializations. -/
theorem mem_semiClosedUpperHalfPlane_of_mem_hnTilt_heart_of_margin
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 0 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecompositionWithMargin m b β ω S)
    {X : C}
    (hX : (S.toWeakStabilityFunction.hnTilt
      ((b β ω : ℝ) : WithTop ℝ) hHN).heart X)
    (hX0 : ¬IsZero X) :
    ambientCharge m b β ω X ∈ semiClosedUpperHalfPlane := by
  exact S.toWeakStabilityFunction.mem_semiClosedUpperHalfPlane_of_mem_hnTilt_heart
    ((b β ω : ℝ) : WithTop ℝ) hHN (ambientChargeHom m b β ω)
    (fun _ hT₀ hT ↦ Cpt.mem_semiClosedUpperHalfPlane_of_hnTors
      hb hHN hzero hT₀ hT)
    (fun _ hF₀ hF ↦ Cpt.mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_margin
      hb hsigPos hω hHN hboundary hF₀ hF)
    hX hX0

/-- **The exponential Mukai charge is positive on every nonzero object of the
HN-tilted heart under an arbitrary factorwise lower bound.** The generic HRS
assembly reduces this to the two Mukai generator theorems above. -/
theorem mem_semiClosedUpperHalfPlane_of_mem_hnTilt_heart_of_lower_bound
    (δ : ℝ)
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 0 < b ω ω) (hωδ : 2 * δ < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecompositionWithLowerBound m b β ω S δ)
    {X : C}
    (hX : (S.toWeakStabilityFunction.hnTilt
      ((b β ω : ℝ) : WithTop ℝ) hHN).heart X)
    (hX0 : ¬IsZero X) :
    ambientCharge m b β ω X ∈ semiClosedUpperHalfPlane := by
  exact S.toWeakStabilityFunction.mem_semiClosedUpperHalfPlane_of_mem_hnTilt_heart
    ((b β ω : ℝ) : WithTop ℝ) hHN (ambientChargeHom m b β ω)
    (fun _ hT₀ hT ↦ Cpt.mem_semiClosedUpperHalfPlane_of_hnTors
      hb hHN hzero hT₀ hT)
    (fun _ hF₀ hF ↦ Cpt.mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_lower_bound
      δ hb hsigPos hω hωδ hHN hboundary hF₀ hF)
    hX hX0

/-- The K3-normalized whole-heart positivity theorem, recovered at `δ = 1`. -/
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
  have hω0 : 0 < b ω ω := by linarith
  exact Cpt.mem_semiClosedUpperHalfPlane_of_mem_hnTilt_heart_of_lower_bound
    1 hb hsigPos hω0 (by simpa using hω) hHN hzero hboundary hX hX0

/-- **The exponential Mukai charge as a stability function on the tilted
heart under the exact factorwise Hodge margin.** This is the parent
constructor: it assumes only what the numerical Hodge-index proof consumes and
does not impose a uniform quadratic lower bound. -/
def tiltStabilityFunctionOfMargin
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 0 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecompositionWithMargin m b β ω S) :
    WeakStabilityCondition.StabilityFunction
      (S.toWeakStabilityFunction.hnTilt ((b β ω : ℝ) : WithTop ℝ) hHN) :=
  S.toWeakStabilityFunction.hnTiltStabilityFunction
    ((b β ω : ℝ) : WithTop ℝ) hHN (ambientChargeHom m b β ω)
    (fun _ hT₀ hT ↦ Cpt.mem_semiClosedUpperHalfPlane_of_hnTors
      hb hHN hzero hT₀ hT)
    (fun _ hF₀ hF ↦ Cpt.mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_margin
      hb hsigPos hω hHN hboundary hF₀ hF)

/-- **The exponential Mukai charge as a stability function on the tilted
heart, parameterized by a factorwise quadratic lower bound.** This is the
categorical conclusion of the four-case positivity argument; it does not
assert an HN property for this new stability function. -/
def tiltStabilityFunctionOfLowerBound
    (δ : ℝ)
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 0 < b ω ω) (hωδ : 2 * δ < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecompositionWithLowerBound m b β ω S δ) :
    WeakStabilityCondition.StabilityFunction
      (S.toWeakStabilityFunction.hnTilt ((b β ω : ℝ) : WithTop ℝ) hHN) :=
  S.toWeakStabilityFunction.hnTiltStabilityFunction
    ((b β ω : ℝ) : WithTop ℝ) hHN (ambientChargeHom m b β ω)
    (fun _ hT₀ hT ↦ Cpt.mem_semiClosedUpperHalfPlane_of_hnTors
      hb hHN hzero hT₀ hT)
    (fun _ hF₀ hF ↦ Cpt.mem_semiClosedUpperHalfPlane_of_shift_hnFree_of_lower_bound
      δ hb hsigPos hω hωδ hHN hboundary hF₀ hF)

/-- The historical K3-normalized stability-function constructor.

This is the `δ = 1` specialization of
`tiltStabilityFunctionOfLowerBound`. The wrapper keeps existing consumers
source-compatible while making the geometric constant explicit for new
surface children. -/
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
      (S.toWeakStabilityFunction.hnTilt ((b β ω : ℝ) : WithTop ℝ) hHN) := by
  have hω0 : 0 < b ω ω := by linarith
  exact Cpt.tiltStabilityFunctionOfLowerBound 1 hb hsigPos hω0 (by simpa using hω)
    hHN hzero hboundary

@[simp]
theorem tiltStabilityFunctionOfMargin_Z
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 0 < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecompositionWithMargin m b β ω S) :
    (Cpt.tiltStabilityFunctionOfMargin hb hsigPos hω hHN hzero hboundary).Z =
      ambientChargeHom m b β ω := rfl

@[simp]
theorem tiltStabilityFunctionOfLowerBound_Z
    (δ : ℝ)
    {m : K₀ C →+ Mukai.RealExtension V} {b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {β ω : V}
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1)
    (hω : 0 < b ω ω) (hωδ : 2 * δ < b ω ω)
    {S : WeakSlopeData t.heart.FullSubcategory}
    (Cpt : MukaiWeakSlopeCompat (ofAmbient t m) S b ω)
    (hHN : S.toWeakStabilityFunction.HasHNProperty)
    (hzero : MukaiTilt.HasDimensionZeroTorsionClasses m b β ω S)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecompositionWithLowerBound m b β ω S δ) :
    (Cpt.tiltStabilityFunctionOfLowerBound δ hb hsigPos hω hωδ hHN hzero hboundary).Z =
      ambientChargeHom m b β ω := rfl

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
