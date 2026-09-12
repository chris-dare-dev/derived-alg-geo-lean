/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.DerivedCategory.BoundedHeart
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialMukai
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Mukai.Assembly
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakHNTransport
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakSlopeOrder
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Signature

/-!
# The Mukai tilt stability function on the bounded derived category of a K3

This file is the geometric adapter from coherent-sheaf data to the abstract
Mukai tilt assembly.  It constructs the correctly normalized numerical slope,
transfers its HN property from the Hilbert-coefficient slope, transports it to
the standard heart of `Dᵇ(Coh X)`, and compares the resulting slope with the
scheme-derived Mukai class.

Two genuinely geometric seams remain explicit: the dimension-zero sheaf
classification and the boundary Jordan--Hölder/Mukai-square decomposition.
The latter is exactly the existing abstract boundary hypothesis: issue #332
supplies finite-dimensional Hom spaces but not yet the stable-simple,
Jordan--Hölder, and Serre-duality argument needed to prove that decomposition.
No topology and no full stability condition are introduced here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

universe u v w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian

namespace AlgebraicGeometry.DerivedCategory.Stability.K3MukaiTilt

open AlgebraicGeometry Numerical
open AlgebraicGeometry.Stability.Gieseker

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]
variable {A : Type v} [CommRing A] [Algebra ℚ A]
variable {W : Type w} [AddCommGroup W] [Module ℝ W]
variable {V : NumericalVarietyData 2 A (K₀Ab (Coh X))}

/-- Grothendieck's boundedness lemma in the exact form needed for μ-HN
filtrations.  This is the only part of `MuHNInput` that remains supplied on a
Noetherian scheme. -/
def SlopeBoundedness (P : PolarizedVarietyData k X) : Prop :=
  ∀ F : Coh X, ∃ μ₀ : ℝ, ∀ B : Subobject F, ¬IsZero (B : Coh X) →
    0 < P.multiplicity (B : Coh X) →
      (P.hilbertDegreeCoefficient (B : Coh X) : ℝ) /
        (P.multiplicity (B : Coh X) : ℝ) ≤ μ₀

/-- Noetherianity of coherent sheaves discharges the first `MuHNInput` field;
only Grothendieck slope boundedness is retained. -/
theorem muHNInput [IsNoetherian X] {P : PolarizedVarietyData k X}
    {hμ : MuPositivityData P} (hbounded : SlopeBoundedness P) : MuHNInput P hμ :=
  MuHNInput.ofSlopeBoundedness hbounded

/-- The precise affine normalization relating the leading two Hilbert
coefficients to numerical rank and `ω · ch₁` on a surface.

For the usual Hilbert polynomial of a polarized K3, `scale` is `H²` and
`shift` is `H² / 2`.  They remain explicit because the current geometric
reconstruction and Gieseker packages do not yet prove that comparison. -/
structure SlopeNormalization
    (P : PolarizedVarietyData k X)
    (R : Numerical.Surface.NumericalRealization V.ring (D := W))
    (ω : W) where
  /-- Positive integral scaling between numerical rank and multiplicity. -/
  scale : ℤ
  /-- The scaling is strictly positive. -/
  scale_pos : 0 < scale
  /-- The affine shift of finite slopes. -/
  shift : ℝ
  /-- Hilbert multiplicity is the scaled numerical rank. -/
  multiplicity_eq : ∀ F : Coh X,
    P.multiplicity F = scale * V.rank (K₀Ab.of F)
  /-- The next Hilbert coefficient is divisor degree plus the rank shift. -/
  degree_eq : ∀ F : Coh X,
    ((P.hilbertDegreeCoefficient F : ℤ) : ℝ) =
      R.divisorSpace.pair ω (R.chernCharacter.chOne (K₀Ab.of F)) +
        shift * (V.rank (K₀Ab.of F) : ℝ)

namespace SlopeNormalization

variable {P : PolarizedVarietyData k X}
variable {R : Numerical.Surface.NumericalRealization V.ring (D := W)}
variable {ω : W}

/-- Numerical rank and `ω · ch₁` as weak slope data on coherent sheaves. -/
def mukaiSlopeData (N : SlopeNormalization P R ω)
    (hμ : MuPositivityData P) : WeakSlopeData (Coh X) where
  rankHom := V.rank
  degreeHom :=
    (R.divisorSpace.intersection ω).toAddMonoidHom.comp R.chernCharacter.chOne
  rank_nonneg F := by
    have hmult := hμ.multiplicity_nonneg F
    rw [N.multiplicity_eq F] at hmult
    nlinarith [N.scale_pos]
  degree_nonneg_of_rank_zero F hF hrank := by
    have hmult : P.multiplicity F = 0 := by
      rw [N.multiplicity_eq F, hrank, mul_zero]
    have hdegree := hμ.degree_nonneg_of_multiplicity_zero F hF hmult
    have hdegree' : (0 : ℝ) ≤ ((P.hilbertDegreeCoefficient F : ℤ) : ℝ) := by
      exact_mod_cast hdegree
    rw [N.degree_eq F, hrank] at hdegree'
    simpa [DivisorSpace.pair] using hdegree'

@[simp]
theorem mukaiSlopeData_rank (N : SlopeNormalization P R ω)
    (hμ : MuPositivityData P) (F : Coh X) :
    (N.mukaiSlopeData hμ).rank F = V.rank (K₀Ab.of F) := rfl

@[simp]
theorem mukaiSlopeData_degree (N : SlopeNormalization P R ω)
    (hμ : MuPositivityData P) (F : Coh X) :
    (N.mukaiSlopeData hμ).degree F =
      R.divisorSpace.pair ω (R.chernCharacter.chOne (K₀Ab.of F)) := rfl

/-- At positive numerical rank, the Hilbert slope is the Mukai slope followed
by the positive affine normalization. -/
theorem hilbertSlope_eq (N : SlopeNormalization P R ω)
    (hμ : MuPositivityData P) {F : Coh X}
    (hrank : 0 < (N.mukaiSlopeData hμ).rank F) :
    (P.weakSlopeData hμ).slope F =
      ((N.mukaiSlopeData hμ).slope F + N.shift) / (N.scale : ℝ) := by
  have hrankR : (0 : ℝ) < ((N.mukaiSlopeData hμ).rank F : ℝ) := by
    exact_mod_cast hrank
  have hrankVR : (0 : ℝ) < (V.rank (K₀Ab.of F) : ℝ) := by
    simpa using hrankR
  have hscaleR : (0 : ℝ) < (N.scale : ℝ) := by exact_mod_cast N.scale_pos
  rw [P.weakSlopeData_slope, N.degree_eq F, N.multiplicity_eq F,
    WeakSlopeData.slope, N.mukaiSlopeData_rank, N.mukaiSlopeData_degree]
  push_cast
  field_simp [ne_of_gt hrankVR, ne_of_gt hscaleR]

/-- The Hilbert-coefficient slope and the numerical Mukai slope induce the
same order on coherent sheaves. -/
theorem sameSlopeOrder (N : SlopeNormalization P R ω)
    (hμ : MuPositivityData P) :
    WeakSlopeData.SameSlopeOrder (P.weakSlopeData hμ) (N.mukaiSlopeData hμ) := by
  constructor
  intro F G
  have hscaleR : (0 : ℝ) < (N.scale : ℝ) := by exact_mod_cast N.scale_pos
  rcases eq_or_lt_of_le ((N.mukaiSlopeData hμ).rank_nonneg F) with hF | hF
  · have hF0 : V.rank (K₀Ab.of F) = 0 := by exact hF.symm
    have hFmult : P.multiplicity F = 0 := by
      rw [N.multiplicity_eq F, hF0, mul_zero]
    rw [P.weakSlopeData_topSlope_of_multiplicity_zero hμ hFmult,
      (N.mukaiSlopeData hμ).topSlope_of_rank_zero hF.symm]
    rcases eq_or_lt_of_le ((N.mukaiSlopeData hμ).rank_nonneg G) with hG | hG
    · have hG0 : V.rank (K₀Ab.of G) = 0 := by exact hG.symm
      have hGmult : P.multiplicity G = 0 := by
        rw [N.multiplicity_eq G, hG0, mul_zero]
      rw [P.weakSlopeData_topSlope_of_multiplicity_zero hμ hGmult,
        (N.mukaiSlopeData hμ).topSlope_of_rank_zero hG.symm]
    · have hGmult : 0 < P.multiplicity G := by
        rw [N.multiplicity_eq G]
        exact mul_pos N.scale_pos hG
      rw [P.weakSlopeData_topSlope_of_multiplicity_pos hμ hGmult,
        (N.mukaiSlopeData hμ).topSlope_of_rank_pos hG]
      simp
  · have hFmult : 0 < P.multiplicity F := by
      rw [N.multiplicity_eq F]
      exact mul_pos N.scale_pos hF
    rcases eq_or_lt_of_le ((N.mukaiSlopeData hμ).rank_nonneg G) with hG | hG
    · have hG0 : V.rank (K₀Ab.of G) = 0 := by exact hG.symm
      have hGmult : P.multiplicity G = 0 := by
        rw [N.multiplicity_eq G, hG0, mul_zero]
      rw [P.weakSlopeData_topSlope_of_multiplicity_pos hμ hFmult,
        (N.mukaiSlopeData hμ).topSlope_of_rank_pos hF,
        P.weakSlopeData_topSlope_of_multiplicity_zero hμ hGmult,
        (N.mukaiSlopeData hμ).topSlope_of_rank_zero hG.symm]
      simp
    · have hGmult : 0 < P.multiplicity G := by
        rw [N.multiplicity_eq G]
        exact mul_pos N.scale_pos hG
      have hFsource : 0 < (P.weakSlopeData hμ).rank F := by
        rw [P.weakSlopeData_rank]
        exact hFmult
      have hGsource : 0 < (P.weakSlopeData hμ).rank G := by
        rw [P.weakSlopeData_rank]
        exact hGmult
      rw [(P.weakSlopeData hμ).topSlope_of_rank_pos hFsource,
        (P.weakSlopeData hμ).topSlope_of_rank_pos hGsource,
        (N.mukaiSlopeData hμ).topSlope_of_rank_pos hF,
        (N.mukaiSlopeData hμ).topSlope_of_rank_pos hG,
        WithTop.coe_le_coe, WithTop.coe_le_coe,
        N.hilbertSlope_eq hμ hF, N.hilbertSlope_eq hμ hG,
        div_le_div_iff_of_pos_right hscaleR]
      constructor <;> intro h <;> linarith

/-- The numerical Mukai slope inherits HN filtrations from Gieseker's
Hilbert-coefficient slope. -/
theorem mukaiSlopeData_hasHNProperty (N : SlopeNormalization P R ω)
    (hμ : MuPositivityData P) (I : MuHNInput P hμ) :
    (N.mukaiSlopeData hμ).toWeakStabilityFunction.HasHNProperty :=
  (N.sameSlopeOrder hμ).hasHNProperty (P.hasHNProperty hμ I)

end SlopeNormalization

/-! ## The standard heart of the bounded derived category -/

/-- The standard t-structure restricted to `Dᵇ(Coh X)`. -/
abbrev boundedStandardT : TStructure (_root_.DerivedCategory.Bounded (Coh X)) :=
  (_root_.DerivedCategory.TStructure.t (C := Coh X)).onBounded

/-- The standard heart of `Dᵇ(Coh X)`. -/
abbrev boundedCohHeart :=
  (boundedStandardT (X := X)).heart.FullSubcategory

namespace SlopeNormalization

variable {P : PolarizedVarietyData k X}
variable {R : Numerical.Surface.NumericalRealization V.ring (D := W)}
variable {ω : W}

/-- The numerical Mukai slope transported from coherent sheaves to the
standard heart of `Dᵇ(Coh X)`. -/
def boundedMukaiSlopeData (N : SlopeNormalization P R ω)
    (hμ : MuPositivityData P) : WeakSlopeData (boundedCohHeart (X := X)) :=
  (N.mukaiSlopeData hμ).congr
    (_root_.DerivedCategory.boundedHeartEquivalence (Coh X))

/-- The bounded-heart numerical slope has the HN property. -/
theorem boundedMukaiSlopeData_hasHNProperty
    (N : SlopeNormalization P R ω) (hμ : MuPositivityData P)
    (I : MuHNInput P hμ) :
    (N.boundedMukaiSlopeData hμ).toWeakStabilityFunction.HasHNProperty :=
  WeakSlopeData.congr_hasHNProperty _ _ (N.mukaiSlopeData_hasHNProperty hμ I)

end SlopeNormalization

/-! ## The real Mukai class and its ambient realization -/

variable (R : Numerical.Surface.NumericalRealization V.ring (D := W))

/-- The real Mukai class of coherent sheaves supplied by the numerical
surface realization. -/
def coherentMukaiClass : K₀Ab (Coh X) →+ Mukai.RealExtension W :=
  R.chernCharacter.mukaiVector R.divisorSpace (R.sqrtTodd (V := V))

@[simp]
theorem coherentMukaiClass_apply (x : K₀Ab (Coh X)) :
    coherentMukaiClass R x =
      R.chernCharacter.mukaiVector R.divisorSpace (R.sqrtTodd (V := V)) x := rfl

/-- The coherent Mukai class transported to the standard bounded heart. -/
def boundedHeartMukaiClass :
    K₀Ab (boundedCohHeart (X := X)) →+ Mukai.RealExtension W :=
  (coherentMukaiClass R).comp
    (K₀Ab.congr (_root_.DerivedCategory.boundedHeartEquivalence (Coh X))).symm.toAddMonoidHom

@[simp]
theorem boundedHeartMukaiClass_of (E : boundedCohHeart (X := X)) :
    boundedHeartMukaiClass R (K₀Ab.of E) =
      coherentMukaiClass R (K₀Ab.of
        ((_root_.DerivedCategory.boundedHeartEquivalence (Coh X)).inverse.obj E)) := by
  simp [boundedHeartMukaiClass]

/-- An ambient Mukai class on `K₀(Dᵇ(Coh X))` realizes the geometric class
when its restriction to the standard heart is the transported coherent-sheaf
class.  The equality stays explicit because only the forward heart-to-ambient
Grothendieck map is currently available. -/
def IsAmbientMukaiClass
    (m : K₀ (_root_.DerivedCategory.Bounded (Coh X)) →+ Mukai.RealExtension W) : Prop :=
  m.comp (K₀Ab.toAmbient (boundedStandardT (X := X))) = boundedHeartMukaiClass R

namespace SlopeNormalization

variable {P : PolarizedVarietyData k X}
variable {R : Numerical.Surface.NumericalRealization V.ring (D := W)}
variable {ω : W}

/-- On a numerical K3, the ambient geometric Mukai class computes the rank
and divisor degree of the bounded-heart normalized slope. -/
theorem mukaiWeakSlopeCompat
    (N : SlopeNormalization P R ω) (hμ : MuPositivityData P)
    (hK3 : Numerical.K3.IsK3 V)
    (m : K₀ (_root_.DerivedCategory.Bounded (Coh X)) →+ Mukai.RealExtension W)
    (hm : IsAmbientMukaiClass R m) :
    MukaiWeakSlopeCompat
      (MukaiChargeData.ofAmbient (boundedStandardT (X := X)) m)
      (N.boundedMukaiSlopeData hμ) R.divisorSpace.intersection ω where
  rank_eq E := by
    change ((m.comp (K₀Ab.toAmbient (boundedStandardT (X := X))))
      (K₀Ab.of E)).1 = _
    rw [hm, boundedHeartMukaiClass_of, coherentMukaiClass_apply,
      R.mukaiVector_of_isK3 hK3]
    exact congrArg (fun z : ℤ => (z : ℝ))
      (WeakSlopeData.congr_rank
        (N.mukaiSlopeData hμ)
        (_root_.DerivedCategory.boundedHeartEquivalence (Coh X)) E).symm
  degree_eq E := by
    change R.divisorSpace.pair ω
      ((m.comp (K₀Ab.toAmbient (boundedStandardT (X := X))))
        (K₀Ab.of E)).2.1 = _
    rw [hm, boundedHeartMukaiClass_of, coherentMukaiClass_apply,
      R.mukaiVector_of_isK3 hK3]
    exact (WeakSlopeData.congr_degree
      (N.mukaiSlopeData hμ)
      (_root_.DerivedCategory.boundedHeartEquivalence (Coh X)) E).symm

end SlopeNormalization

/-! ## The remaining sheaf-level geometric classification -/

/-- The dimension-zero Mukai-class statement at the coherent-sheaf level.

This is the honest geometric gap: the repository does not yet have a theory
of support dimension and length from which to prove it.  Naming it here avoids
replacing that missing theorem by a manufactured heart-level witness. -/
def HasDimensionZeroMukaiClasses (ω : W) : Prop :=
  ∀ F : Coh X, ¬IsZero F →
    V.rank (K₀Ab.of F) = 0 →
    R.divisorSpace.pair ω (R.chernCharacter.chOne (K₀Ab.of F)) = 0 →
    ∃ s : ℝ, 0 < s ∧ coherentMukaiClass R (K₀Ab.of F) = ((0 : ℝ), (0 : W), s)

namespace SlopeNormalization

variable {P : PolarizedVarietyData k X}
variable {R : Numerical.Surface.NumericalRealization V.ring (D := W)}
variable {ω : W}

/-- A coherent-sheaf dimension-zero classification supplies exactly the
abstract torsion-boundary input required by the Mukai tilt argument. -/
theorem hasDimensionZeroTorsionClasses
    (N : SlopeNormalization P R ω) (hμ : MuPositivityData P)
    (m : K₀ (_root_.DerivedCategory.Bounded (Coh X)) →+ Mukai.RealExtension W)
    (hm : IsAmbientMukaiClass R m)
    (hzero : HasDimensionZeroMukaiClasses R ω)
    (β : W) :
    MukaiTilt.HasDimensionZeroTorsionClasses m R.divisorSpace.intersection β ω
      (N.boundedMukaiSlopeData hμ) := by
  intro T₀ hT₀ _hT hrank hdegree
  let e := _root_.DerivedCategory.boundedHeartEquivalence (Coh X)
  let F : Coh X := e.inverse.obj T₀
  have hF : ¬IsZero F := not_isZero_inverse_obj e hT₀
  have hrankF : V.rank (K₀Ab.of F) = 0 := by
    change (N.mukaiSlopeData hμ).rank F = 0
    rw [← WeakSlopeData.congr_rank (N.mukaiSlopeData hμ) e T₀]
    exact hrank
  have hdegreeF :
      R.divisorSpace.pair ω (R.chernCharacter.chOne (K₀Ab.of F)) = 0 := by
    change (N.mukaiSlopeData hμ).degree F = 0
    rw [← WeakSlopeData.congr_degree (N.mukaiSlopeData hμ) e T₀]
    exact hdegree
  obtain ⟨s, hs, hclass⟩ := hzero F hF hrankF hdegreeF
  refine ⟨s, hs, ?_⟩
  change (m.comp (K₀Ab.toAmbient (boundedStandardT (X := X)))) (K₀Ab.of T₀) = _
  rw [hm, boundedHeartMukaiClass_of]
  exact hclass

end SlopeNormalization

/-! ## The K3 Mukai tilt stability function -/

namespace SlopeNormalization

variable {P : PolarizedVarietyData k X}
variable {R : Numerical.Surface.NumericalRealization V.ring (D := W)}
variable {β ω : W}
variable [FiniteDimensional ℝ W]
variable [IsNoetherian X]

/-- The exponential Mukai charge as a stability function on the tilted
standard heart of `Dᵇ(Coh X)`.

All formal inputs are discharged here.  The ambient realization equality,
dimension-zero classification, and K3 boundary decomposition remain visible
geometric hypotheses.  The last is the named gap whose missing categorical
ingredients are tracked from issue #332.  The conclusion is only a stability
function; it does not assert the HN property on the tilted heart or package a
full stability condition. -/
def tiltStabilityFunction
    (N : SlopeNormalization P R ω) (hμ : MuPositivityData P)
    (hbounded : SlopeBoundedness P) (hK3 : Numerical.K3.IsK3 V)
    (m : K₀ (_root_.DerivedCategory.Bounded (Coh X)) →+ Mukai.RealExtension W)
    (hm : IsAmbientMukaiClass R m)
    (hHodge : R.divisorSpace.HodgeDefinite ω)
    (hω : 2 < R.divisorSpace.pair ω ω)
    (hzero : HasDimensionZeroMukaiClasses R ω)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition m
      R.divisorSpace.intersection β ω (N.boundedMukaiSlopeData hμ)) :
    WeakStabilityCondition.StabilityFunction
      ((N.boundedMukaiSlopeData hμ).toWeakStabilityFunction.hnTilt
        (((R.divisorSpace.intersection β ω : ℝ)) : WithTop ℝ)
        (N.boundedMukaiSlopeData_hasHNProperty hμ (muHNInput hbounded))) := by
  let hHN := N.boundedMukaiSlopeData_hasHNProperty hμ (muHNInput hbounded)
  exact (N.mukaiWeakSlopeCompat hμ hK3 m hm).tiltStabilityFunction
    (fun x y => R.divisorSpace.pair_comm x y)
    (R.divisorSpace.sigPos_sigNeg_of_hodgeDefinite hHodge).1
    hω hHN (N.hasDimensionZeroTorsionClasses hμ m hm hzero β) hboundary

/-- The assembled stability function uses the original ambient exponential
Mukai charge, with no numerical replacement of the third coordinate. -/
@[simp]
theorem tiltStabilityFunction_Z
    (N : SlopeNormalization P R ω) (hμ : MuPositivityData P)
    (hbounded : SlopeBoundedness P) (hK3 : Numerical.K3.IsK3 V)
    (m : K₀ (_root_.DerivedCategory.Bounded (Coh X)) →+ Mukai.RealExtension W)
    (hm : IsAmbientMukaiClass R m)
    (hHodge : R.divisorSpace.HodgeDefinite ω)
    (hω : 2 < R.divisorSpace.pair ω ω)
    (hzero : HasDimensionZeroMukaiClasses R ω)
    (hboundary : MukaiTilt.HasBoundaryMukaiDecomposition m
      R.divisorSpace.intersection β ω (N.boundedMukaiSlopeData hμ)) :
    (N.tiltStabilityFunction hμ hbounded hK3 m hm hHodge hω hzero hboundary).Z =
      MukaiChargeData.ambientChargeHom m R.divisorSpace.intersection β ω := rfl

end SlopeNormalization

end AlgebraicGeometry.DerivedCategory.Stability.K3MukaiTilt
