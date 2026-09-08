/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.ProjectivePlane
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialCharge
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialChargeNumerical
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialWallSlice
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.SurfaceChargeNumerical
import Mathlib.Data.Fin.VecNotation

/-!
# The projective-plane child of the divisorial surface charge

This file instantiates the intrinsic divisorial surface construction for
`ℙ²`.  Its divisor space is one-dimensional, with the hyperplane class `H`
normalized by `H² = 1`.  Both the explicit projective-family coordinates and
the existing `SurfaceNum` presentation carry a full `Surface.ChernCharacter`,
and their comparison is made before choosing `B` and `omega`.

The older scalar `Surface.ChargeCoordinates` objects are derived compatibility
views.  Thus the projective-plane charge is a child of the same parent as the
smooth-quadric charge, rather than a parent or a separate charge polynomial.

The adapter is still only arithmetic.  It does not claim that the source
carrier is `K₀(ℙ²)`, nor does it provide the geometric family map or the C1/C2
properties needed by the eventual stability comparison.
-/

open Complex
namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

/-! ### The projective-plane divisor space -/

/-- Real numerical divisor classes on `ℙ²`, represented in the hyperplane
basis. -/
abbrev P2Divisor : Type := ℝ

/-- The intersection form in the normalized hyperplane basis. -/
def p2IntersectionForm : LinearMap.BilinForm ℝ P2Divisor :=
  LinearMap.mk₂ ℝ (fun x y => x * y)
    (fun _ _ _ => by ring)
    (fun _ _ _ => by ring)
    (fun _ _ _ => by ring)
    (fun _ _ _ => by ring)

/-- The rank-one numerical divisor space of `ℙ²`. -/
def p2DivisorSpace : Surface.DivisorSpace P2Divisor where
  intersection := p2IntersectionForm
  intersection_symm := ⟨by intro x y; simp [p2IntersectionForm]; ring⟩

/-- The hyperplane generator in the one-dimensional divisor space. -/
def p2Hyperplane : P2Divisor := 1

@[simp]
theorem p2Hyperplane_square :
    p2DivisorSpace.pair p2Hyperplane p2Hyperplane = 1 := by
  norm_num [Surface.DivisorSpace.pair, p2DivisorSpace, p2IntersectionForm,
    p2Hyperplane]

/-! ### The two full Chern-character presentations -/

/-- The integral `(r, c, v)` coordinates used on the projective-family side.

This is intentionally not an alias of `SurfaceNum`: the adapter below must
carry an explicit source-to-target map. -/
abbrev P2ProjectiveCoordinates : Type := ℤ × ℤ × ℤ

/-- The full Chern character on the explicit projective-family coordinates. -/
noncomputable def p2ProjectiveChernCharacter :
    Surface.ChernCharacter P2ProjectiveCoordinates P2Divisor where
  rank := AddMonoidHom.mk' (fun E => (E.1 : ℝ)) (by
    intro E F
    change ((E.1 + F.1 : ℤ) : ℝ) = (E.1 : ℝ) + (F.1 : ℝ)
    push_cast
    rfl)
  chOne := AddMonoidHom.mk' (fun E => (E.2.1 : ℝ)) (by
    intro E F
    change ((E.2.1 + F.2.1 : ℤ) : ℝ) = (E.2.1 : ℝ) + (F.2.1 : ℝ)
    push_cast
    rfl)
  chTwo := AddMonoidHom.mk' (fun E => (E.2.1 : ℝ) / 2 + (E.2.2 : ℝ)) (by
    intro E F
    change ((E.2.1 + F.2.1 : ℤ) : ℝ) / 2 + ((E.2.2 + F.2.2 : ℤ) : ℝ) =
      ((E.2.1 : ℝ) / 2 + (E.2.2 : ℝ)) +
        ((F.2.1 : ℝ) / 2 + (F.2.2 : ℝ))
    push_cast
    ring)

/-- The old scalar-coordinate view, derived from the full character at `H`. -/
noncomputable def p2ProjectiveChargeCoordinates :
    Surface.ChargeCoordinates P2ProjectiveCoordinates :=
  p2ProjectiveChernCharacter.coordinatesAt p2DivisorSpace p2Hyperplane

/-- The source rank coordinate is the first projective triple entry. -/
@[simp]
theorem p2ProjectiveChargeCoordinates_rank (E : P2ProjectiveCoordinates) :
    p2ProjectiveChargeCoordinates.rank E = (E.1 : ℝ) := by
  rfl

/-- The source degree coordinate is the second projective triple entry. -/
@[simp]
theorem p2ProjectiveChargeCoordinates_degree (E : P2ProjectiveCoordinates) :
    p2ProjectiveChargeCoordinates.degree E = (E.2.1 : ℝ) := by
  simp [p2ProjectiveChargeCoordinates, p2ProjectiveChernCharacter,
    p2DivisorSpace, p2IntersectionForm, p2Hyperplane, Surface.DivisorSpace.pair]

/-- The source `ch₂` coordinate is `c/2 + v`. -/
@[simp]
theorem p2ProjectiveChargeCoordinates_chTwo (E : P2ProjectiveCoordinates) :
    p2ProjectiveChargeCoordinates.chTwo E = (E.2.1 : ℝ) / 2 + (E.2.2 : ℝ) := by
  rfl

/-- The projective-plane source uses the normalization `H² = 1`. -/
@[simp]
theorem p2ProjectiveChargeCoordinates_hyperplaneSquare :
    p2ProjectiveChargeCoordinates.hyperplaneSquare = 1 := by
  exact p2Hyperplane_square

/-- The hyperplane class as the polarisation used by the `ℙ²` surface model. -/
noncomputable def p2Polarization : Polarization p2NumericalVariety.ring where
  cls := H
  cls_mem := H_mem_piece_one
  degree_pow_pos := by
    change 0 < surfaceDegree 1 (H ^ 2)
    rw [surfaceDegree_Hsq]
    norm_num

/-- The projective-plane `B`-field `B = βH` in the rational numerical ring.

Every rational numerical divisor class on this rank-one model has this form.
The real scalar API below extends the same coordinate formula to real `b`. -/
noncomputable def p2BField (β : ℚ) : BField p2NumericalVariety.ring :=
  BField.along p2Polarization β

/-- The named projective-plane `B`-field evaluates to `βH`. -/
@[simp]
theorem p2BField_cls (β : ℚ) :
    (p2BField β).cls = algebraMap ℚ SurfaceRing β * H := rfl

/-! ### Real realization of the rational divisor piece -/

/-- The unique basis index of codimension one in the rank-one surface ring. -/
def p2DivisorIndex : Fin surfacePB.dim :=
  ⟨1, by rw [surfacePB_dim]; norm_num⟩

/-- The weight-one basis vectors are exactly the singleton `H`. -/
theorem surfaceWeightOneBasis :
    surfacePB.basis '' (surfaceW ⁻¹' ({1} : Set ℕ)) = ({H} : Set SurfaceRing) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
    have hindex : i = p2DivisorIndex := Fin.ext hi
    rw [hindex, surfacePB_basis_apply]
    simp [p2DivisorIndex]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨p2DivisorIndex, ?_, ?_⟩
    · simp [surfaceW, p2DivisorIndex]
    · rw [surfacePB_basis_apply]
      simp [p2DivisorIndex]

/-- The codimension-one graded piece of the projective-plane ring is the
one-dimensional span of `H`. -/
theorem surfacePieceOne_eq_span_H :
    p2NumericalVariety.ring.piece 1 = Submodule.span ℚ ({H} : Set SurfaceRing) := by
  change DerivedAlgGeo.LinearAlgebra.gradedPiece
    (surfacePB.basis : Fin surfacePB.dim → SurfaceRing) surfaceW 1 = _
  rw [DerivedAlgGeo.LinearAlgebra.gradedPiece, surfaceWeightOneBasis]

/-- Realize a rational divisor class by its coefficient in the hyperplane
basis, computed invariantly as `∫xH` using `H² = 1`. -/
noncomputable def p2DivisorClass : p2NumericalVariety.ring.piece 1 →+ P2Divisor :=
  AddMonoidHom.mk'
    (fun x => ((p2NumericalVariety.ring.degree (x.1 * H) : ℚ) : ℝ))
    (by
      intro x y
      change (((p2NumericalVariety.ring.degree ((x.1 + y.1) * H) : ℚ) : ℝ)) = _
      rw [add_mul, map_add]
      push_cast
      rfl)

/-- The hyperplane-coefficient realization respects rational scalar
extension. -/
theorem p2DivisorClass_map_rat_smul
    (q : ℚ) (x : p2NumericalVariety.ring.piece 1) :
    p2DivisorClass (q • x) = (q : ℝ) • p2DivisorClass x := by
  change (((p2NumericalVariety.ring.degree ((q • x.1) * H) : ℚ) : ℝ)) = _
  rw [Algebra.smul_def, mul_assoc,
    NumericalRingData.degree_algebraMap_mul]
  push_cast
  rfl

/-- On the codimension-one piece, multiplication followed by degree is the
ordinary product of realized hyperplane coefficients. -/
theorem p2DivisorClass_intersection
    (x y : p2NumericalVariety.ring.piece 1) :
    p2DivisorSpace.pair (p2DivisorClass x) (p2DivisorClass y) =
      ((p2NumericalVariety.ring.degree (x.1 * y.1) : ℚ) : ℝ) := by
  have hx : x.1 ∈ Submodule.span ℚ ({H} : Set SurfaceRing) := by
    rw [← surfacePieceOne_eq_span_H]
    exact x.2
  have hy : y.1 ∈ Submodule.span ℚ ({H} : Set SurfaceRing) := by
    rw [← surfacePieceOne_eq_span_H]
    exact y.2
  obtain ⟨qx, hqx⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨qy, hqy⟩ := Submodule.mem_span_singleton.mp hy
  have hclassx : p2DivisorClass x = (qx : ℝ) := by
    change (((surfaceDegree 1 (x.1 * H) : ℚ) : ℝ)) = _
    rw [← hqx, Algebra.smul_def, mul_assoc,
      surfaceDegree_algebraMap_mul, ← pow_two, surfaceDegree_Hsq]
    push_cast
    ring
  have hclassy : p2DivisorClass y = (qy : ℝ) := by
    change (((surfaceDegree 1 (y.1 * H) : ℚ) : ℝ)) = _
    rw [← hqy, Algebra.smul_def, mul_assoc,
      surfaceDegree_algebraMap_mul, ← pow_two, surfaceDegree_Hsq]
    push_cast
    ring
  rw [hclassx, hclassy]
  change (qx : ℝ) * (qy : ℝ) = _
  rw [← hqx, ← hqy]
  have hproduct :
      (qx • H) * (qy • H) =
        algebraMap ℚ SurfaceRing (qx * qy) * H ^ 2 := by
    simp [Algebra.smul_def, map_mul]
    ring
  rw [hproduct, surfaceDegree_algebraMap_mul, surfaceDegree_Hsq]
  push_cast
  ring

/-- The projective-plane numerical ring realized in `N¹(P²)_ℝ`. -/
noncomputable def p2NumericalRealization :
    Surface.NumericalRealization p2NumericalVariety.ring (D := P2Divisor) where
  divisorSpace := p2DivisorSpace
  divisorClass := p2DivisorClass
  map_rat_smul := p2DivisorClass_map_rat_smul
  intersection_eq := p2DivisorClass_intersection

@[simp]
theorem p2NumericalRealization_divisorSpace :
    p2NumericalRealization.divisorSpace = p2DivisorSpace := rfl

/-- The rational hyperplane realizes to the chosen real hyperplane. -/
@[simp]
theorem p2NumericalRealization_polarization :
    p2NumericalRealization.realizePolarization p2Polarization = p2Hyperplane := by
  change (((surfaceDegree 1 (H * H) : ℚ) : ℝ)) = 1
  rw [← pow_two, surfaceDegree_Hsq]
  norm_num

/-- The rational field `βH` realizes to the real divisor `βH`. -/
@[simp]
theorem p2NumericalRealization_BField (β : ℚ) :
    p2NumericalRealization.realizeBField (p2BField β) =
      (β : ℝ) • p2Hyperplane := by
  change (((surfaceDegree 1 ((algebraMap ℚ SurfaceRing β * H) * H) : ℚ) : ℝ)) = _
  rw [mul_assoc, ← pow_two, surfaceDegree_algebraMap_mul, surfaceDegree_Hsq]
  push_cast
  simp [p2Hyperplane]

/-- The surface-side charge coordinates induced by the numerical presentation. -/
noncomputable def p2SurfaceChargeCoordinates :
    Surface.ChargeCoordinates SurfaceNum :=
  Surface.ChargeCoordinates.ofNumericalData p2NumericalVariety p2Polarization

/-- The full Chern character on the existing surface numerical presentation.

Because `N¹(ℙ²)_ℝ = ℝH` and `H² = 1`, the old `H`-degree is exactly the
coefficient of the full first Chern class. -/
noncomputable def p2SurfaceChernCharacter :
    Surface.ChernCharacter SurfaceNum P2Divisor :=
  p2NumericalRealization.chernCharacter

/-! ### The explicit numerical comparison map -/

/-- The source-to-target additive map sending `(r, c, v)` to `![r, c, v]`. -/
def p2ProjectiveToSurface : P2ProjectiveCoordinates →+ SurfaceNum :=
  AddMonoidHom.mk'
    (fun E => ![E.1, E.2.1, E.2.2])
    (by
      intro E F
      funext i
      fin_cases i <;> rfl)

/-- The target rank coordinate is the first `SurfaceNum` entry. -/
@[simp]
theorem p2SurfaceChargeCoordinates_rank (E : SurfaceNum) :
    p2SurfaceChargeCoordinates.rank E = (E 0 : ℝ) := by
  change ((p2NumericalVariety.rank E : ℤ) : ℝ) = (E 0 : ℝ)
  rfl

/-- The target polarised degree is the second `SurfaceNum` entry. -/
@[simp]
theorem p2SurfaceChargeCoordinates_degree (E : SurfaceNum) :
    p2SurfaceChargeCoordinates.degree E = (E 1 : ℝ) := by
  change (((surfaceNumericalRing 1).degree
      (algebraMap ℚ SurfaceRing (p2ChCoeff E 1) * H * H ^ 1) : ℚ) : ℝ) = _
  rw [pow_one, mul_assoc, ← pow_two,
    NumericalRingData.degree_algebraMap_mul, surfaceDegree_Hsq]
  simp [p2ChCoeff]

/-- The target integrated `ch₂` is the projective `c/2 + v` coordinate. -/
@[simp]
theorem p2SurfaceChargeCoordinates_chTwo (E : SurfaceNum) :
    p2SurfaceChargeCoordinates.chTwo E = (E 1 : ℝ) / 2 + (E 2 : ℝ) := by
  change (((surfaceNumericalRing 1).degree
      (algebraMap ℚ SurfaceRing (p2ChCoeff E 2) * H ^ 2) : ℚ) : ℝ) = _
  rw [NumericalRingData.degree_algebraMap_mul, surfaceDegree_Hsq]
  simp [p2ChCoeff]

/-- The chosen target polarisation has square one. -/
@[simp]
theorem p2SurfaceChargeCoordinates_hyperplaneSquare :
    p2SurfaceChargeCoordinates.hyperplaneSquare = 1 := by
  change (((surfaceNumericalRing 1).degree (H ^ 2) : ℚ) : ℝ) = 1
  rw [surfaceDegree_Hsq]
  norm_num

/-- The realized surface rank is the first numerical coordinate. -/
@[simp]
theorem p2SurfaceChernCharacter_rank (E : SurfaceNum) :
    p2SurfaceChernCharacter.rank E = (E 0 : ℝ) := by
  rfl

/-- The realized full first Chern class is its hyperplane coefficient. -/
@[simp]
theorem p2SurfaceChernCharacter_chOne (E : SurfaceNum) :
    p2SurfaceChernCharacter.chOne E = (E 1 : ℝ) := by
  change (((surfaceDegree 1
    ((algebraMap ℚ SurfaceRing (p2ChCoeff E 1) * H) * H) : ℚ) : ℝ)) = _
  rw [mul_assoc, ← pow_two, surfaceDegree_algebraMap_mul, surfaceDegree_Hsq]
  simp [p2ChCoeff]

/-- The realized integrated second Chern character is unchanged. -/
@[simp]
theorem p2SurfaceChernCharacter_chTwo (E : SurfaceNum) :
    p2SurfaceChernCharacter.chTwo E = (E 1 : ℝ) / 2 + (E 2 : ℝ) := by
  exact p2SurfaceChargeCoordinates_chTwo E

/-- The two presentations preserve the full Chern character, before any
choice of `B`-field or ample class.  Consequently this one witness compares
all projective-plane divisorial charges. -/
noncomputable def p2ChernCharacterPullback :
    Surface.ChernCharacter.Pullback
      p2ProjectiveChernCharacter p2SurfaceChernCharacter where
  map := p2ProjectiveToSurface
  rank_eq := by
    intro E
    change (E.1 : ℝ) =
      p2SurfaceChernCharacter.rank (p2ProjectiveToSurface E)
    rw [p2SurfaceChernCharacter_rank]
    rfl
  chOne_eq := by
    intro E
    change (E.2.1 : ℝ) =
      p2SurfaceChernCharacter.chOne (p2ProjectiveToSurface E)
    rw [p2SurfaceChernCharacter_chOne]
    rfl
  chTwo_eq := by
    intro E
    change (E.2.1 : ℝ) / 2 + (E.2.2 : ℝ) =
      p2SurfaceChernCharacter.chTwo (p2ProjectiveToSurface E)
    rw [p2SurfaceChernCharacter_chTwo]
    rfl

/-- The coordinates derived from the full surface character agree with the
legacy numerical coordinates.  This bridge exists only because `H² = 1` on
the chosen rank-one basis. -/
noncomputable def p2SurfaceCoordinatesPullback :
    Surface.ChargeCoordinates.Pullback
      (p2SurfaceChernCharacter.coordinatesAt p2DivisorSpace p2Hyperplane)
      p2SurfaceChargeCoordinates where
  map := AddMonoidHom.id SurfaceNum
  rank_eq := by
    intro E
    rfl
  degree_eq := by
    intro E
    rw [Surface.ChernCharacter.coordinatesAt_degree,
      p2SurfaceChernCharacter_chOne, p2SurfaceChargeCoordinates_degree]
    simp [p2DivisorSpace, p2IntersectionForm, p2Hyperplane,
      Surface.DivisorSpace.pair]
  chTwo_eq := by
    intro E
    rfl
  hyperplaneSquare_eq := by
    rw [Surface.ChernCharacter.coordinatesAt_hyperplaneSquare,
      p2Hyperplane_square, p2SurfaceChargeCoordinates_hyperplaneSquare]

/-- The full-character comparison induces the legacy scalar-coordinate
comparison at the projective hyperplane. -/
noncomputable def p2ChargePullback :
    Surface.ChargeCoordinates.Pullback
      p2ProjectiveChargeCoordinates p2SurfaceChargeCoordinates where
  map := p2ProjectiveToSurface
  rank_eq := by
    intro E
    rw [p2ProjectiveChargeCoordinates_rank, p2SurfaceChargeCoordinates_rank]
    rfl
  degree_eq := by
    intro E
    rw [p2ProjectiveChargeCoordinates_degree, p2SurfaceChargeCoordinates_degree]
    rfl
  chTwo_eq := by
    intro E
    rw [p2ProjectiveChargeCoordinates_chTwo, p2SurfaceChargeCoordinates_chTwo]
    rfl
  hyperplaneSquare_eq := by
    rw [p2ProjectiveChargeCoordinates_hyperplaneSquare,
      p2SurfaceChargeCoordinates_hyperplaneSquare]

/-! ### The two presentations of the same charge -/

/-- The projective-plane rank-one family `B = bH`, `omega = aH`, obtained as
a specialization of the parent parameter space. -/
def p2Parameters (a b : ℝ) : Surface.StabilityParameters P2Divisor :=
  Surface.StabilityParameters.rankOne p2Hyperplane a b

/-- Li's projective-space charge on the `(r, c, v)` carrier, instantiated from
the intrinsic divisorial parent. -/
noncomputable def p2ProjectiveCharge (a b : ℝ) :
    P2ProjectiveCoordinates →+ ℂ :=
  p2ProjectiveChernCharacter.centralCharge p2DivisorSpace (p2Parameters a b)

/-- The same parent charge on the existing `SurfaceNum` presentation. -/
noncomputable def p2SurfaceCharge (a b : ℝ) :
    SurfaceNum →+ ℂ :=
  p2SurfaceChernCharacter.centralCharge p2DivisorSpace (p2Parameters a b)

/-! ### The inherited rank-one wall slice -/

/-- The projective-plane wall slice has no transverse directions. -/
def p2WallSlice :
    Surface.OrthogonalSlice p2DivisorSpace (Fin 0 → ℝ) :=
  Surface.OrthogonalSlice.rankOne p2DivisorSpace p2Hyperplane

/-- The projective-coordinate charge as a child of the generic wall-family
and orthogonal-slice layers. -/
def p2ProjectiveWallFamily :
    CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily
      (Surface.OrthogonalSlice.Point (Fin 0 → ℝ)) P2ProjectiveCoordinates :=
  p2WallSlice.chargeFamily p2ProjectiveChernCharacter

/-- Evaluating the inherited rank-one family recovers the existing
projective-plane charge. -/
@[simp]
theorem p2ProjectiveWallFamily_charge (a b : ℝ)
    (E : P2ProjectiveCoordinates) :
    p2ProjectiveWallFamily.charge
        (Surface.OrthogonalSlice.Point.rankOne b a) E =
      p2ProjectiveCharge a b E := by
  rw [p2ProjectiveCharge]
  have hparameters :
      p2WallSlice.parameters (Surface.OrthogonalSlice.Point.rankOne b a) =
        p2Parameters a b := by
    apply congrArg₂ Surface.StabilityParameters.mk
    · change b • p2Hyperplane + 0 = b • p2Hyperplane
      simp
    · rfl
  change p2ProjectiveChernCharacter.centralCharge p2DivisorSpace
      (p2WallSlice.parameters (Surface.OrthogonalSlice.Point.rankOne b a)) E = _
  rw [hparameters]

/-- The projective charge respects the additive zero class. -/
@[simp]
theorem p2ProjectiveCharge_zero (a b : ℝ) :
    p2ProjectiveCharge a b 0 = 0 :=
  (p2ProjectiveCharge a b).map_zero

/-- The surface charge respects the additive zero class. -/
@[simp]
theorem p2SurfaceCharge_zero (a b : ℝ) :
    p2SurfaceCharge a b 0 = 0 :=
  (p2SurfaceCharge a b).map_zero

/-- For rational `β`, the real scalar presentation is exactly the charge
built from the general twisted Chern character at `B = βH`. -/
theorem p2SurfaceCharge_eq_BFieldCharge (a : ℝ) (β : ℚ) (E : SurfaceNum) :
    p2SurfaceCharge a (β : ℝ) E =
      (Surface.ChargeCoordinates.ofNumericalDataB
        p2NumericalVariety p2Polarization (p2BField β)).centralCharge a E := by
  simpa [p2SurfaceCharge, p2SurfaceChernCharacter, p2Parameters,
    Surface.NumericalRealization.parameters, Surface.StabilityParameters.rankOne] using
    (Surface.NumericalRealization.centralCharge_eq_ofNumericalDataB
      p2NumericalRealization p2Polarization (p2BField β) a E)

/-- Li's charge is the standard surface charge under the identity parameter map.

The only nontrivial map here is the explicit map between the two numerical
class presentations. -/
theorem p2ProjectiveCharge_eq_surfaceCharge (a b : ℝ)
    (E : P2ProjectiveCoordinates) :
    p2ProjectiveCharge a b E =
      p2SurfaceCharge a b (p2ProjectiveToSurface E) := by
  simpa [p2ProjectiveCharge, p2SurfaceCharge, p2ChernCharacterPullback] using
    (Surface.ChernCharacter.Pullback.centralCharge_eq
      p2ChernCharacterPullback p2DivisorSpace (p2Parameters a b) E)

/-- Li's exponential notation expanded in the projective `(r,c,v)` coordinates. -/
@[simp]
theorem p2ProjectiveCharge_apply (a b : ℝ) (E : P2ProjectiveCoordinates) :
    p2ProjectiveCharge a b E =
      -Complex.ofReal ((E.2.1 : ℝ) / 2 + (E.2.2 : ℝ))
        + (b + a * Complex.I) * Complex.ofReal (E.2.1 : ℝ)
        - (b + a * Complex.I) ^ 2 * Complex.ofReal ((E.1 : ℝ) / 2) := by
  calc
    p2ProjectiveCharge a b E =
        (p2ProjectiveChargeCoordinates.twistByScalar b).centralCharge a E := by
      simpa [p2ProjectiveCharge, p2Parameters, p2ProjectiveChargeCoordinates] using
        (Surface.ChernCharacter.centralCharge_rankOne_eq p2ProjectiveChernCharacter
          p2DivisorSpace p2Hyperplane a b E)
    _ = _ := by
      rw [Surface.ChargeCoordinates.centralCharge_twistByScalar_apply]
      simp

/-! ### Coordinate formulas -/

/-- The real part of the projective-plane charge in `(r, c, v)` coordinates. -/
theorem p2ProjectiveCharge_re (a b : ℝ) (E : P2ProjectiveCoordinates) :
    (p2ProjectiveCharge a b E).re =
      -((E.2.1 : ℝ) / 2 + (E.2.2 : ℝ))
        + b * (E.2.1 : ℝ)
        + (a ^ 2 - b ^ 2) * ((E.1 : ℝ) / 2) := by
  rw [p2ProjectiveCharge_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, pow_two]
  ring

/-- The imaginary part of the projective-plane charge in `(r, c, v)` coordinates. -/
theorem p2ProjectiveCharge_im (a b : ℝ) (E : P2ProjectiveCoordinates) :
    (p2ProjectiveCharge a b E).im =
      a * (E.2.1 : ℝ) - (2 * a * b) * ((E.1 : ℝ) / 2) := by
  rw [p2ProjectiveCharge_apply]
  simp only [Complex.sub_im, Complex.add_im, Complex.neg_im,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, pow_two]
  ring

end

end Examples

end AlgebraicGeometry.Numerical
