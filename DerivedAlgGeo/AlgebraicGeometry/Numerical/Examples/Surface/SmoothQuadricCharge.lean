/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.SmoothQuadric
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialChargeScalarExtension
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialWallSlice

/-!
# The divisorial central charge on a smooth quadric surface

Over an algebraically closed field, the smooth quadric surface is
`Q = P^1 x P^1`.  Its real numerical divisor space has basis given by the two
rulings `f₁, f₂`, with

`f₁^2 = f₂^2 = 0`, `f₁.f₂ = 1`.

This is the first example in which a scalar field `B = beta H` is not the
intrinsic parameter.  We model

`H = h₁ f₁ + h₂ f₂`, `B = b₁ f₁ + b₂ f₂`

independently and recover the explicit rank-two formula.  The ample cone is
recorded separately as `h₁ > 0` and `h₂ > 0`, while the arithmetic central
charge itself remains defined for every pair of real classes.

The numerical carrier uses coordinates `(r, c, d, v)` for
`ch(E) = (r, c f₁ + d f₂, v)`.  Its real Chern character is induced from the
rational graded ring through `Surface.NumericalRealization`, so this charge is
a child of the general divisorial construction rather than an independent
coordinate polynomial.
-/

open Complex
open scoped TensorProduct

namespace AlgebraicGeometry.Numerical.Examples.SmoothQuadric

open Surface

noncomputable section

/-- Independent real parameters in the ruling basis. -/
def parameters (h₁ h₂ b₁ b₂ : ℝ) : Surface.StabilityParameters Divisor where
  B := (b₁, b₂)
  omega := (h₁, h₂)

/-! ### The arbitrary real scalar-extension presentation -/

/-- A real divisor class in the rational ruling basis, regarded as an element
of `ℝ ⊗[ℚ] A¹(Q)_ℚ`. -/
def scalarExtendedDivisor (x y : ℝ) :
    Surface.RealDivisorClass numericalRing :=
  x ⊗ₜ[ℚ] (⟨rulingOneQ, rulingOneQ_mem⟩ : numericalRing.piece 1) +
    y ⊗ₜ[ℚ] (⟨rulingTwoQ, rulingTwoQ_mem⟩ : numericalRing.piece 1)

/-- The scalar-extended ruling coordinates realize to the corresponding
arbitrary real class in `N¹(Q)_ℝ`. -/
@[simp]
theorem realize_scalarExtendedDivisor (x y : ℝ) :
    numericalRealization.extendDivisorClass (scalarExtendedDivisor x y) =
      (x, y) := by
  rw [scalarExtendedDivisor, map_add]
  rw [Surface.NumericalRealization.extendDivisorClass_tmul,
    Surface.NumericalRealization.extendDivisorClass_tmul]
  ext <;> simp [numericalRealization, divisorClass, rulingOneQ, rulingTwoQ]

/-- The scalar-extension realization reaches every real divisor class on the
smooth quadric. -/
theorem extendDivisorClass_surjective :
    Function.Surjective numericalRealization.extendDivisorClass := by
  intro x
  exact ⟨scalarExtendedDivisor x.1 x.2, by
    simpa using realize_scalarExtendedDivisor x.1 x.2⟩

/-- Independent real `B` and `omega` in the scalar extension of the quadric's
rational numerical ring. -/
def scalarExtendedParameters (h₁ h₂ b₁ b₂ : ℝ) :
    Surface.StabilityParameters (Surface.RealDivisorClass numericalRing) where
  B := scalarExtendedDivisor b₁ b₂
  omega := scalarExtendedDivisor h₁ h₂

/-- Realizing scalar-extended parameters recovers the intrinsic ruling
coordinates. -/
@[simp]
theorem realize_scalarExtendedParameters (h₁ h₂ b₁ b₂ : ℝ) :
    numericalRealization.realizeParameters
        (scalarExtendedParameters h₁ h₂ b₁ b₂) =
      parameters h₁ h₂ b₁ b₂ := by
  apply congrArg₂ Surface.StabilityParameters.mk
  · exact realize_scalarExtendedDivisor b₁ b₂
  · exact realize_scalarExtendedDivisor h₁ h₂

/-- The smooth-quadric child of the intrinsic divisorial central charge. -/
noncomputable def charge (h₁ h₂ b₁ b₂ : ℝ) : NumericalClass →+ ℂ :=
  chernCharacter.centralCharge divisorSpace (parameters h₁ h₂ b₁ b₂)

/-- The coordinate charge is exactly the canonical scalar-extension charge
for every real pair `B = (b₁,b₂)` and `omega = (h₁,h₂)`.  Unlike the rational
compatibility theorem below, this statement loses no real divisor classes. -/
theorem charge_eq_scalarExtension
    (h₁ h₂ b₁ b₂ : ℝ) (E : NumericalClass) :
    charge h₁ h₂ b₁ b₂ E =
      (Surface.ScalarExtension.chernCharacter (V := numericalVariety)).centralCharge
        (Surface.RealDivisorClass.divisorSpace numericalRing)
        (scalarExtendedParameters h₁ h₂ b₁ b₂) E := by
  rw [charge]
  symm
  change
    (Surface.ScalarExtension.chernCharacter (V := numericalVariety)).centralCharge
        (Surface.RealDivisorClass.divisorSpace numericalRing)
        (scalarExtendedParameters h₁ h₂ b₁ b₂) E =
      numericalRealization.chernCharacter.centralCharge
        numericalRealization.divisorSpace (parameters h₁ h₂ b₁ b₂) E
  simpa only [realize_scalarExtendedParameters] using
    (Surface.ScalarExtension.centralCharge_eq_realization numericalRealization
      (scalarExtendedParameters h₁ h₂ b₁ b₂) E)

/-- The ample cone of the smooth quadric in ruling coordinates. -/
def ampleCone : Set Divisor := {H | 0 < H.1 ∧ 0 < H.2}

/-- Bundle the geometric ampleness side condition without changing the charge
arithmetic. -/
def divisorialParameters (h₁ h₂ b₁ b₂ : ℝ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    Surface.DivisorialParameters ampleCone where
  B := (b₁, b₂)
  omega := (h₁, h₂)
  omega_ample := ⟨hh₁, hh₂⟩

/-- The polarization square is `2 h₁ h₂`. -/
theorem omega_square (h₁ h₂ : ℝ) :
    divisorSpace.pair (h₁, h₂) (h₁, h₂) = 2 * h₁ * h₂ := by
  simp [Surface.DivisorSpace.pair, divisorSpace, intersectionForm]
  ring

/-- An ample class on the smooth quadric has positive square.  This is a
derived fact in the example, not the definition of ampleness in the core API. -/
theorem omega_square_pos {h₁ h₂ : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) :
    0 < divisorSpace.pair (h₁, h₂) (h₁, h₂) := by
  rw [omega_square]
  positivity

/-- Explicit central charge for a smooth quadric in the ruling basis.

For `ch(E) = (r, c f₁ + d f₂, v)`, the real and imaginary parts are

`-v + b₁d + b₂c + (h₁h₂-b₁b₂)r`,
`h₁d + h₂c - (h₁b₂+h₂b₁)r`.
-/
theorem centralCharge_apply (h₁ h₂ b₁ b₂ : ℝ) (r c d v : ℤ) :
    charge h₁ h₂ b₁ b₂ (r, c, d, v) =
      Complex.ofReal
          (-(v : ℝ) + b₁ * d + b₂ * c + (h₁ * h₂ - b₁ * b₂) * r)
        + Complex.I * Complex.ofReal
          (h₁ * d + h₂ * c - (h₁ * b₂ + h₂ * b₁) * r) := by
  rw [charge, Surface.ChernCharacter.centralCharge_apply]
  simp only [chernCharacter_rank, chernCharacter_chOne, chernCharacter_chTwo]
  simp [parameters, divisorSpace, intersectionForm,
    Surface.DivisorSpace.pair]
  ring

/-- The intrinsic real charge agrees with the generic numerical-ring charge
for arbitrary rational ample polarization and arbitrary rational `B`-field. -/
theorem charge_eq_numericalBField
    (a : ℝ) (h₁ h₂ b₁ b₂ : ℚ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (E : NumericalClass) :
    charge (a * (h₁ : ℝ)) (a * (h₂ : ℝ)) (b₁ : ℝ) (b₂ : ℝ) E =
      (Surface.ChargeCoordinates.ofNumericalDataB numericalVariety
        (polarization h₁ h₂ hh₁ hh₂) (bField b₁ b₂)).centralCharge a E := by
  have hparameters :
      parameters (a * (h₁ : ℝ)) (a * (h₂ : ℝ)) (b₁ : ℝ) (b₂ : ℝ) =
        numericalRealization.parameters
          (polarization h₁ h₂ hh₁ hh₂) (bField b₁ b₂) a := by
    change Surface.StabilityParameters.mk ((b₁ : ℝ), (b₂ : ℝ))
        (a * (h₁ : ℝ), a * (h₂ : ℝ)) =
      Surface.StabilityParameters.mk
        (numericalRealization.realizeBField (bField b₁ b₂))
        (a • numericalRealization.realizePolarization
          (polarization h₁ h₂ hh₁ hh₂))
    apply congrArg₂ Surface.StabilityParameters.mk
    · exact (numericalRealization_bField b₁ b₂).symm
    · rw [numericalRealization_polarization]
      ext <;> simp
  rw [charge, hparameters]
  exact Surface.NumericalRealization.centralCharge_eq_ofNumericalDataB
    numericalRealization (polarization h₁ h₂ hh₁ hh₂) (bField b₁ b₂) a E

/-- The direction `f₁-f₂`, orthogonal to the Segre polarization. -/
def antiDiagonal (u : ℝ) : Divisor := (u, -u)

@[simp]
theorem segre_pair_antiDiagonal (u : ℝ) :
    divisorSpace.pair segre (antiDiagonal u) = 0 := by
  simp [Surface.DivisorSpace.pair, divisorSpace, intersectionForm, segre, antiDiagonal]

/-! ### The inherited orthogonal wall slice -/

/-- Linear parameterization of the direction transverse to the Segre class. -/
def antiDiagonalMap : ℝ →ₗ[ℝ] Divisor where
  toFun := antiDiagonal
  map_add' := by
    intro x y
    ext
    · simp [antiDiagonal]
    · simp [antiDiagonal, add_comm]
  map_smul' := by intro a x; ext <;> simp [antiDiagonal]

/-- The full rank-two wall slice of the quadric, as a child of the basis-free
orthogonal-slice construction. -/
def wallSlice : Surface.OrthogonalSlice divisorSpace ℝ where
  H := segre
  transverse := antiDiagonalMap
  orthogonal := segre_pair_antiDiagonal

/-- The generic wall family specialized to the smooth quadric. -/
def wallChargeFamily :
    CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily
      (Surface.OrthogonalSlice.Point ℝ) NumericalClass :=
  wallSlice.chargeFamily chernCharacter

/-- Evaluating the inherited wall family gives the existing arbitrary-real
quadric charge in ruling coordinates. -/
@[simp]
theorem wallChargeFamily_charge (s u t : ℝ) (E : NumericalClass) :
    wallChargeFamily.charge ⟨s, u, t⟩ E =
      charge t t (s + u) (s - u) E := by
  rw [charge]
  have hparameters :
      wallSlice.parameters ⟨s, u, t⟩ =
        parameters t t (s + u) (s - u) := by
    apply congrArg₂ Surface.StabilityParameters.mk
    · change s • segre + antiDiagonalMap u = (s + u, s - u)
      ext <;> simp [antiDiagonalMap, antiDiagonal, segre, sub_eq_add_neg]
    · change t • segre = (t, t)
      ext <;> simp [segre]
  change chernCharacter.centralCharge divisorSpace
      (wallSlice.parameters ⟨s, u, t⟩) E = _
  rw [hparameters]

/-- A nonzero anti-diagonal `B`-field cannot be represented as `beta H` for
the Segre polarization.  This is the concrete information lost by a scalar-only
`B` parameter on a rank-two surface. -/
theorem antiDiagonal_not_rankOne {u : ℝ} (hu : u ≠ 0) :
    ¬ ∃ beta : ℝ, antiDiagonal u = beta • segre := by
  rintro ⟨beta, hbeta⟩
  have h₁ := congrArg Prod.fst hbeta
  have h₂ := congrArg Prod.snd hbeta
  simp [antiDiagonal, segre] at h₁ h₂
  apply hu
  linarith

end

end AlgebraicGeometry.Numerical.Examples.SmoothQuadric
