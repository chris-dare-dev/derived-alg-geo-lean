/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.SmoothQuadric
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialChargeScalarExtension
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Slice

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

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical.Examples.SmoothQuadric

open Surface

noncomputable section

/-- Independent real parameters in the ruling basis. -/
def parameters (h₁ h₂ b₁ b₂ : ℝ) : StabilityParameters Divisor where
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
    StabilityParameters (Surface.RealDivisorClass numericalRing) where
  B := scalarExtendedDivisor b₁ b₂
  omega := scalarExtendedDivisor h₁ h₂

/-- Realizing scalar-extended parameters recovers the intrinsic ruling
coordinates. -/
@[simp]
theorem realize_scalarExtendedParameters (h₁ h₂ b₁ b₂ : ℝ) :
    numericalRealization.realizeParameters
        (scalarExtendedParameters h₁ h₂ b₁ b₂) =
      parameters h₁ h₂ b₁ b₂ := by
  apply congrArg₂ StabilityParameters.mk
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
    DivisorialParameters ampleCone where
  B := (b₁, b₂)
  omega := (h₁, h₂)
  omega_ample := ⟨hh₁, hh₂⟩

/-- The polarization square is `2 h₁ h₂`. -/
theorem omega_square (h₁ h₂ : ℝ) :
    divisorSpace.pair (h₁, h₂) (h₁, h₂) = 2 * h₁ * h₂ := by
  simp [DivisorSpace.pair, divisorSpace, intersectionForm]
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
  rw [charge, ChernCharacter.centralCharge_apply]
  simp only [chernCharacter_rank, chernCharacter_chOne, chernCharacter_chTwo]
  simp [parameters, divisorSpace, intersectionForm,
    DivisorSpace.pair]
  ring

/-- The intrinsic real charge agrees with the generic numerical-ring charge
for arbitrary rational ample polarization and arbitrary rational `B`-field. -/
theorem charge_eq_numericalBField
    (a : ℝ) (h₁ h₂ b₁ b₂ : ℚ) (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    (E : NumericalClass) :
    charge (a * (h₁ : ℝ)) (a * (h₂ : ℝ)) (b₁ : ℝ) (b₂ : ℝ) E =
      (ChargeCoordinates.ofNumericalDataB numericalVariety
        (polarization h₁ h₂ hh₁ hh₂) (bField b₁ b₂)).centralCharge a E := by
  have hparameters :
      parameters (a * (h₁ : ℝ)) (a * (h₂ : ℝ)) (b₁ : ℝ) (b₂ : ℝ) =
        numericalRealization.parameters
          (polarization h₁ h₂ hh₁ hh₂) (bField b₁ b₂) a := by
    change StabilityParameters.mk ((b₁ : ℝ), (b₂ : ℝ))
        (a * (h₁ : ℝ), a * (h₂ : ℝ)) =
      StabilityParameters.mk
        (numericalRealization.realizeBField (bField b₁ b₂))
        (a • numericalRealization.realizePolarization
          (polarization h₁ h₂ hh₁ hh₂))
    apply congrArg₂ StabilityParameters.mk
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
  simp [DivisorSpace.pair, divisorSpace, intersectionForm, segre, antiDiagonal]

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
def wallSlice : OrthogonalSlice divisorSpace ℝ where
  H := segre
  transverse := antiDiagonalMap
  orthogonal := segre_pair_antiDiagonal

/-! ### The certificates of the slice

`Walls/Divisorial/Slice.lean` attaches `IsHodge` and `IsGeometric` to an
orthogonal slice, and `wallSlice` carried neither.  Both hold here, and the
pieces were already in the file: the Segre class has positive square, the
anti-diagonal direction has negative square, and `ampleCone` is exactly the set
`IsGeometric` wants.

On a hyperbolic form the first condition is not automatic.  `ω² = 2h₁h₂` is
negative on half the plane and zero on the two rulings, which are isotropic, so
`H_square_pos` genuinely selects the positive cone.  That is the difference from
the rank-one slice, where every nonzero class has positive square, and it makes
the quadric the first slice whose Hodge certificate is neither vacuous nor
automatic. -/

/-- `∫(f₁+f₂)² = 2`, so the Segre class has positive square. -/
@[simp]
theorem segre_square : divisorSpace.pair segre segre = 2 := by
  show (1 : ℝ) * 1 + 1 * 1 = 2
  norm_num

/-- The anti-diagonal direction has square `-2u²`: negative for every nonzero
parameter.  The ruling classes themselves are isotropic, which is why this needs
the anti-diagonal and not an arbitrary transverse direction. -/
@[simp]
theorem antiDiagonal_square (u : ℝ) :
    divisorSpace.pair (antiDiagonal u) (antiDiagonal u) = -2 * u ^ 2 := by
  show u * (-u) + (-u) * u = -2 * u ^ 2
  ring

/-- **The quadric's wall slice is Hodge.**

Not vacuous, unlike the rank-one slice: the transverse space is a line and the
second clause has to be checked on it. -/
theorem wallSlice_isHodge : wallSlice.IsHodge where
  H_square_pos := by
    show 0 < divisorSpace.pair segre segre
    rw [segre_square]
    norm_num
  transverse_square_neg u hu := by
    show divisorSpace.pair (antiDiagonal u) (antiDiagonal u) < 0
    rw [antiDiagonal_square]
    have : 0 < u ^ 2 := by positivity
    linarith

/-- The Segre class is ample. -/
theorem segre_mem_ampleCone : segre ∈ ampleCone := by
  simp [ampleCone, segre]

/-- **The quadric's wall slice is geometric.**

`ampleCone` and the slice were both already here; nothing had put them together,
so `IsGeometric` had no witness on this surface. -/
theorem wallSlice_isGeometric : wallSlice.IsGeometric ampleCone where
  __ := wallSlice_isHodge
  H_ample := segre_mem_ampleCone

/-- **The Hodge certificate fails off the positive cone**, which is what makes
the hyperbolic case different from the definite one.

A ruling class is isotropic, so it cannot be the distinguished direction of any
Hodge slice.  On a rank-one surface no such class exists. -/
theorem not_isHodge_rulingOne (T : OrthogonalSlice divisorSpace ℝ)
    (hH : T.H = rulingOne) : ¬ T.IsHodge := by
  intro h
  have hsq : divisorSpace.pair T.H T.H = 0 := by
    rw [hH]
    exact rulingOne_sq
  have := h.H_square_pos
  rw [hsq] at this
  exact lt_irrefl 0 this

/-- The generic wall family specialized to the smooth quadric. -/
def wallChargeFamily :
    CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily
      (OrthogonalSlice.Point ℝ) NumericalClass :=
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
    apply congrArg₂ StabilityParameters.mk
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
