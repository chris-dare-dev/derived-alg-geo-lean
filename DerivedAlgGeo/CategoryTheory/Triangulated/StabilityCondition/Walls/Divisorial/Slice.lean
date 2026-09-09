/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.ChargeFamily
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Charge

/-!
# Orthogonal slices of divisorial surface-charge families

`Wall.ChargeFamily` defines numerical walls for arbitrary parameterized
central charges.  This file supplies a surface-specific descendant without
making its coordinate choices part of the wall root.

Given a real divisor space, a distinguished class `H`, and a linear family of
transverse classes `G(u)` orthogonal to `H`, an `OrthogonalSlice` parameterizes

`B = s H + G(u)`, `omega = t H`.

The transverse parameter space `U` is an arbitrary real vector space.  Thus a
rank-one surface uses the zero-dimensional `U`, a Picard-rank-two surface may
use `U = ℝ`, and higher-rank surfaces may use a finite-dimensional coordinate
space or the entire intrinsic orthogonal subspace.  Bases remain optional
children of the construction.

All wall loci are inherited from `Wall.ChargeFamily.wall`.  This file only
proves the divisorial formulas used to calculate them.  Ampleness and the
Hodge-index signature are separate proposition-valued certificates; neither
is required to define the charge family or its numerical walls.
-/

open Complex

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

universe u v w x

variable {D : Type u} [AddCommGroup D] [Module ℝ D]
variable {N : Type v} [AddCommGroup N]
variable {P : Type w}

namespace ChernCharacter

variable (ch : ChernCharacter N D)

/-- Any parameterization of divisorial data induces a generic central-charge
family. -/
def chargeFamily (S : DivisorSpace D)
    (parameters : P → StabilityParameters D) : Wall.ChargeFamily P N where
  charge p := ch.centralCharge S (parameters p)

/-- The full divisorial wall family, indexed by arbitrary independent real
`B` and `omega` classes.  Every surface slice below is a reindexing of this
parent family. -/
def fullChargeFamily (S : DivisorSpace D) :
    Wall.ChargeFamily (StabilityParameters D) N :=
  ch.chargeFamily S id

@[simp]
theorem chargeFamily_charge (S : DivisorSpace D)
    (parameters : P → StabilityParameters D) (p : P) (E : N) :
    (ch.chargeFamily S parameters).charge p E =
      ch.centralCharge S (parameters p) E := rfl

@[simp]
theorem fullChargeFamily_charge (S : DivisorSpace D)
    (p : StabilityParameters D) (E : N) :
    (ch.fullChargeFamily S).charge p E = ch.centralCharge S p E := rfl

end ChernCharacter

/-- A basis-free orthogonal slice through the real divisor parameter space.

Only orthogonality is structural.  Positivity, ampleness, and negative
definiteness belong to `OrthogonalSlice.IsHodge` and `.IsGeometric`. -/
structure OrthogonalSlice (S : DivisorSpace D) (U : Type w)
    [AddCommGroup U] [Module ℝ U] where
  /-- The distinguished polarization direction. -/
  H : D
  /-- A linear parameterization of directions transverse to `H`. -/
  transverse : U →ₗ[ℝ] D
  /-- Every transverse direction is intersection-orthogonal to `H`. -/
  orthogonal : ∀ u, S.pair H (transverse u) = 0

namespace OrthogonalSlice

variable {U : Type w} [AddCommGroup U] [Module ℝ U]
variable {S : DivisorSpace D}
variable (T : OrthogonalSlice S U)

/-- A point `(s,u,t)` of an orthogonal slice. -/
structure Point (U : Type w) where
  /-- Coefficient of `H` in the `B`-field. -/
  s : ℝ
  /-- Transverse `B`-field parameter. -/
  u : U
  /-- Coefficient of `H` in `omega`. -/
  t : ℝ

/-- The intrinsic divisor parameters represented by a slice point. -/
def parameters (p : Point U) : StabilityParameters D where
  B := p.s • T.H + T.transverse p.u
  omega := p.t • T.H

/-- The central-charge family obtained from an orthogonal divisor slice. -/
def chargeFamily (ch : ChernCharacter N D) : Wall.ChargeFamily (Point U) N :=
  (ch.fullChargeFamily S).reindex T.parameters

/-- The numerical wall of two classes in an orthogonal divisor slice. -/
def wall (ch : ChernCharacter N D) (v w : N) : Set (Point U) :=
  (T.chargeFamily ch).wall v w

/-- The intrinsic intersection-orthogonal complement of a divisor class. -/
def orthogonalSubspace (S : DivisorSpace D) (H : D) : Submodule ℝ D :=
  LinearMap.ker (S.intersection H)

/-- The basis-free slice using the full intrinsic orthogonal complement of
`H`. -/
def fullOrthogonal (S : DivisorSpace D) (H : D) :
    OrthogonalSlice S (orthogonalSubspace S H) where
  H := H
  transverse := (orthogonalSubspace S H).subtype
  orthogonal u := u.property

/-- Every real divisor class decomposes into its `H` component and an
orthogonal component when `H²` is nonzero.  Thus the intrinsic
`fullOrthogonal` slice loses no `B`-field directions; only `omega` is
restricted to the ray through `H`. -/
theorem exists_fullOrthogonal_coordinates (S : DivisorSpace D) (H B : D)
    (hH : S.pair H H ≠ 0) :
    ∃ s : ℝ, ∃ G : orthogonalSubspace S H, B = s • H + G.1 := by
  let s := S.pair H B / S.pair H H
  let G₀ := B - s • H
  have hG₀ : S.pair H G₀ = 0 := by
    simp only [G₀, DivisorSpace.pair, map_sub, map_smul, smul_eq_mul]
    dsimp only [s]
    change S.pair H B -
      (S.pair H B / S.pair H H) * S.pair H H = 0
    rw [div_mul_cancel₀ _ hH, sub_self]
  refine ⟨s, ⟨G₀, hG₀⟩, ?_⟩
  dsimp only [G₀]
  abel

/-- The rank-one slice has no transverse directions. -/
def rankOne (S : DivisorSpace D) (H : D) :
    OrthogonalSlice S (Fin 0 → ℝ) where
  H := H
  transverse := 0
  orthogonal := by intro u; simp [DivisorSpace.pair]

namespace Point

/-- A point of the rank-one slice. -/
def rankOne (s t : ℝ) : Point (Fin 0 → ℝ) where
  s := s
  u := 0
  t := t

end Point

/-- Numerical Hodge-index data for an orthogonal slice.  It is not needed for
the wall equation itself. -/
structure IsHodge : Prop where
  /-- The distinguished direction has positive square. -/
  H_square_pos : 0 < S.pair T.H T.H
  /-- Every nonzero transverse parameter has negative square. -/
  transverse_square_neg : ∀ u : U, u ≠ 0 →
    S.pair (T.transverse u) (T.transverse u) < 0

/-- Geometry-specific ampleness attached to the numerical Hodge data. -/
structure IsGeometric (ample : Set D) : Prop extends IsHodge T where
  /-- The distinguished direction lies in the supplied ample cone. -/
  H_ample : T.H ∈ ample

@[simp]
theorem parameters_B (p : Point U) :
    (T.parameters p).B = p.s • T.H + T.transverse p.u := rfl

@[simp]
theorem parameters_omega (p : Point U) :
    (T.parameters p).omega = p.t • T.H := rfl

/-- The `B`-field square splits into its longitudinal and transverse parts. -/
theorem B_square (p : Point U) :
    S.pair (T.parameters p).B (T.parameters p).B =
      p.s ^ 2 * S.pair T.H T.H +
        S.pair (T.transverse p.u) (T.transverse p.u) := by
  have hHG := T.orthogonal p.u
  have hGH := S.pair_comm (T.transverse p.u) T.H
  rw [hHG] at hGH
  simp only [parameters_B, DivisorSpace.pair, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  change p.s * (p.s * S.pair T.H T.H + S.pair (T.transverse p.u) T.H) +
      (p.s * S.pair T.H (T.transverse p.u) +
        S.pair (T.transverse p.u) (T.transverse p.u)) = _
  rw [hHG, hGH]
  simp only [DivisorSpace.pair]
  ring

/-- The polarization square on the slice. -/
theorem omega_square (p : Point U) :
    S.pair (T.parameters p).omega (T.parameters p).omega =
      p.t ^ 2 * S.pair T.H T.H := by
  simp only [parameters_omega, DivisorSpace.pair, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The mixed product `omega.B` has no transverse contribution. -/
theorem omega_B (p : Point U) :
    S.pair (T.parameters p).omega (T.parameters p).B =
      p.t * p.s * S.pair T.H T.H := by
  rw [parameters_omega, parameters_B]
  simp only [DivisorSpace.pair, map_add, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  change p.s * (p.t * S.pair T.H T.H) +
      p.t * S.pair T.H (T.transverse p.u) = _
  rw [T.orthogonal]
  simp only [DivisorSpace.pair]
  ring

/-- Pairing the `B`-field with an arbitrary divisor class. -/
theorem B_pair (p : Point U) (x : D) :
    S.pair (T.parameters p).B x =
      p.s * S.pair T.H x + S.pair (T.transverse p.u) x := by
  rw [parameters_B]
  simp only [DivisorSpace.pair, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-- Pairing `omega` with an arbitrary divisor class. -/
theorem omega_pair (p : Point U) (x : D) :
    S.pair (T.parameters p).omega x = p.t * S.pair T.H x := by
  rw [parameters_omega]
  simp only [DivisorSpace.pair, map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- The real-part polynomial of the divisorial charge on the slice. -/
def reFormula (ch : ChernCharacter N D) (p : Point U) (E : N) : ℝ :=
  -ch.chTwo E + p.s * S.pair T.H (ch.chOne E) +
      S.pair (T.transverse p.u) (ch.chOne E) -
    (((p.s ^ 2 - p.t ^ 2) * S.pair T.H T.H +
        S.pair (T.transverse p.u) (T.transverse p.u)) * ch.rank E / 2)

/-- The imaginary-part polynomial of the divisorial charge on the slice. -/
def imFormula (ch : ChernCharacter N D) (p : Point U) (E : N) : ℝ :=
  p.t * (S.pair T.H (ch.chOne E) -
    p.s * S.pair T.H T.H * ch.rank E)

/-- The intrinsic divisorial central charge restricted to an arbitrary
orthogonal slice. -/
theorem centralCharge_eq_formula
    (ch : ChernCharacter N D) (p : Point U) (E : N) :
    ch.centralCharge S (T.parameters p) E =
      Complex.ofReal (T.reFormula ch p E) +
        Complex.I * Complex.ofReal (T.imFormula ch p E) := by
  rw [ChernCharacter.centralCharge_apply]
  rw [T.B_pair p, T.B_square p, T.omega_square p,
    T.omega_pair p, T.omega_B p]
  simp only [reFormula, imFormula]
  congr 1 <;> ring_nf

@[simp]
theorem charge_re (ch : ChernCharacter N D) (p : Point U) (E : N) :
    ((T.chargeFamily ch).charge p E).re = T.reFormula ch p E := by
  change (ch.centralCharge S (T.parameters p) E).re = _
  rw [T.centralCharge_eq_formula]
  simp

@[simp]
theorem charge_im (ch : ChernCharacter N D) (p : Point U) (E : N) :
    ((T.chargeFamily ch).charge p E).im = T.imFormula ch p E := by
  change (ch.centralCharge S (T.parameters p) E).im = _
  rw [T.centralCharge_eq_formula]
  simp

/-- Every numerical wall on the slice is inherited from the universal
determinant equation and evaluates using the two displayed polynomials. -/
theorem wallValue_eq (ch : ChernCharacter N D) (p : Point U) (v w : N) :
    (T.chargeFamily ch).wallValue p v w =
      T.reFormula ch p v * T.imFormula ch p w -
        T.imFormula ch p v * T.reFormula ch p w := by
  simp only [Wall.ChargeFamily.wallValue, Wall.ChargeFamily.re,
    Wall.ChargeFamily.im, T.charge_re, T.charge_im]

end OrthogonalSlice

end


end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
