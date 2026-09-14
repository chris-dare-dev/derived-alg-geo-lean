/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Family

/-!
# The threefold central charge in the `(α, β)` half plane

This file owns the four-coordinate numerical class, its `β`-twist, and the
Bayer--Macrì--Toda central charge. It deliberately stops before wall equations
and wall-specific numerical quantities.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

noncomputable section

namespace Threefold

/-- A numerical class of a polarised threefold, compressed to its four
`H`-degrees `(∫H³ch₀, ∫H²ch₁, ∫H·ch₂, ∫ch₃)`.

A quadruple of reals.  It is **not** `ch(E)` for a sheaf `E`, and the first slot
is weighted by `∫H³`; see the module docstring. -/
abbrev NumClass : Type := ℝ × ℝ × ℝ × ℝ

namespace NumClass

/-- The weighted rank coordinate, standing for `∫H³·ch₀`. -/
def deg0 (v : NumClass) : ℝ := v.1

/-- The coordinate standing for `∫H²·ch₁`. -/
def deg1 (v : NumClass) : ℝ := v.2.1

/-- The coordinate standing for `∫H·ch₂`. -/
def deg2 (v : NumClass) : ℝ := v.2.2.1

/-- The coordinate standing for `∫ch₃`. -/
def deg3 (v : NumClass) : ℝ := v.2.2.2

end NumClass

open NumClass

/-! ### The `β`-twist on compressed coordinates -/

/-- The compressed `β`-twist: the four `H`-degrees of `ch^{βH} = e^{-βH}ch`.

`deg0` is fixed, because the twist sums over `j ≤ 0` in codimension zero. -/
def betaTwist (β : ℝ) (v : NumClass) : NumClass :=
  (v.deg0, v.deg1 - β * v.deg0, v.deg2 - β * v.deg1 + β ^ 2 / 2 * v.deg0,
    v.deg3 - β * v.deg2 + β ^ 2 / 2 * v.deg1 - β ^ 3 / 6 * v.deg0)

@[simp] theorem betaTwist_deg0 (β : ℝ) (v : NumClass) :
    (betaTwist β v).deg0 = v.deg0 := rfl

@[simp] theorem betaTwist_deg1 (β : ℝ) (v : NumClass) :
    (betaTwist β v).deg1 = v.deg1 - β * v.deg0 := rfl

@[simp] theorem betaTwist_deg2 (β : ℝ) (v : NumClass) :
    (betaTwist β v).deg2 = v.deg2 - β * v.deg1 + β ^ 2 / 2 * v.deg0 := rfl

@[simp] theorem betaTwist_deg3 (β : ℝ) (v : NumClass) :
    (betaTwist β v).deg3 =
      v.deg3 - β * v.deg2 + β ^ 2 / 2 * v.deg1 - β ^ 3 / 6 * v.deg0 := rfl

@[simp] theorem betaTwist_zero (v : NumClass) : betaTwist 0 v = v := by
  simp only [betaTwist, deg0, deg1, deg2, deg3]
  norm_num

/-- **The group law**: twisting by `β₁ + β₂` is twisting by `β₂` and then by
`β₁`.  This is `e^{-(β₁+β₂)H} = e^{-β₁H}e^{-β₂H}` on the four degrees, and it is
what makes the name `betaTwist` honest. -/
theorem betaTwist_betaTwist (β₁ β₂ : ℝ) (v : NumClass) :
    betaTwist β₁ (betaTwist β₂ v) = betaTwist (β₁ + β₂) v := by
  simp only [betaTwist, deg0, deg1, deg2, deg3, Prod.mk.injEq]
  exact ⟨trivial, by ring, by ring, by ring⟩

/-! ### The charge -/

/-- The real part of the threefold charge at `(α, β)`. -/
def reZ (α β : ℝ) (v : NumClass) : ℝ :=
  -v.deg3 + β * v.deg2 - (β ^ 2 - α ^ 2) / 2 * v.deg1
    + (β ^ 3 - 3 * β * α ^ 2) / 6 * v.deg0

/-- The imaginary part of the threefold charge at `(α, β)`.

The outer factor of `α` is the one the expansion of `-∫exp(-(β+iα)H)ch`
produces.  Some presentations divide it out; `alignmentValue` is unchanged by that,
because dropping it rescales the imaginary part by `α > 0` and
`alignmentValue_div_alpha` records the resulting proportionality. -/
def imZ (α β : ℝ) (v : NumClass) : ℝ :=
  α * (v.deg2 - β * v.deg1 + (3 * β ^ 2 - α ^ 2) / 6 * v.deg0)

/-- **`β` is a twist, not a coordinate**: the charge at `(α, β)` is the charge
at `(α, 0)` of the `β`-twisted class.  This is the consistency check that ties
the two polynomials to the exponential they came from. -/
theorem reZ_eq_betaTwist (α β : ℝ) (v : NumClass) :
    reZ α β v = reZ α 0 (betaTwist β v) := by
  simp only [reZ, betaTwist, deg0, deg1, deg2, deg3]
  ring

theorem imZ_eq_betaTwist (α β : ℝ) (v : NumClass) :
    imZ α β v = imZ α 0 (betaTwist β v) := by
  simp only [imZ, betaTwist, deg0, deg1, deg2, deg3]
  ring

/-- The complex charge whose real and imaginary parts are `reZ` and `imZ`. -/
def charge (α β : ℝ) : NumClass →+ ℂ :=
  AddMonoidHom.mk'
    (fun v => Complex.ofReal (reZ α β v) + Complex.I * Complex.ofReal (imZ α β v))
    (by
      intro v w
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
        simp only [reZ, deg0, deg1, deg2, deg3, Prod.fst_add, Prod.snd_add]
        ring
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, zero_add]
        simp only [imZ, deg0, deg1, deg2, Prod.fst_add, Prod.snd_add]
        ring)

@[simp]
theorem charge_re (α β : ℝ) (v : NumClass) : (charge α β v).re = reZ α β v := by
  simp [charge]

@[simp]
theorem charge_im (α β : ℝ) (v : NumClass) : (charge α β v).im = imZ α β v := by
  simp [charge]

/-- **The threefold charge family**, a child of the dimension-independent charge
root.  Its parameter space is the whole `(α, β)` plane: positivity `α > 0` stays
attached to the statements that need it, exactly as in the surface child. -/
def chargeFamily : ChargeFamily (ℝ × ℝ) NumClass where
  charge p := charge p.1 p.2

@[simp]
theorem chargeFamily_charge (p : ℝ × ℝ) (v : NumClass) :
    chargeFamily.charge p v = charge p.1 p.2 v := rfl


end Threefold

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
