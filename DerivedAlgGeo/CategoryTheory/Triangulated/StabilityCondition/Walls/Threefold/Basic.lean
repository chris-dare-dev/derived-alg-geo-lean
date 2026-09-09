/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.ChargeFamily

/-!
# The threefold charge in the `(α, β)` half plane

`Walls/Numerical/Basic.lean` is the surface model: three real coordinates and
the twisted charge of the `(s, t)` half plane.  This file is its threefold
counterpart, four real coordinates and the Bayer--Macrì--Toda charge, and it is
another child of `Walls/ChargeFamily.lean` rather than a second wall theory.

## The charge, derived rather than guessed

For a polarised threefold with `ω = αH` and `B = βH`, the double-tilt charge is
`Z = -∫ exp(-(β + iα)H) ch`.  Writing `w = β + iα` and

```text
d₀ = ∫H³ch₀,  d₁ = ∫H²ch₁,  d₂ = ∫H·ch₂,  d₃ = ∫ch₃,
```

the expansion of `exp(-wH)` to codimension three gives

```text
Z = -d₃ + w d₂ - (w²/2) d₁ + (w³/6) d₀,
```

and separating real and imaginary parts is `reZ` and `imZ` below.  Nothing is
matched term by term against a source: the two polynomials are the real and
imaginary parts of that one expansion, and `charge_eq_betaTwist` checks the
consistency that makes `β` a twist rather than a coordinate.

## The rank slot carries `∫H³`

Exactly as in the surface model, where it carries `∫H²`.  `d₀` is `∫H³·ch₀`, not
`ch₀`; the unweighted reading does not satisfy the charge formula.  The
transport from a numerical threefold lives with the geometry and carries the
weight.

## What is not here

No stability condition, no heart, no tilt.  `Q` and `nu` are **definitions** on
four real numbers: `Q` is the Bayer--Macrì--Toda quantity and `nu` the tilt
slope, and the conjectural inequality `0 ≤ Q` appears nowhere below.  It is
false in general — it fails on the blow-up of `ℙ³` at a point (Schmidt, IMRN
2017) — and `AlgebraicGeometry/Numerical/Stability/BMT.lean` carries it as
supplied data with that warning.  Defining the quantity is not assuming the
conjecture, and this file does only the former.
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
produces.  Some presentations divide it out; `wallValue` is unchanged by that,
because dropping it rescales the imaginary part by `α > 0` and
`wallValue_div_alpha` records the resulting proportionality. -/
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

/-- **The threefold charge family**, a child of the dimension-independent wall
root.  Its parameter space is the whole `(α, β)` plane: positivity `α > 0` stays
attached to the statements that need it, exactly as in the surface child. -/
def chargeFamily : ChargeFamily (ℝ × ℝ) NumClass where
  charge p := charge p.1 p.2

@[simp]
theorem chargeFamily_charge (p : ℝ × ℝ) (v : NumClass) :
    chargeFamily.charge p v = charge p.1 p.2 v := rfl

/-- The universal determinant of the threefold family, written out in the two
polynomials. -/
theorem chargeFamily_wallValue (p : ℝ × ℝ) (v w : NumClass) :
    chargeFamily.wallValue p v w =
      reZ p.1 p.2 v * imZ p.1 p.2 w - imZ p.1 p.2 v * reZ p.1 p.2 w := by
  simp [ChargeFamily.wallValue, ChargeFamily.re, ChargeFamily.im]

/-- Dropping the outer `α` from the imaginary part rescales every wall
expression by `α`, so it moves no wall off `α = 0`.  This is why the two
normalisations of the threefold charge found in the literature agree about
walls. -/
theorem wallValue_div_alpha (α β : ℝ) (v w : NumClass) :
    reZ α β v * imZ α β w - imZ α β v * reZ α β w =
      α * (reZ α β v * (imZ α β w / α) - (imZ α β v / α) * reZ α β w) ∨ α = 0 := by
  by_cases hα : α = 0
  · exact Or.inr hα
  · refine Or.inl ?_
    field_simp

/-! ### The Bayer--Macrì--Toda quantities, as definitions -/

/-- The `H`-discriminant of a compressed threefold class,
`Δ_H = (∫H²ch₁)² − 2(∫H³ch₀)(∫H·ch₂)`. -/
def discr (v : NumClass) : ℝ := v.deg1 ^ 2 - 2 * v.deg0 * v.deg2

/-- **The tilt slope** `ν_{α,β}`, junk where the denominator vanishes — the same
convention the surface slope uses at rank zero. -/
def nu (α β : ℝ) (v : NumClass) : ℝ :=
  ((betaTwist β v).deg2 - α ^ 2 / 2 * v.deg0) / (betaTwist β v).deg1

/-- **The Bayer--Macrì--Toda quantity**
`Q_{α,β} = α²Δ_H + 4(∫H·ch₂^β)² − 6(∫H²ch₁^β)(∫ch₃^β)`.

Defining it is all this does.  Its nonnegativity on tilt-semistable objects is
the BMT conjecture, which is **false in general**; see the module docstring and
`AlgebraicGeometry/Numerical/Stability/BMT.lean`. -/
def Q (α β : ℝ) (v : NumClass) : ℝ :=
  α ^ 2 * discr (betaTwist β v) + 4 * (betaTwist β v).deg2 ^ 2
    - 6 * (betaTwist β v).deg1 * (betaTwist β v).deg3

/-- At `α = 0` the quantity loses its discriminant term. -/
theorem Q_zero_alpha (β : ℝ) (v : NumClass) :
    Q 0 β v = 4 * (betaTwist β v).deg2 ^ 2
      - 6 * (betaTwist β v).deg1 * (betaTwist β v).deg3 := by
  rw [Q]
  ring

/-- At `β = 0` the twist disappears. -/
@[simp]
theorem Q_zero_beta (α : ℝ) (v : NumClass) :
    Q α 0 v = α ^ 2 * discr v + 4 * v.deg2 ^ 2 - 6 * v.deg1 * v.deg3 := by
  rw [Q, betaTwist_zero]

/-- At `α = 0` the tilt slope is the plain ratio of the two twisted degrees. -/
theorem nu_zero_alpha (β : ℝ) (v : NumClass) :
    nu 0 β v = (betaTwist β v).deg2 / (betaTwist β v).deg1 := by
  rw [nu]
  norm_num

end Threefold

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
