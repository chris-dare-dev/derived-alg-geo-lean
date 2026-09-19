/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.ThreefoldWallTransport

/-!
# The tilt family on a polarised threefold, and the slope it induces

`ThreefoldWallTransport.lean` transports a polarised threefold class to the
four-coordinate `(α, β)` model and proves `nu_toNumClass`: the model's
`Wall.Threefold.nu` is the `BMT.nu` this directory already had. `Walls/Threefold/
Tilt.lean` proves `nu_eq_tilt_slope`: that same model slope is `α` times the
charge slope of the tilt family.

This file composes the two, which is what #1228 asked for and what neither half
could state alone. The result is the geometric reading of the tilt charge:

> the Bayer--Macrì--Toda slope of a class on a polarised numerical threefold is
> `α` times the charge slope of `Tilt.tiltFamily` at its transported class.

## No new carrier

There is deliberately no `tiltWallChargeFamily` here. The sketch had one, and
`Walls/Threefold/TiltComparison.lean` records why it is not reinstated: the
implemented transport pulls back the **untilted** `Threefold.chargeFamily`, the
two families genuinely differ, and `Tilt.exists_tilt_alignmentValue_ne_threefold`
proves it with a computed witness. A family here would need the two independent
consumers the abstraction tree requires before a root is minted, and it has
none: the statements below need `Tilt.tiltFamily` applied at a transported
class, which is not the same thing as a new family.

## No third slope

`nu` (this directory) and `Wall.Threefold.nu` (the model) are the two the
adjudication kept, and both appear below in the same equation rather than a
third being defined.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

universe u v

namespace AlgebraicGeometry.Numerical

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

namespace Threefold

variable (V : NumericalVarietyData 3 A N) (P : Polarization V.ring)

/-! ### The tilt charge, in the degrees this directory reads -/

/-- The tilt family's imaginary part at a transported class is `α·∫H²·ch₁^β`.

This is what makes the positivity hypothesis of the slope theorems below
checkable on a threefold: it is a statement about `degH1Beta`, not about a
coordinate of an abstract quadruple. -/
theorem tiltFamily_im_toNumClass (α β : ℚ) (E : N) :
    Wall.Tilt.tiltFamily.im ((α : ℝ), (β : ℝ)) (toNumClass V P E)
      = ((α * degH1Beta V P β E : ℚ) : ℝ) := by
  rw [Wall.Tilt.tiltFamily_im, betaTwist_toNumClass]
  push_cast
  rfl

/-- The tilt family's real part at a transported class is the negated
Bayer--Macrì--Toda numerator, `−(∫H·ch₂^β − (α²/2)·∫H³·ch₀)`.

`ch₀` carries no `β`, which is why the subtrahend reads the untwisted rank slot
of the transported class. -/
theorem tiltFamily_re_toNumClass (α β : ℚ) (E : N) :
    Wall.Tilt.tiltFamily.re ((α : ℝ), (β : ℝ)) (toNumClass V P E)
      = -((degH2Beta V P β E
            - (α ^ 2 / 2) * (V.ring.degree (P.cls ^ 3) * (V.rank E : ℚ)) : ℚ) : ℝ) := by
  rw [Wall.Tilt.tiltFamily_re, betaTwist_toNumClass, toNumClass_deg0]
  simp only [Wall.Threefold.NumClass.deg2]
  push_cast
  ring

/-! ### The slope, composed -/

/-- **The Bayer--Macrì--Toda slope is the tilt family's charge slope, rescaled.**

`Tilt.nu_eq_tilt_slope` says this of the four-coordinate model and
`nu_toNumClass` says the model's slope is this directory's `nu`; neither alone
connects `Tilt.tiltFamily` to a threefold. This is the composition, and it is
the sense in which the library has one tilt charge rather than three.

The hypothesis is the one the slope convention needs, stated in the degrees a
threefold supplies. -/
theorem nu_eq_tiltFamily_slope (α β : ℚ) (E : N)
    (h : 0 < α * degH1Beta V P β E) :
    ((nu V P α β E : ℚ) : ℝ)
      = (α : ℝ)
          * (-(Wall.Tilt.tiltFamily.re ((α : ℝ), (β : ℝ)) (toNumClass V P E))
              / Wall.Tilt.tiltFamily.im ((α : ℝ), (β : ℝ)) (toNumClass V P E)) := by
  have him : 0 < Wall.Tilt.tiltFamily.im ((α : ℝ), (β : ℝ)) (toNumClass V P E) := by
    rw [tiltFamily_im_toNumClass]
    exact_mod_cast h
  rw [← nu_toNumClass V P α β E]
  exact Wall.Tilt.nu_eq_tilt_slope (α : ℝ) (β : ℝ) (toNumClass V P E) him

/-- The same statement as a `chargeSlope`, which is the form the semistability
vocabulary of `Abelian/Stability/` uses. -/
theorem chargeSlope_tiltFamily_toNumClass (α β : ℚ) (E : N)
    (h : 0 < α * degH1Beta V P β E) :
    CategoryTheory.Triangulated.chargeSlope
        (Wall.Tilt.tiltFamily.charge ((α : ℝ), (β : ℝ)) (toNumClass V P E))
      = (((nu V P α β E : ℚ) / (α : ℝ) : ℝ) : WithTop ℝ) := by
  have him : 0 < Wall.Tilt.tiltFamily.im ((α : ℝ), (β : ℝ)) (toNumClass V P E) := by
    rw [tiltFamily_im_toNumClass]
    exact_mod_cast h
  rw [Wall.Tilt.chargeSlope_tilt (α : ℝ) (β : ℝ) (toNumClass V P E) him,
    nu_toNumClass V P α β E]

end Threefold

end AlgebraicGeometry.Numerical
