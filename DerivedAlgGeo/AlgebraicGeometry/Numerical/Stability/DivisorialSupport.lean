/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialDiscriminant
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Support

/-!
# Bogomolov--Gieseker gives the support property on a realized surface

`Walls/Divisorial/Support.lean` proves that the `C`-discriminant, bundled as a
`QuadraticForm ℝ` on the real Mukai extension, is negative on every nonzero
class of vanishing charge, provided the intersection form is negative definite
on `ω^⊥`.  What it leaves open is the other half of
`Support.IsCompatible`: nonnegativity of that form on the locus of classes one
actually wants a support property for.

This file closes it for slope-semistable classes of a realized numerical
surface, and the closing input is exactly the one the repository already
isolates as unproved.  `BogomolovGiesekerData` supplies `∫Δ(E) ≥ 0` for a
semistable `E`; `discriminant_le_discriminantC` upgrades that to `Δ^C ≥ 0` for
`C ≥ 0`; and `hasQuadraticSupportProperty_image` transports it along the class
map.

## What the two hypotheses are

* `BogomolovGiesekerData` is **supplied**, not proved.  Nothing below asserts an
  inequality about sheaves, and the trust boundary is unchanged.
* `DivisorSpace.HodgeDefinite` is **supplied**, not proved.  It is the Hodge
  index theorem in the form the support property needs — negative definiteness
  on `ω^⊥`, not merely the inequality `H²x² ≤ (H·x)²`.  On a smooth projective
  surface with `ω` ample it is true; this repository does not prove it, and
  `hodgeIndexStatement_of_hodgeDefinite` records that it is the stronger of the
  two certificates already in the library.

## What is not claimed

Nothing here says the resulting `Z` is a Bridgeland stability condition, or that
the semistable locus is the set of semistable objects of a heart.  The support
property is a statement about a linear charge and a set of classes, and that is
all that is proved.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

universe u v w

namespace AlgebraicGeometry.Numerical.Surface

noncomputable section

variable {A : Type u} {N : Type v} {D : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

namespace NumericalRealization

/-! ### The stronger Hodge certificate -/

section Algebraic

variable [AddCommGroup D] [Module ℝ D]
variable {V : NumericalVarietyData 2 A N}
variable (R : NumericalRealization V.ring (D := D))
variable (P : Polarization V.ring)

/-- Negative definiteness on `ω^⊥` yields the numerical `HodgeIndexStatement`,
through the weaker inequality certificate.  This is what places
`HodgeDefinite` above `HodgeIndex` in the same one-directional ladder
`DivisorialDiscriminant.lean` describes. -/
theorem hodgeIndexStatement_of_hodgeDefinite
    (h : R.divisorSpace.HodgeDefinite (R.realizePolarization P)) :
    HodgeIndexStatement V P :=
  R.hodgeIndexStatement_of_hodgeIndex P h.toHodgeIndex

/-- **`Δ^C` is nonnegative on the slope-semistable locus** for every `C ≥ 0`.

This is Bogomolov--Gieseker plus `discriminant_le_discriminantC`; the first is
supplied and the second is proved. -/
theorem discriminantC_nonneg_of_semistable {E : N} (B : BogomolovGiesekerData V P)
    (hE : B.Semistable E) (Q : StabilityParameters D) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ R.chernCharacter.discriminantC R.divisorSpace Q C E :=
  le_trans (R.discriminant_nonneg_of_semistable P B hE)
    (ChernCharacter.discriminant_le_discriminantC _ _ Q hC E)

end Algebraic

/-! ### The support property -/

section Normed

variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {V : NumericalVarietyData 2 A N}
variable (R : NumericalRealization V.ring (D := D))
variable (P : Polarization V.ring)

/-- **The divisorial charge has the support property on the slope-semistable
locus.**

The quadratic form is the `C`-discriminant of Macrì--Schmidt Definition 6.12,
bundled on the real Mukai extension.  Its nonnegativity on the locus is
Bogomolov--Gieseker, supplied by `BogomolovGiesekerData`; its negativity on the
kernel of the charge is proved from `HodgeDefinite` in
`Walls/Divisorial/Support.lean`.

This is the Kontsevich--Soibelman support property in the form
`Weak/Support/Predicate/Quadratic.lean` states it, for the charge of an
arbitrary `(B, ω)` with `ω` in the positive cone. -/
theorem hasQuadraticSupportProperty_semistable (B : BogomolovGiesekerData V P)
    (Q : StabilityParameters D) (hω : R.divisorSpace.HodgeDefinite Q.omega)
    {C : ℝ} (hC : 0 ≤ C) :
    Support.HasQuadraticSupportProperty (R.divisorSpace.realCentralCharge Q)
      (R.chernCharacter.toRealExtension '' {E : N | B.Semistable E}) :=
  R.chernCharacter.hasQuadraticSupportProperty_image R.divisorSpace Q hω C _
    fun _ hE => R.discriminantC_nonneg_of_semistable P B hE Q hC

section FiniteDimensional

variable [FiniteDimensional ℝ D]

/-- The same conclusion in the norm-bound formulation of
`Support.HasSupportProperty`, which is the shape the stability-condition
interfaces consume. -/
theorem hasSupportProperty_semistable (B : BogomolovGiesekerData V P)
    (Q : StabilityParameters D) (hω : R.divisorSpace.HodgeDefinite Q.omega)
    {C : ℝ} (hC : 0 ≤ C) :
    Support.HasSupportProperty (R.divisorSpace.realCentralCharge Q)
      (R.chernCharacter.toRealExtension '' {E : N | B.Semistable E}) :=
  (R.hasQuadraticSupportProperty_semistable P B Q hω hC).hasSupportProperty

end FiniteDimensional

end Normed

end NumericalRealization

end

end AlgebraicGeometry.Numerical.Surface
