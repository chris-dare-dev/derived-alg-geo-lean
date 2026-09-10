/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.RankOneRealization
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Signature
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.IntegralBridge

/-!
# Finitely many spherical walls on a Picard-rank-one surface

`Walls/Divisorial/Signature.lean` shows that `DivisorSpace.HodgeDefinite` is the
`PeriodDomain.HasSignatureTwo` hypothesis, and spends it on Bridgeland's local
finiteness at a point of the period domain.  This file instantiates that on the
models of `RankOneRealization.lean`, so the statement is about a surface rather
than about an abstract quadratic space.

## What the statement says

For a Picard-rank-one surface with `∫H² = h2 > 0`, the real Mukai extension is
`ℝ ⊕ ℝH ⊕ ℝ` and the lattice is the integral Mukai extension
`ℤ ⊕ ℤH ⊕ ℤ`, which is `Mukai.integralExtension` of `ℤ·H`.  Then for every
`(B, ω)` with `ω ≠ 0`:

```text
only finitely many spherical classes of ℤ ⊕ ℤH ⊕ ℤ
have a wall through the plane of exp(B + iω).
```

Both hypotheses are discharged.  Positivity of `ω²` is `h2 · ω² > 0`, and the
signature comes from `surfaceHodgeDefinite`, which is free on a line.  Nothing
is assumed.

## Why the rank-one case is the honest first instance

The Mukai extension of a rank-one divisor space has signature `(2, 1)`, so the
positive planes form a genuine period domain and the finiteness statement is not
vacuous.  The two-point blow-up gives signature `(2, 3)` by the same route, recorded as
`BlowUpPlane.hasSignatureTwo`; its lattice is not built here, because
`Mukai.extendBasis` wants an explicit basis of the rank-three divisor space.

## What is not proved

The **region-wise** finiteness — finitely many walls meeting a family of planes
— does not follow, for the reason `QuadraticForm/WallFiniteness.lean` records:
the coercivity constant degrades at the boundary of the positive-plane locus.
That needs a `PlaneRegion` carrying its own constant and is a separate change.

Nothing here identifies the carrier with `K_num(X)` for a geometric surface.
-/

open QuadraticMap
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

/-! ### The signature of the rank-one Mukai extension -/

/-- **The real Mukai extension of a Picard-rank-one surface has signature
`(2, 1)`.**

This is `hasSignatureTwo_of_hodgeDefinite` fed with `surfaceHodgeDefinite`, and
it is what every period-domain theorem has been waiting for. -/
theorem surfaceHasSignatureTwo {h2 : ℝ} (hh2 : 0 < h2) :
    PeriodDomain.HasSignatureTwo (Mukai.realForm (surfaceDivisorSpace h2).intersection) :=
  DivisorSpace.hasSignatureTwo_of_hodgeDefinite (surfaceHodgeDefinite hh2 one_ne_zero)

/-- The degree-`2d` K3 model, for `d > 0`. -/
theorem k3HasSignatureTwo {d : ℕ} (hd : d ≠ 0) :
    PeriodDomain.HasSignatureTwo
      (Mukai.realForm (k3Realization d).divisorSpace.intersection) := by
  rw [k3Realization_divisorSpace]
  refine surfaceHasSignatureTwo ?_
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  linarith

/-! ### The lattice -/

/-- The `ℝ`-basis of the rank-one divisor line. -/
def surfaceDivisorBasis : Module.Basis Unit ℝ SurfaceDivisor :=
  Module.Basis.singleton Unit ℝ

/-- The induced basis of the real Mukai extension `ℝ ⊕ ℝH ⊕ ℝ`. -/
def surfaceMukaiBasis :
    Module.Basis (Unit ⊕ (Unit ⊕ Unit)) ℝ (Mukai.RealExtension SurfaceDivisor) :=
  Mukai.extendBasis surfaceDivisorBasis

/-- **The `ℤ`-span of that basis is the integral Mukai extension `ℤ ⊕ ℤH ⊕ ℤ`.**

This is what makes the finiteness statement below one about integral classes. -/
theorem span_surfaceMukaiBasis :
    Submodule.span ℤ (Set.range surfaceMukaiBasis)
      = Mukai.integralExtension (Submodule.span ℤ (Set.range surfaceDivisorBasis)) :=
  Mukai.span_range_extendBasis surfaceDivisorBasis

/-! ### Local finiteness of spherical walls -/

/-- **Only finitely many spherical classes of the integral Mukai lattice have a
wall through the plane of `exp(B + iω)`**, on a Picard-rank-one surface with
`∫H² > 0`.

Both hypotheses of the generic theorem are discharged here: `ω² = h2 · ω² > 0`
because `ω ≠ 0`, and the signature by `surfaceHasSignatureTwo`. -/
theorem surface_finite_walls_through_expPlane {h2 : ℝ} (hh2 : 0 < h2)
    (B omega : SurfaceDivisor) (homega : omega ≠ 0) :
    {δ : Mukai.RealExtension SurfaceDivisor |
        PeriodDomain.IsSphericalClass
          (Mukai.realForm (surfaceDivisorSpace h2).intersection) δ ∧
        DivisorSpace.expPlane (surfaceDivisorSpace h2) B omega ∈
          PeriodDomain.wall (Mukai.realForm (surfaceDivisorSpace h2).intersection) δ ∧
        δ ∈ (Submodule.span ℤ (Set.range surfaceMukaiBasis) :
              Set (Mukai.RealExtension SurfaceDivisor))}.Finite := by
  refine DivisorSpace.finite_walls_through_expPlane
    (surfaceHodgeDefinite hh2 one_ne_zero) B omega ?_ surfaceMukaiBasis
  show 0 < h2 * omega * omega
  rw [mul_assoc]
  exact mul_pos hh2 (mul_self_pos.mpr homega)

/-- The same, on the degree-`2d` K3 model. -/
theorem k3_finite_walls_through_expPlane {d : ℕ} (hd : d ≠ 0)
    (B omega : SurfaceDivisor) (homega : omega ≠ 0) :
    {δ : Mukai.RealExtension SurfaceDivisor |
        PeriodDomain.IsSphericalClass
          (Mukai.realForm (surfaceDivisorSpace (2 * (d : ℝ))).intersection) δ ∧
        DivisorSpace.expPlane (surfaceDivisorSpace (2 * (d : ℝ))) B omega ∈
          PeriodDomain.wall
            (Mukai.realForm (surfaceDivisorSpace (2 * (d : ℝ))).intersection) δ ∧
        δ ∈ (Submodule.span ℤ (Set.range surfaceMukaiBasis) :
              Set (Mukai.RealExtension SurfaceDivisor))}.Finite := by
  refine surface_finite_walls_through_expPlane ?_ B omega homega
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  linarith

/-- The K3 statement with the lattice named as the integral Mukai extension
`ℤ ⊕ ℤH ⊕ ℤ` rather than as a span of basis vectors. -/
theorem k3_finite_walls_integral {d : ℕ} (hd : d ≠ 0)
    (B omega : SurfaceDivisor) (homega : omega ≠ 0) :
    {δ : Mukai.RealExtension SurfaceDivisor |
        PeriodDomain.IsSphericalClass
          (Mukai.realForm (surfaceDivisorSpace (2 * (d : ℝ))).intersection) δ ∧
        DivisorSpace.expPlane (surfaceDivisorSpace (2 * (d : ℝ))) B omega ∈
          PeriodDomain.wall
            (Mukai.realForm (surfaceDivisorSpace (2 * (d : ℝ))).intersection) δ ∧
        δ ∈ (Mukai.integralExtension (Submodule.span ℤ (Set.range surfaceDivisorBasis)) :
              Set (Mukai.RealExtension SurfaceDivisor))}.Finite := by
  have h := k3_finite_walls_through_expPlane hd B omega homega
  rwa [span_surfaceMukaiBasis] at h

end

end Examples

end AlgebraicGeometry.Numerical
