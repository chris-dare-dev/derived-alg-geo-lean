/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.RankOneRealization
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Signature
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Region
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Spherical.DivisorialRegion
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

## Both the pointwise and the region-wise count

`surface_finite_walls_through_expPlane` is the count at one plane.
`surface_finite_walls_meeting_box` is the count over the compact parameter box
`|B| ≤ b₀`, `t₀ ≤ ω ≤ t₁` with `t₀ > 0`, which is the form a wall-and-chamber
argument consumes.  The second needs a uniform coercivity constant, supplied by
`PlaneRegion.ofCompactPairs` through `Divisorial/Region.lean`.

## What is not proved

Chambers.  Finitely many walls meeting a box does not by itself produce the
connected components of its complement, nor constancy of the semistable objects
on one.

Nothing here identifies the carrier with `K_num(X)` for a geometric surface.
-/

open QuadraticMap
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
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

/-! ### Region-wise finiteness over a compact parameter box -/

/-- The compact family of parameters `|B| ≤ b₀`, `t₀ ≤ ω ≤ t₁`.  Any compact set
on which `ω` stays away from zero would do; a box is the readable choice. -/
def parameterBox (b₀ t₀ t₁ : ℝ) : Set (SurfaceDivisor × SurfaceDivisor) :=
  Set.Icc (-b₀) b₀ ×ˢ Set.Icc t₀ t₁

theorem isCompact_parameterBox (b₀ t₀ t₁ : ℝ) : IsCompact (parameterBox b₀ t₀ t₁) :=
  isCompact_Icc.prod isCompact_Icc

theorem omega_sq_pos_on_parameterBox {h2 : ℝ} (hh2 : 0 < h2) {b₀ t₀ t₁ : ℝ} (ht₀ : 0 < t₀) :
    ∀ p ∈ parameterBox b₀ t₀ t₁, 0 < (surfaceDivisorSpace h2).pair p.2 p.2 := by
  rintro ⟨B, t⟩ hp
  have ht : t₀ ≤ t := hp.2.1
  have htpos : 0 < t := lt_of_lt_of_le ht₀ ht
  show 0 < h2 * t * t
  rw [mul_assoc]
  exact mul_pos hh2 (mul_pos htpos htpos)

/-- **Only finitely many spherical classes of the integral Mukai lattice have a
wall meeting the parameter box**, on a Picard-rank-one surface with `∫H² > 0`.

This is the region-wise statement, the one a wall-and-chamber argument consumes.
Both hypotheses of the generic theorem are discharged: the box is compact, and
`ω² = h2 · ω² > 0` because `ω ≥ t₀ > 0`. -/
theorem surface_finite_walls_meeting_box {h2 : ℝ} (hh2 : 0 < h2)
    (b₀ t₀ t₁ : ℝ) (ht₀ : 0 < t₀) :
    {δ : Mukai.RealExtension SurfaceDivisor |
        PeriodDomain.IsSphericalClass
          (Mukai.realForm (surfaceDivisorSpace h2).intersection) δ ∧
        (∃ p ∈ parameterBox b₀ t₀ t₁,
          DivisorSpace.expPlane (surfaceDivisorSpace h2) p.1 p.2 ∈
            PeriodDomain.wall (Mukai.realForm (surfaceDivisorSpace h2).intersection) δ) ∧
        δ ∈ (Submodule.span ℤ (Set.range surfaceMukaiBasis) :
              Set (Mukai.RealExtension SurfaceDivisor))}.Finite :=
  DivisorSpace.finite_walls_meeting_expFamily (surfaceHodgeDefinite hh2 one_ne_zero)
    (isCompact_parameterBox b₀ t₀ t₁) (omega_sq_pos_on_parameterBox hh2 ht₀) surfaceMukaiBasis

/-- **The region-wise count on the degree-`2d` K3 model**, with the lattice named
as the integral Mukai extension `ℤ ⊕ ℤH ⊕ ℤ`.

Nothing is assumed beyond `d > 0` and `t₀ > 0`. -/
theorem k3_finite_walls_meeting_box {d : ℕ} (hd : d ≠ 0)
    (b₀ t₀ t₁ : ℝ) (ht₀ : 0 < t₀) :
    {δ : Mukai.RealExtension SurfaceDivisor |
        PeriodDomain.IsSphericalClass
          (Mukai.realForm (surfaceDivisorSpace (2 * (d : ℝ))).intersection) δ ∧
        (∃ p ∈ parameterBox b₀ t₀ t₁,
          DivisorSpace.expPlane (surfaceDivisorSpace (2 * (d : ℝ))) p.1 p.2 ∈
            PeriodDomain.wall
              (Mukai.realForm (surfaceDivisorSpace (2 * (d : ℝ))).intersection) δ) ∧
        δ ∈ (Mukai.integralExtension (Submodule.span ℤ (Set.range surfaceDivisorBasis)) :
              Set (Mukai.RealExtension SurfaceDivisor))}.Finite := by
  have hh2 : (0 : ℝ) < 2 * (d : ℝ) := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
    linarith
  have hfin := surface_finite_walls_meeting_box hh2 b₀ t₀ t₁ ht₀
  rwa [span_surfaceMukaiBasis] at hfin

/-- `∫H² = 2d > 0` on the K3 model. -/
theorem k3_h2_pos {d : ℕ} (hd : d ≠ 0) : (0 : ℝ) < 2 * (d : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  linarith

/-! ### The chamber of the box, cut out by finitely many walls -/

/-- The bounded region of the parameter box, in the `(β, ω)` chart.  This is the
first witness for `Spherical.BoundedRegion` on a surface. -/
def boxRegion {h2 : ℝ} (hh2 : 0 < h2) (b₀ t₀ t₁ : ℝ) (ht₀ : 0 < t₀) :
    Wall.Spherical.BoundedRegion (surfaceDivisorSpace h2).intersection :=
  Wall.Spherical.BoundedRegion.ofDivisorSpace (surfaceHodgeDefinite hh2 one_ne_zero)
    (isCompact_parameterBox b₀ t₀ t₁) (omega_sq_pos_on_parameterBox hh2 ht₀)

/-- **Finitely many spherical classes of the lattice have a wall meeting the
box**, in the `(β, ω)` chart of a Picard-rank-one surface. -/
theorem surface_finite_wallCandidates_box {h2 : ℝ} (hh2 : 0 < h2)
    (b₀ t₀ t₁ : ℝ) (ht₀ : 0 < t₀) :
    (Wall.Spherical.wallCandidates (surfaceDivisorSpace h2).intersection
      (boxRegion hh2 b₀ t₀ t₁ ht₀)
      ↑(Submodule.span ℤ (Set.range surfaceDivisorBasis))).Finite :=
  Wall.Spherical.finite_wallCandidates_ofDivisorSpace _ _ _ surfaceDivisorBasis

/-- **On the box, the chamber of the whole lattice is the chamber of those
finitely many classes.**

This is the chamber decomposition, on a surface, with every hypothesis
discharged.  It says nothing about semistable objects: `chamber` is a subset of
the parameter chart. -/
theorem surface_chamber_inter_box {h2 : ℝ} (hh2 : 0 < h2)
    (b₀ t₀ t₁ : ℝ) (ht₀ : 0 < t₀) :
    Wall.Spherical.chamber (surfaceDivisorSpace h2).intersection
        (Wall.Spherical.latticeSpherical (surfaceDivisorSpace h2).intersection
          ↑(Submodule.span ℤ (Set.range surfaceDivisorBasis)))
        ∩ parameterBox b₀ t₀ t₁
      = Wall.Spherical.chamber (surfaceDivisorSpace h2).intersection
        (Wall.Spherical.wallCandidates (surfaceDivisorSpace h2).intersection
          (boxRegion hh2 b₀ t₀ t₁ ht₀)
          ↑(Submodule.span ℤ (Set.range surfaceDivisorBasis)))
        ∩ parameterBox b₀ t₀ t₁ :=
  Wall.Spherical.chamber_inter_ofDivisorSpace _ _ _ surfaceDivisorBasis

/-- The same on the degree-`2d` K3 model, assuming only `d > 0` and `t₀ > 0`. -/
theorem k3_finite_wallCandidates_box {d : ℕ} (hd : d ≠ 0) (b₀ t₀ t₁ : ℝ) (ht₀ : 0 < t₀) :
    (Wall.Spherical.wallCandidates (surfaceDivisorSpace (2 * (d : ℝ))).intersection
      (boxRegion (k3_h2_pos hd) b₀ t₀ t₁ ht₀)
      ↑(Submodule.span ℤ (Set.range surfaceDivisorBasis))).Finite :=
  surface_finite_wallCandidates_box (k3_h2_pos hd) b₀ t₀ t₁ ht₀

end

end Examples

end AlgebraicGeometry.Numerical
