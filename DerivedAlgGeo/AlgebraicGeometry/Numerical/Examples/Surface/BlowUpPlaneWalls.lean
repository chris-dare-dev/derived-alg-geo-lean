/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.BlowUpPlane
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Spherical.DivisorialRegion
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.IntegralBridge

/-!
# Walls and chambers on the two-point blow-up

`BlowUpPlane.lean` proves the hard part for this model and gets none of the
consequences.  It has `hodgeDefinite` — the reverse Cauchy--Schwarz inequality
for `diag(1, -1, -1)`, so the intersection form is negative definite on the
*plane* `ω^⊥` — and `hasSignatureTwo` follows.  But it has no basis of the
rank-three divisor space, so nothing downstream reaches it:
`Mukai.extendBasis` wants one, and without a lattice there is no wall count, no
region, and no chamber.

`RankOneWalls.lean` has all of that on the line.  But in Picard rank one the
Hodge input is *vacuous*: the orthogonal complement of a nonzero vector on a
line is zero, so the definiteness clause says nothing.  This model is the one
where it says something, which makes it the model where the wall statements
have content.

This file supplies the basis and instantiates the chain.

## What lands

* `divisorBasis` — the missing ingredient, `H, E₁, E₂` as an `ℝ`-basis.
* `span_mukaiBasis` — its extension spans the integral Mukai extension
  `ℤ ⊕ (ℤH ⊕ ℤE₁ ⊕ ℤE₂) ⊕ ℤ`, which is the lattice the counts are stated
  against.
* `finite_walls_through_expPlane` — the pointwise count.
* `finite_walls_meeting_ampleBox` — the region-wise count over a compact family.
* `boxRegion`, `chamber_inter_ampleBox` — the chamber, cut out by finitely many
  walls on the family.

Every hypothesis is discharged.  Because `hodgeDefinite` needs only `ω² > 0` on
this surface, so does everything below: no separate Hodge certificate is carried.

## The compact family

`ampleBox ω₀ b₀ t₀ t₁` is `‖B‖ ≤ b₀` together with `ω` on the segment
`[t₀, t₁]·ω₀` of the ray through a fixed class of positive square.  Scaling a
fixed `ω₀` keeps `ω² = t²·ω₀² > 0` for `t ≥ t₀ > 0`, which is the only thing the
region needs.  `RankOneWalls.parameterBox` is the same shape specialised to the
line; each example states its own, as examples do.

## What is not claimed

Nothing about semistable objects.  `chamber` is a subset of the parameter chart,
and no constancy on it is asserted.  The carrier is not identified with
`K_num(X)` for a geometric blow-up, and no Hodge index theorem is proved for
one — `hodgeDefinite` is proved for *this lattice*, which is the whole point.
-/

open Bornology Set
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical.Examples.BlowUpPlane

noncomputable section

/-! ### The basis of the rank-three divisor space -/

/-- Coordinates on the real divisor space in the basis `H, E₁, E₂`. -/
def divisorCoordEquiv : Divisor ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x := ![x.1, x.2.1, x.2.2]
  invFun x := (x 0, x 1, x 2)
  left_inv _ := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_add' _ _ := by
    funext i
    fin_cases i <;> simp
  map_smul' _ _ := by
    funext i
    fin_cases i <;> simp

/-- **The missing ingredient**: `H, E₁, E₂` as an `ℝ`-basis of the divisor
space. -/
def divisorBasis : Module.Basis (Fin 3) ℝ Divisor :=
  Module.Basis.ofEquivFun divisorCoordEquiv

/-- The induced basis of the real Mukai extension `ℝ ⊕ N¹_ℝ ⊕ ℝ`. -/
def mukaiBasis :
    Module.Basis (Unit ⊕ (Fin 3 ⊕ Unit)) ℝ (Mukai.RealExtension Divisor) :=
  Mukai.extendBasis divisorBasis

/-- **The `ℤ`-span of that basis is the integral Mukai extension** of the
Néron--Severi lattice `ℤH ⊕ ℤE₁ ⊕ ℤE₂`.  This is what makes the counts below
statements about integral classes. -/
theorem span_mukaiBasis :
    Submodule.span ℤ (Set.range mukaiBasis)
      = Mukai.integralExtension (Submodule.span ℤ (Set.range divisorBasis)) :=
  Mukai.span_range_extendBasis divisorBasis

/-! ### The pointwise count -/

/-- **Only finitely many spherical classes of the lattice have a wall through
the plane of `exp(B + iω)`**, on the two-point blow-up.

The only hypothesis is `ω² > 0`.  On this surface `hodgeDefinite` needs nothing
more, so neither does the finiteness. -/
theorem finite_walls_through_expPlane (B omega : Divisor)
    (homega : 0 < divisorSpace.pair omega omega) :
    {δ : Mukai.RealExtension Divisor |
        PeriodDomain.IsSphericalClass (Mukai.realForm divisorSpace.intersection) δ ∧
        DivisorSpace.expPlane divisorSpace B omega ∈
          PeriodDomain.wall (Mukai.realForm divisorSpace.intersection) δ ∧
        δ ∈ (Submodule.span ℤ (Set.range mukaiBasis) :
              Set (Mukai.RealExtension Divisor))}.Finite :=
  DivisorSpace.finite_walls_through_expPlane (hodgeDefinite homega) B omega homega mukaiBasis

/-! ### A compact family along an ample ray -/

/-- The compact family `‖B‖ ≤ b₀`, `ω ∈ [t₀, t₁]·ω₀`. -/
def ampleBox (omega₀ : Divisor) (b₀ t₀ t₁ : ℝ) : Set (Divisor × Divisor) :=
  Metric.closedBall (0 : Divisor) b₀ ×ˢ ((fun t : ℝ => t • omega₀) '' Set.Icc t₀ t₁)

theorem isCompact_ampleBox (omega₀ : Divisor) (b₀ t₀ t₁ : ℝ) :
    IsCompact (ampleBox omega₀ b₀ t₀ t₁) :=
  (isCompact_closedBall _ _).prod
    (isCompact_Icc.image (by continuity))

/-- On the family `ω²` stays positive, because scaling a class of positive
square by `t ≥ t₀ > 0` scales the square by `t²`. -/
theorem omega_sq_pos_on_ampleBox {omega₀ : Divisor}
    (h₀ : 0 < divisorSpace.pair omega₀ omega₀) {b₀ t₀ t₁ : ℝ} (ht₀ : 0 < t₀) :
    ∀ p ∈ ampleBox omega₀ b₀ t₀ t₁, 0 < divisorSpace.pair p.2 p.2 := by
  rintro ⟨B, omega⟩ ⟨-, t, ht, rfl⟩
  have htpos : 0 < t := lt_of_lt_of_le ht₀ ht.1
  have hval : divisorSpace.pair (t • omega₀) (t • omega₀)
      = t ^ 2 * divisorSpace.pair omega₀ omega₀ := by
    simp only [divisorSpace_pair, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [hval]
  have : 0 < t ^ 2 := by positivity
  exact mul_pos this h₀

/-! ### The region-wise count, and the chamber -/

/-- **The region-wise count.**  Only finitely many spherical classes of the
lattice have a wall meeting the family. -/
theorem finite_walls_meeting_ampleBox {omega₀ : Divisor}
    (h₀ : 0 < divisorSpace.pair omega₀ omega₀) (b₀ : ℝ) {t₀ : ℝ} (t₁ : ℝ) (ht₀ : 0 < t₀) :
    {δ : Mukai.RealExtension Divisor |
        PeriodDomain.IsSphericalClass (Mukai.realForm divisorSpace.intersection) δ ∧
        (∃ p ∈ ampleBox omega₀ b₀ t₀ t₁,
          DivisorSpace.expPlane divisorSpace p.1 p.2 ∈
            PeriodDomain.wall (Mukai.realForm divisorSpace.intersection) δ) ∧
        δ ∈ (Submodule.span ℤ (Set.range mukaiBasis) :
              Set (Mukai.RealExtension Divisor))}.Finite :=
  DivisorSpace.finite_walls_meeting_expFamily (hodgeDefinite h₀)
    (isCompact_ampleBox omega₀ b₀ t₀ t₁)
    (omega_sq_pos_on_ampleBox h₀ ht₀) mukaiBasis

/-- The bounded region of the family, in the `(β, ω)` chart. -/
def boxRegion {omega₀ : Divisor} (h₀ : 0 < divisorSpace.pair omega₀ omega₀)
    (b₀ : ℝ) {t₀ : ℝ} (t₁ : ℝ) (ht₀ : 0 < t₀) :
    Wall.Spherical.BoundedRegion divisorSpace.intersection :=
  Wall.Spherical.BoundedRegion.ofDivisorSpace (hodgeDefinite h₀)
    (isCompact_ampleBox omega₀ b₀ t₀ t₁) (omega_sq_pos_on_ampleBox h₀ ht₀)

/-- **Finitely many spherical classes have a wall meeting the family**, in the
`(β, ω)` chart. -/
theorem finite_wallCandidates_ampleBox {omega₀ : Divisor}
    (h₀ : 0 < divisorSpace.pair omega₀ omega₀) (b₀ : ℝ) {t₀ : ℝ} (t₁ : ℝ) (ht₀ : 0 < t₀) :
    (Wall.Spherical.wallCandidates divisorSpace.intersection
      (boxRegion h₀ b₀ t₁ ht₀)
      ↑(Submodule.span ℤ (Set.range divisorBasis))).Finite :=
  Wall.Spherical.finite_wallCandidates_ofDivisorSpace _ _ _ divisorBasis

/-- **On the family, the chamber of the whole lattice is the chamber of those
finitely many classes.**

This is the chamber decomposition on the model where the Hodge input is not
vacuous.  It says nothing about semistable objects. -/
theorem chamber_inter_ampleBox {omega₀ : Divisor}
    (h₀ : 0 < divisorSpace.pair omega₀ omega₀) (b₀ : ℝ) {t₀ : ℝ} (t₁ : ℝ) (ht₀ : 0 < t₀) :
    Wall.Spherical.chamber divisorSpace.intersection
        (Wall.Spherical.latticeSpherical divisorSpace.intersection
          ↑(Submodule.span ℤ (Set.range divisorBasis)))
        ∩ ampleBox omega₀ b₀ t₀ t₁
      = Wall.Spherical.chamber divisorSpace.intersection
        (Wall.Spherical.wallCandidates divisorSpace.intersection
          (boxRegion h₀ b₀ t₁ ht₀)
          ↑(Submodule.span ℤ (Set.range divisorBasis)))
        ∩ ampleBox omega₀ b₀ t₀ t₁ :=
  Wall.Spherical.chamber_inter_ofDivisorSpace _ _ _ divisorBasis

/-! ### The anticanonical ray -/

/-- The realized anticanonical class `-K = 3H - E₁ - E₂` has square `7`, so it
is an admissible `ω₀`. -/
theorem antiCanonical_sq_pos :
    0 < divisorSpace.pair
      (numericalRealization.realizePolarization antiCanonicalPolarization)
      (numericalRealization.realizePolarization antiCanonicalPolarization) :=
  hodgeDefinite_antiCanonical.H_square_pos

/-- The chamber decomposition along the anticanonical ray, with every hypothesis
discharged and nothing supplied. -/
theorem finite_walls_meeting_antiCanonicalBox (b₀ : ℝ) {t₀ : ℝ} (t₁ : ℝ) (ht₀ : 0 < t₀) :
    {δ : Mukai.RealExtension Divisor |
        PeriodDomain.IsSphericalClass (Mukai.realForm divisorSpace.intersection) δ ∧
        (∃ p ∈ ampleBox
            (numericalRealization.realizePolarization antiCanonicalPolarization) b₀ t₀ t₁,
          DivisorSpace.expPlane divisorSpace p.1 p.2 ∈
            PeriodDomain.wall (Mukai.realForm divisorSpace.intersection) δ) ∧
        δ ∈ (Submodule.span ℤ (Set.range mukaiBasis) :
              Set (Mukai.RealExtension Divisor))}.Finite :=
  finite_walls_meeting_ampleBox antiCanonical_sq_pos b₀ t₁ ht₀

end

end AlgebraicGeometry.Numerical.Examples.BlowUpPlane
