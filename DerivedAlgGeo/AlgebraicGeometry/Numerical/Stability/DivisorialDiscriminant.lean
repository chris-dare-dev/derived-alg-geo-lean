/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialWallTransport

/-!
# Discriminants and the Hodge index on a real divisor space

Macrì--Schmidt (arXiv:1607.01262v3, Definition 6.12) attach three quadratic
quantities to a class on a polarised surface:

* the discriminant `Δ = (ch₁)² - 2 ch₀ ch₂`, which is invariant under every
  `B`-twist;
* `Δ^C_{ω,B} = Δ + C (ω · ch₁^B)²`, the support form of Theorem 6.13;
* `\bar Δ^B_ω = (ω · ch₁^B)² - 2 ω² ch₀^B ch₂^B`, the form that gives the support
  property on the `(α,β)`-plane.

Until this file only the compressed `Surface.discrH` existed, and only on the
`(s,t)` branch of the wall hierarchy.  Here the three forms are defined on the
intrinsic `ChernCharacter` over an arbitrary real divisor space, and the
relations between them are proved:

* `discriminant_twist`: `Δ` does not see `B`;
* `omega_square_mul_discriminant_le_barDiscriminant`: `ω² Δ ≤ \bar Δ^B_ω`
  whenever the Hodge index inequality holds at `ω`;
* `barDiscriminant_rankOne`: on `B = βH`, `ω = αH` the bar form is
  `α²` times the compressed discriminant, independently of `β`, and through a
  `NumericalRealization` this is `α² · discrH`, hence `α²` times the wall-plane
  discriminant of the transported class.

## The Hodge index inequality, in the divisor space

`DivisorSpace.HodgeIndex S H` is the inequality `H² · x² ≤ (H · x)²` for every
real class `x`, together with `H² > 0`.  It is a proposition-valued
certificate; nothing here proves it for a geometric surface.  Two bridges are
proved:

* a Hodge index on a realized divisor space yields the numerical
  `HodgeIndexStatement` of `BogomolovGieseker.lean`, which is the same
  inequality restricted to first Chern classes of numerical classes;
* the numerical statement yields the inequality on realized first Chern
  classes only.  It does **not** yield `DivisorSpace.HodgeIndex`, because it
  quantifies over classes `E : N` and not over arbitrary real divisors.  The
  two certificates are therefore related in one direction only, and that
  asymmetry is the honest content of this file, not an omission.

For orthogonal slices, `OrthogonalSlice.isHodge_of_hodgeIndex` derives the
`IsHodge` certificate from the Hodge index inequality plus nondegeneracy of the
transverse pairing; the inequality alone gives only `≤ 0` on `H^⊥`, which is
`OrthogonalSlice.transverse_square_nonpos_of_hodgeIndex`.  Conversely
`IsHodge.index_le_B` recovers the inequality on the `B`-fields a slice can
reach.  The rank-one slice is Hodge as soon as `H² > 0`.

## What is not here

No Bogomolov inequality is proved.  `discriminant_nonneg_of_semistable` and its
consequences take `BogomolovGiesekerData`, the supplied datum of
`BogomolovGieseker.lean`, and transport it; the statement
`0 ≤ \bar Δ^B_ω(E)` for a semistable `E` and arbitrary `(B, ω)` is obtained only
under a supplied Hodge index at `ω`.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

universe u v w x

namespace AlgebraicGeometry.Numerical.Surface

noncomputable section

variable {A : Type u} {N : Type v} {D : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable [AddCommGroup D] [Module ℝ D]

/-! ### The Hodge index inequality on a divisor space -/

namespace DivisorSpace

variable (S : DivisorSpace D)

/-- **The Hodge index inequality** relative to a class `H` of positive square:
`H² · x² ≤ (H · x)²` for every real divisor class `x`.

This is a certificate.  For `N¹(X)_ℝ` of a smooth projective surface and `H`
ample it is the Hodge index theorem, which is not proved in this repository. -/
structure HodgeIndex (H : D) : Prop where
  /-- The reference class has positive square. -/
  H_square_pos : 0 < S.pair H H
  /-- The index inequality at every real class. -/
  index_le : ∀ x : D, S.pair H H * S.pair x x ≤ S.pair H x ^ 2

namespace HodgeIndex

variable {S} {H : D}

/-- A class orthogonal to `H` has nonpositive square. -/
theorem pair_self_nonpos_of_orthogonal (h : S.HodgeIndex H) {x : D}
    (hx : S.pair H x = 0) : S.pair x x ≤ 0 := by
  have hidx := h.index_le x
  rw [hx] at hidx
  nlinarith [h.H_square_pos, hidx]

/-- A class orthogonal to `H` with nonzero square has negative square.  The
nondegeneracy hypothesis is what the inequality alone cannot supply. -/
theorem pair_self_neg_of_orthogonal (h : S.HodgeIndex H) {x : D}
    (hx : S.pair H x = 0) (hne : S.pair x x ≠ 0) : S.pair x x < 0 :=
  lt_of_le_of_ne (h.pair_self_nonpos_of_orthogonal hx) hne

end HodgeIndex

end DivisorSpace

/-! ### Orthogonal slices -/

namespace OrthogonalSlice

variable {U : Type x} [AddCommGroup U] [Module ℝ U]
variable {S : DivisorSpace D} (T : OrthogonalSlice S U)

/-- The Hodge index inequality gives nonpositive square on every transverse
direction. -/
theorem transverse_square_nonpos_of_hodgeIndex (h : S.HodgeIndex T.H) (u : U) :
    S.pair (T.transverse u) (T.transverse u) ≤ 0 :=
  h.pair_self_nonpos_of_orthogonal (T.orthogonal u)

/-- **Hodge index plus nondegeneracy of the transverse pairing gives the
`IsHodge` certificate.**  Nondegeneracy is stated as: a nonzero transverse
parameter has nonzero square; it implies injectivity of `transverse`. -/
theorem isHodge_of_hodgeIndex (h : S.HodgeIndex T.H)
    (hnd : ∀ u : U, u ≠ 0 → S.pair (T.transverse u) (T.transverse u) ≠ 0) :
    T.IsHodge where
  H_square_pos := h.H_square_pos
  transverse_square_neg u hu :=
    h.pair_self_neg_of_orthogonal (T.orthogonal u) (hnd u hu)

/-- The pairing of `H` with the `B`-field of a slice point sees only the
longitudinal coefficient. -/
theorem H_pair_B (p : Point U) :
    S.pair T.H (T.parameters p).B = p.s * S.pair T.H T.H := by
  rw [parameters_B]
  simp only [DivisorSpace.pair, map_add, map_smul, smul_eq_mul]
  rw [show S.intersection T.H (T.transverse p.u) = 0 from T.orthogonal p.u]
  ring

/-- On the `B`-fields of a Hodge slice the index inequality holds outright:
this is the direction from `IsHodge` back to the inequality, on the classes the
slice can reach. -/
theorem IsHodge.index_le_B (hT : T.IsHodge) (p : Point U) :
    S.pair T.H T.H * S.pair (T.parameters p).B (T.parameters p).B ≤
      S.pair T.H (T.parameters p).B ^ 2 := by
  rw [T.B_square, T.H_pair_B]
  have hG : S.pair (T.transverse p.u) (T.transverse p.u) ≤ 0 := by
    by_cases hu : p.u = 0
    · rw [hu, map_zero]
      simp [DivisorSpace.pair]
    · exact (hT.transverse_square_neg p.u hu).le
  nlinarith [hT.H_square_pos, hG]

/-- The rank-one slice is Hodge as soon as `H² > 0`: there are no transverse
directions. -/
theorem rankOne_isHodge (S : DivisorSpace D) (H : D) (hH : 0 < S.pair H H) :
    (rankOne S H).IsHodge where
  H_square_pos := hH
  transverse_square_neg u hu := absurd (Subsingleton.elim u 0) hu

end OrthogonalSlice

/-! ### The three discriminants -/

namespace ChernCharacter

variable (ch : ChernCharacter N D) (S : DivisorSpace D)

/-- **The discriminant** `Δ(E) = (ch₁)² - 2 ch₀ ch₂`, with `(ch₁)²` computed by
the intersection form of the divisor space. -/
def discriminant (E : N) : ℝ :=
  S.pair (ch.chOne E) (ch.chOne E) - 2 * ch.rank E * ch.chTwo E

/-- The discriminant is invariant under every `B`-twist: `Δ(ch^B) = Δ(ch)`. -/
theorem discriminant_twist (B : D) (E : N) :
    (ch.twist S B).discriminant S E = ch.discriminant S E := by
  have hs : S.pair B (ch.chOne E) = S.pair (ch.chOne E) B := S.pair_comm B (ch.chOne E)
  simp only [discriminant, twist_rank, twist_chOne, twist_chTwo, DivisorSpace.pair,
    map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul] at hs ⊢
  linear_combination (ch.rank E) * hs

/-- **The `ω`-bar discriminant** `\bar Δ^B_ω(E) = (ω · ch₁^B)² - 2 ω² ch₀^B ch₂^B`
of Macrì--Schmidt Definition 6.12. -/
def barDiscriminant (P : StabilityParameters D) (E : N) : ℝ :=
  S.pair P.omega ((ch.twist S P.B).chOne E) ^ 2
    - 2 * S.pair P.omega P.omega * ch.rank E * (ch.twist S P.B).chTwo E

/-- **The `C`-discriminant** `Δ^C_{ω,B}(E) = Δ(E) + C (ω · ch₁^B)²` of
Macrì--Schmidt Definition 6.12; the constant `C` is the one of their
Exercise 6.11 and is supplied by the caller. -/
def discriminantC (P : StabilityParameters D) (C : ℝ) (E : N) : ℝ :=
  ch.discriminant S E + C * S.pair P.omega ((ch.twist S P.B).chOne E) ^ 2

/-- For `C ≥ 0` the `C`-discriminant dominates the discriminant. -/
theorem discriminant_le_discriminantC (P : StabilityParameters D) {C : ℝ}
    (hC : 0 ≤ C) (E : N) :
    ch.discriminant S E ≤ ch.discriminantC S P C E := by
  unfold discriminantC
  nlinarith [sq_nonneg (S.pair P.omega ((ch.twist S P.B).chOne E)), hC]

/-- **`ω² Δ ≤ \bar Δ^B_ω` under the Hodge index inequality at `ω`.**  This is
the step by which Macrì--Schmidt pass from Bogomolov's `Δ ≥ 0` to the support
form on the `(α,β)`-plane. -/
theorem omega_square_mul_discriminant_le_barDiscriminant (P : StabilityParameters D)
    (h : S.HodgeIndex P.omega) (E : N) :
    S.pair P.omega P.omega * ch.discriminant S E ≤ ch.barDiscriminant S P E := by
  rw [← ch.discriminant_twist S P.B E]
  have hidx := h.index_le ((ch.twist S P.B).chOne E)
  unfold discriminant barDiscriminant
  rw [twist_rank]
  nlinarith [hidx]

/-- A nonnegative discriminant gives a nonnegative bar discriminant at every
`(B, ω)` with the Hodge index inequality at `ω`. -/
theorem barDiscriminant_nonneg_of_discriminant_nonneg (P : StabilityParameters D)
    (h : S.HodgeIndex P.omega) (E : N) (hΔ : 0 ≤ ch.discriminant S E) :
    0 ≤ ch.barDiscriminant S P E :=
  le_trans (mul_nonneg h.H_square_pos.le hΔ)
    (ch.omega_square_mul_discriminant_le_barDiscriminant S P h E)

end ChernCharacter

/-! ### The compressed discriminant and the rank-one slice -/

namespace ChargeCoordinates

variable (Dc : ChargeCoordinates N)

/-- The compressed discriminant `(∫H·ch₁)² - 2 (∫H²) ch₀ ∫ch₂` on charge
coordinates: the shape of `Surface.discrH` and of the wall-plane
`Wall.NumClass.discr`, with the rank slot weighted by `∫H²`. -/
def discr (E : N) : ℝ :=
  Dc.degree E ^ 2 - 2 * Dc.hyperplaneSquare * Dc.rank E * Dc.chTwo E

end ChargeCoordinates

namespace ChernCharacter

variable (ch : ChernCharacter N D) (S : DivisorSpace D)

/-- On the rank-one slice `B = βH`, `ω = αH` the bar discriminant is `α²`
times the compressed discriminant at `H`, and does not depend on `β`. -/
theorem barDiscriminant_rankOne (H : D) (alpha beta : ℝ) (E : N) :
    ch.barDiscriminant S (StabilityParameters.rankOne H alpha beta) E =
      alpha ^ 2 * (ch.coordinatesAt S H).discr E := by
  simp only [barDiscriminant, StabilityParameters.rankOne, twist_chOne, twist_chTwo,
    ChargeCoordinates.discr, coordinatesAt_degree, coordinatesAt_rank, coordinatesAt_chTwo,
    coordinatesAt_hyperplaneSquare, DivisorSpace.pair, map_sub, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  ring

end ChernCharacter

/-! ### Through a numerical realization -/

namespace NumericalRealization

variable {V : NumericalVarietyData 2 A N}
variable (R : NumericalRealization V.ring (D := D))
variable (P : Polarization V.ring)

/-- The realized first Chern class has the rational self-intersection. -/
theorem pair_chOne_self (E : N) :
    R.divisorSpace.pair (R.chernCharacter.chOne E) (R.chernCharacter.chOne E) =
      ((V.ring.degree (V.chComp E 1 * V.chComp E 1) : ℚ) : ℝ) := by
  change R.divisorSpace.pair
      (R.divisorClass ⟨V.chComp E 1, V.chComp_mem E 1⟩)
      (R.divisorClass ⟨V.chComp E 1, V.chComp_mem E 1⟩) = _
  rw [R.intersection_eq]

/-- The intrinsic discriminant of the realized character is the integrated
numerical discriminant `∫Δ(E)`. -/
theorem discriminant_chernCharacter (E : N) :
    R.chernCharacter.discriminant R.divisorSpace E =
      ((V.ring.degree (V.discriminant E) : ℚ) : ℝ) := by
  rw [ChernCharacter.discriminant, R.pair_chOne_self, V.degree_discriminant]
  simp only [chernCharacter_rank, chernCharacter_chTwo]
  push_cast
  ring

/-- **A Hodge index inequality on the realized divisor space yields the
numerical `HodgeIndexStatement`**: the latter is the former restricted to first
Chern classes of numerical classes. -/
theorem hodgeIndexStatement_of_hodgeIndex
    (h : R.divisorSpace.HodgeIndex (R.realizePolarization P)) :
    HodgeIndexStatement V P where
  index_le E := by
    have hidx := h.index_le (R.chernCharacter.chOne E)
    rw [R.pair_realizePolarization_self P, R.pair_chOne_self,
      R.pair_realizePolarization_chOne P] at hidx
    exact_mod_cast hidx

/-- The numerical `HodgeIndexStatement` yields the index inequality on realized
first Chern classes.  It does not yield `DivisorSpace.HodgeIndex`, which
quantifies over every real class. -/
theorem index_le_chOne_of_hodgeIndexStatement (hI : HodgeIndexStatement V P) (E : N) :
    R.divisorSpace.pair (R.realizePolarization P) (R.realizePolarization P) *
        R.divisorSpace.pair (R.chernCharacter.chOne E) (R.chernCharacter.chOne E) ≤
      R.divisorSpace.pair (R.realizePolarization P) (R.chernCharacter.chOne E) ^ 2 := by
  rw [R.pair_realizePolarization_self P, R.pair_chOne_self,
    R.pair_realizePolarization_chOne P]
  exact_mod_cast hI.index_le E

/-- Bogomolov--Gieseker, transported: the intrinsic discriminant of a
semistable class is nonnegative.  `BogomolovGiesekerData` is the supplied
datum; nothing is proved about sheaves. -/
theorem discriminant_nonneg_of_semistable {E : N} (B : BogomolovGiesekerData V P)
    (hE : B.Semistable E) :
    0 ≤ R.chernCharacter.discriminant R.divisorSpace E := by
  rw [R.discriminant_chernCharacter]
  exact_mod_cast nonneg_degree_discriminant B hE

/-- **The bar discriminant of a semistable class is nonnegative at every
`(B, ω)` with a Hodge index at `ω`.**  This is the Bogomolov half of
Macrì--Schmidt Theorem 6.13 for slope-semistable classes; the Bridgeland
semistable half is not stated here. -/
theorem barDiscriminant_nonneg_of_semistable {E : N} (B : BogomolovGiesekerData V P)
    (hE : B.Semistable E) (Q : StabilityParameters D)
    (h : R.divisorSpace.HodgeIndex Q.omega) :
    0 ≤ R.chernCharacter.barDiscriminant R.divisorSpace Q E :=
  ChernCharacter.barDiscriminant_nonneg_of_discriminant_nonneg _ _ Q h E
    (R.discriminant_nonneg_of_semistable P B hE)

/-- On the rank-one slice `B = sH`, `ω = tH` of a realized polarisation the bar
discriminant is `t² · discrH`. -/
theorem barDiscriminant_rankOneParameters (p : ℝ × ℝ) (E : N) :
    R.chernCharacter.barDiscriminant R.divisorSpace (R.rankOneParameters P p) E =
      p.2 ^ 2 * ((discrH V P E : ℚ) : ℝ) := by
  rw [rankOneParameters, ChernCharacter.barDiscriminant_rankOne]
  simp only [ChargeCoordinates.discr, ChernCharacter.coordinatesAt_degree,
    ChernCharacter.coordinatesAt_rank, ChernCharacter.coordinatesAt_chTwo,
    ChernCharacter.coordinatesAt_hyperplaneSquare, chernCharacter_rank, chernCharacter_chTwo,
    R.pair_realizePolarization_chOne P, R.pair_realizePolarization_self P, discrH_eq]
  push_cast
  ring

/-- The same, against the wall-plane discriminant of the transported class:
the bar discriminant on the `(s,t)` slice is `t²` times
`Wall.NumClass.discr (toNumClass V P E)`. -/
theorem barDiscriminant_rankOneParameters_eq_discr_toNumClass (p : ℝ × ℝ) (E : N) :
    R.chernCharacter.barDiscriminant R.divisorSpace (R.rankOneParameters P p) E =
      p.2 ^ 2 * Wall.NumClass.discr (toNumClass V P E) := by
  rw [R.barDiscriminant_rankOneParameters P, discr_toNumClass]

/-- On the rank-one slice the bar discriminant of a semistable class is
nonnegative from the numerical data alone: `BogomolovGiesekerData` and the
numerical `HodgeIndexStatement`, with no real Hodge index at `ω` required. -/
theorem barDiscriminant_rankOneParameters_nonneg {E : N} (B : BogomolovGiesekerData V P)
    (hI : HodgeIndexStatement V P) (hE : B.Semistable E) (p : ℝ × ℝ) :
    0 ≤ R.chernCharacter.barDiscriminant R.divisorSpace (R.rankOneParameters P p) E := by
  rw [R.barDiscriminant_rankOneParameters P]
  have h := discrH_nonneg B hI hE
  have h' : (0 : ℝ) ≤ ((discrH V P E : ℚ) : ℝ) := by exact_mod_cast h
  positivity

end NumericalRealization

end

end AlgebraicGeometry.Numerical.Surface
