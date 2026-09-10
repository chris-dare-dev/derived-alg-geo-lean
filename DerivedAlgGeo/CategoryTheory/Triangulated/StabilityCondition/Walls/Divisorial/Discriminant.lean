/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Slice

/-!
# Discriminants and the Hodge index on a real divisor space

Macrì--Schmidt (arXiv:1607.01262v3, Definition 6.12) attach three quadratic
quantities to a class on a polarised surface:

* the discriminant `Δ = (ch₁)² - 2 ch₀ ch₂`, which is invariant under every
  `B`-twist;
* `Δ^C_{ω,B} = Δ + C (ω · ch₁^B)²`, the support form of Theorem 6.13;
* `\bar Δ^B_ω = (ω · ch₁^B)² - 2 ω² ch₀^B ch₂^B`, the form that gives the support
  property on the `(α,β)`-plane.

Before this file the only discriminant available was the compressed one of
the `(s,t)` branch of the wall hierarchy.  Here the three forms are defined on the
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


universe v w x

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

variable {N : Type v} {D : Type w}
variable [AddCommGroup N]
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

/-- **Negative definiteness of the intersection form on `H^⊥`**, together with
positivity of `H²`.

This is what the Hodge index theorem gives for `N¹(X)_ℝ` with `H` ample: the
form has signature `(1, ρ - 1)`, so it is negative definite on `H^⊥`.
`HodgeIndex` records only the inequality that follows from it, and the
inequality is strictly weaker — it permits an isotropic class in `H^⊥`, which a
support property cannot. -/
structure HodgeDefinite (H : D) : Prop where
  /-- The reference class has positive square. -/
  H_square_pos : 0 < S.pair H H
  /-- The form is negative definite on the orthogonal complement of `H`. -/
  neg_definite : ∀ x : D, S.pair H x = 0 → x ≠ 0 → S.pair x x < 0

namespace HodgeDefinite

variable {S} {H : D}

/-- Definiteness on `H^⊥` implies the index inequality, by splitting a class
into its `H`-component and an orthogonal remainder. -/
theorem toHodgeIndex (h : S.HodgeDefinite H) : S.HodgeIndex H where
  H_square_pos := h.H_square_pos
  index_le x := by
    have hH : S.pair H H ≠ 0 := ne_of_gt h.H_square_pos
    set t : ℝ := S.pair H x / S.pair H H with ht
    set x' : D := x - t • H with hx'
    have horth : S.pair H x' = 0 := by
      simp only [hx', DivisorSpace.pair, map_sub, map_smul, smul_eq_mul]
      change S.pair H x - t * S.pair H H = 0
      rw [ht, div_mul_cancel₀ _ hH, sub_self]
    have hsplit : x = t • H + x' := by
      simp only [hx']
      abel
    have hcomm : S.pair x' H = 0 := by rw [S.pair_comm]; exact horth
    have hxx : S.pair x x = t ^ 2 * S.pair H H + S.pair x' x' := by
      conv_lhs => rw [hsplit]
      simp only [DivisorSpace.pair, map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul] at horth hcomm ⊢
      linear_combination t * horth + t * hcomm
    have hx'nonpos : S.pair x' x' ≤ 0 := by
      by_cases hz : x' = 0
      · rw [hz]
        simp [DivisorSpace.pair]
      · exact (h.neg_definite x' horth hz).le
    have hts : t ^ 2 * S.pair H H * S.pair H H = S.pair H x ^ 2 := by
      rw [ht]
      field_simp
    nlinarith [h.H_square_pos, hxx, hx'nonpos, hts]

end HodgeDefinite

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
coordinates: the shape consumed by the wall-plane
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

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
