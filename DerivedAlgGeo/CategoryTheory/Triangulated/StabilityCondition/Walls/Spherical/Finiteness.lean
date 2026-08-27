/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Spherical.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Local finiteness of the spherical walls

Only finitely many spherical walls meet a bounded region of the chart. This is
the second half of Bridgeland's Proposition 11.2; `Walls/Spherical/Basic.lean`
supplies the arithmetic it runs on and stops deliberately short of this
statement.

## Two hypotheses the printed proof leaves implicit

The argument is: a wall through `(β, ω)` forces `Δ − rβ ∈ ω^⊥`, negative
definiteness there bounds `q(Δ − rβ, Δ − rβ) ≤ 0`, sphericity turns the wall
inequality into `r²·q(ω,ω) ≤ 2 + q(Δ − rβ, Δ − rβ) ≤ 2`, and then "only finitely
many `r`, hence only finitely many `Δ`". Writing that down forces two
quantifiers the source does not state.

**`q(ω,ω)` must be bounded below by a positive constant.** Boundedness of the
region does not give this: a bounded subset of the chart can approach the
boundary of the ample cone, where `q(ω,ω) → 0` and `r² ≤ 2/q(ω,ω)` bounds
nothing. The source's region is implicitly one whose closure stays inside the
chart.

**The coercivity constant on `ω^⊥` must be uniform in `ω`.** The subspace varies
with `ω` across the region, so a per-point constant gives a per-point bound and
no single finite set. Compactness of the closure supplies a uniform one, but
that is a separate argument about the region, not about the walls.

`BoundedRegion` carries both as fields, so a caller has to produce them and the
theorem cannot quietly assume either. Neither is proved here: exhibiting a
region with these constants is a statement about the ample cone, and the ample
cone does not appear in this file any more than it does in `Basic`.

## What is still not assumed

No K3 surface, no Néron--Severi group, no ample cone, no Hodge index theorem.
`neg_definite` is the *hypothesis* that the geometric theory would discharge by
Hodge index; here it is supplied. `latticeBasis` is a `ℤ`-span of an `ℝ`-basis,
not `NS(X)`.

## Main results

* `BoundedRegion` — a region together with the two constants above.
* `rk_sq_le` — `r² ≤ 2 / ampleLower` for a spherical class whose wall meets the
  region. This is where positivity of the lower bound on `q(ω,ω)` is spent.
* `normSq_sub_smul_le` — `‖Δ − rβ‖² ≤ 2 / coercivity`, from the same
  inequality read the other way.
* `finite_walls_meeting` — the theorem.
-/

open CategoryTheory Bornology Set

namespace CategoryTheory.Triangulated.StabilityCondition.Wall.Spherical

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- A bounded region of the `(β, ω)` chart, together with the two uniform
constants the finiteness argument needs.

`ample_le` and `neg_definite` are the two hypotheses Bridgeland's Proposition
11.2 uses without stating; see the module docstring. Both are fields rather than
side conditions so that producing a region is visibly an obligation. -/
structure BoundedRegion where
  /-- The region itself. -/
  carrier : Set (V × V)
  /-- It is bounded. -/
  bounded : IsBounded carrier
  /-- A positive lower bound for `q(ω,ω)` on the region. -/
  ampleLower : ℝ
  /-- It is positive. This is what stops `r` running away. -/
  ampleLower_pos : 0 < ampleLower
  /-- The bound holds. -/
  ample_le : ∀ p ∈ carrier, ampleLower ≤ q p.2 p.2
  /-- A uniform coercivity constant for `−q` on `ω^⊥`. -/
  coercivity : ℝ
  /-- It is positive. -/
  coercivity_pos : 0 < coercivity
  /-- `q` is uniformly negative definite on `ω^⊥`, with that constant, at every
  point of the region. -/
  neg_definite : ∀ p ∈ carrier, ∀ x : V, q x p.2 = 0 → q x x ≤ -coercivity * ‖x‖ ^ 2

namespace BoundedRegion

variable {q} (R : BoundedRegion q)

/-- The two facts a wall through the region gives about the class, before any
finiteness reasoning: the offset `Δ − rβ` is `q`-negative, and the wall
inequality holds. -/
theorem key (hq : ∀ x y : V, q x y = q y x) {δ : Mukai.RealExtension V}
    (hs : IsSpherical q δ) (hr : 0 < δ.1) {p : V × V} (hp : p ∈ R.carrier)
    (hw : p ∈ wall q δ) :
    q (δ.2.1 - δ.1 • p.1) (δ.2.1 - δ.1 • p.1) ≤ -R.coercivity * ‖δ.2.1 - δ.1 • p.1‖ ^ 2 ∧
      δ.1 ^ 2 * q p.2 p.2
        ≤ 2 + q (δ.2.1 - δ.1 • p.1) (δ.2.1 - δ.1 • p.1) := by
  rw [mem_wall_iff_of_isSpherical q hq hs hr] at hw
  exact ⟨R.neg_definite p hp _ hw.1, hw.2⟩

/-- **The rank is bounded.** `r² ≤ 2 / ampleLower`.

This is the step that needs `ampleLower > 0`, and the step the printed argument
performs by saying "`ω` is constrained to lie in a bounded region". -/
theorem rk_sq_le (hq : ∀ x y : V, q x y = q y x) {δ : Mukai.RealExtension V}
    (hs : IsSpherical q δ) (hr : 0 < δ.1) {p : V × V} (hp : p ∈ R.carrier)
    (hw : p ∈ wall q δ) :
    δ.1 ^ 2 ≤ 2 / R.ampleLower := by
  obtain ⟨hneg, hle⟩ := R.key hq hs hr hp hw
  have hnn : -R.coercivity * ‖δ.2.1 - δ.1 • p.1‖ ^ 2 ≤ 0 := by
    have : (0 : ℝ) ≤ ‖δ.2.1 - δ.1 • p.1‖ ^ 2 := sq_nonneg _
    nlinarith [R.coercivity_pos]
  have hω : R.ampleLower ≤ q p.2 p.2 := R.ample_le p hp
  have hrsq : 0 ≤ δ.1 ^ 2 := sq_nonneg _
  rw [le_div_iff₀ R.ampleLower_pos]
  nlinarith [R.ampleLower_pos]

/-- **The offset is bounded.** `‖Δ − rβ‖² ≤ 2 / coercivity`.

The same inequality as `rk_sq_le`, read for the other term: `r²·q(ω,ω) ≥ 0`
absorbs the rank contribution and what is left bounds the offset. -/
theorem normSq_sub_smul_le (hq : ∀ x y : V, q x y = q y x) {δ : Mukai.RealExtension V}
    (hs : IsSpherical q δ) (hr : 0 < δ.1) {p : V × V} (hp : p ∈ R.carrier)
    (hw : p ∈ wall q δ) :
    ‖δ.2.1 - δ.1 • p.1‖ ^ 2 ≤ 2 / R.coercivity := by
  obtain ⟨hneg, hle⟩ := R.key hq hs hr hp hw
  have hω : R.ampleLower ≤ q p.2 p.2 := R.ample_le p hp
  have hprod : 0 ≤ δ.1 ^ 2 * q p.2 p.2 := by
    have : 0 ≤ q p.2 p.2 := le_trans R.ampleLower_pos.le hω
    positivity
  rw [le_div_iff₀ R.coercivity_pos]
  nlinarith

end BoundedRegion

/-! ### From the two bounds to a finite set

`rk_sq_le` and `normSq_sub_smul_le` bound `r` and the offset `Δ − rβ`. Turning
that into finiteness needs one more input the source states without comment:
**the rank is an integer.** Over `ℝ` alone the bounds are useless for this — `r`
ranges in `(0, √(2/ampleLower)]`, which is bounded and infinite, and worse, the
third coordinate `s = (q(Δ,Δ) + 2)/(2r)` supplied by `corank_eq_of_isSpherical`
blows up as `r → 0`. Integrality of the rank is what makes `r ≥ 1`, which bounds
`s` and lets a class be reconstructed from `(r, Δ)` alone. -/

/-- Rebuild a class from its rank and middle coordinate, with the third
coordinate forced by sphericity.

This is `corank_eq_of_isSpherical` read as a definition: on spherical classes of
nonzero rank the third coordinate is not free, so `(n, Δ)` already determines
the class and a finiteness statement never has to bound `s`. -/
noncomputable def reconstruct (nΔ : ℤ × V) : Mukai.RealExtension V :=
  ((nΔ.1 : ℝ), nΔ.2, (q nΔ.2 nΔ.2 + 2) / (2 * (nΔ.1 : ℝ)))

/-- The spherical classes of positive integral rank, with middle coordinate in
`Λ`, whose wall meets the region. -/
def wallCandidates (R : BoundedRegion q) (Λ : Set V) : Set (Mukai.RealExtension V) :=
  {δ | IsSpherical q δ ∧ 0 < δ.1 ∧ (∃ n : ℤ, (n : ℝ) = δ.1) ∧ δ.2.1 ∈ Λ ∧
    (wall q δ ∩ R.carrier).Nonempty}

namespace BoundedRegion

variable {q} (R : BoundedRegion q)

/-- A bound on `‖β‖` over the region, extracted from boundedness. -/
theorem exists_norm_fst_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ R.carrier, ‖p.1‖ ≤ M := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 R.bounded
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  exact le_trans (le_trans (norm_fst_le p) (hC p hp)) (le_max_left _ _)

/-- **Every candidate is reconstructed from a bounded integer and a bounded
lattice point.** This is the whole content of the finiteness argument; the
finiteness itself is then two standard facts. -/
theorem wallCandidates_subset (hq : ∀ x y : V, q x y = q y x) (Λ : Set V)
    {M : ℝ} (hM : ∀ p ∈ R.carrier, ‖p.1‖ ≤ M) :
    wallCandidates q R Λ ⊆
      reconstruct q ''
        (Set.Icc (1 : ℤ) ⌈2 / R.ampleLower⌉ ×ˢ
          (Metric.closedBall (0 : V)
            (Real.sqrt (2 / R.coercivity) +
              Real.sqrt (2 / R.ampleLower) * M) ∩ Λ)) := by
  rintro δ ⟨hs, hr, ⟨n, hn⟩, hΛ, p, hw, hp⟩
  -- the rank is a positive integer, so it is at least one
  have hn1 : 1 ≤ n := by
    have : (0 : ℝ) < (n : ℝ) := hn ▸ hr
    exact_mod_cast this
  -- and it is bounded above, because `n ≤ n²`
  have hsq : δ.1 ^ 2 ≤ 2 / R.ampleLower := R.rk_sq_le hq hs hr hp hw
  have hn_le : n ≤ ⌈2 / R.ampleLower⌉ := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have : (n : ℝ) ≤ 2 / R.ampleLower := by nlinarith [hn ▸ hsq]
    exact_mod_cast le_trans this (Int.le_ceil _)
  -- the offset is bounded, hence so is the middle coordinate
  have hoff : ‖δ.2.1 - δ.1 • p.1‖ ≤ Real.sqrt (2 / R.coercivity) := by
    have h := Real.sqrt_le_sqrt (R.normSq_sub_smul_le hq hs hr hp hw)
    rwa [Real.sqrt_sq (norm_nonneg _)] at h
  have hrle : δ.1 ≤ Real.sqrt (2 / R.ampleLower) := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hr.le] at h
  have hmid : ‖δ.2.1‖ ≤ Real.sqrt (2 / R.coercivity) + Real.sqrt (2 / R.ampleLower) * M := by
    have htri : ‖δ.2.1‖ ≤ ‖δ.2.1 - δ.1 • p.1‖ + ‖δ.1 • p.1‖ := by
      simpa using norm_add_le (δ.2.1 - δ.1 • p.1) (δ.1 • p.1)
    calc ‖δ.2.1‖ ≤ ‖δ.2.1 - δ.1 • p.1‖ + ‖δ.1 • p.1‖ := htri
      _ ≤ Real.sqrt (2 / R.coercivity) + Real.sqrt (2 / R.ampleLower) * M := by
          have hsm : ‖δ.1 • p.1‖ = δ.1 * ‖p.1‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
          have hβ : ‖p.1‖ ≤ M := hM p hp
          have : δ.1 * ‖p.1‖ ≤ Real.sqrt (2 / R.ampleLower) * M :=
            mul_le_mul hrle hβ (norm_nonneg _) (Real.sqrt_nonneg _)
          rw [hsm]; linarith
  refine ⟨(n, δ.2.1), ⟨Set.mem_Icc.2 ⟨hn1, hn_le⟩, ?_, hΛ⟩, ?_⟩
  · simpa [Metric.mem_closedBall, dist_zero_right] using hmid
  · -- sphericity forces the third coordinate, so `(n, Δ)` rebuilds `δ`
    have hcor := corank_eq_of_isSpherical q hs (ne_of_gt hr)
    refine Prod.ext hn (Prod.ext rfl ?_)
    simpa [reconstruct, hn] using hcor.symm

/-- **Only finitely many spherical walls meet a bounded region.**

Bridgeland's Proposition 11.2, with the two uniform constants of
`BoundedRegion` made explicit and the rank required to be an integer. `Λ` is the
`ℤ`-span of an `ℝ`-basis; it is not asserted to be `NS(X)`. -/
theorem finite_wallCandidates (hq : ∀ x y : V, q x y = q y x)
    [FiniteDimensional ℝ V] {ι : Type*} [Finite ι] (basis : Module.Basis ι ℝ V) :
    (wallCandidates q R ↑(Submodule.span ℤ (Set.range basis))).Finite := by
  obtain ⟨M, _, hM⟩ := R.exists_norm_fst_le
  refine Set.Finite.subset (Set.Finite.image _ ?_)
    (R.wallCandidates_subset hq _ hM)
  exact (Set.finite_Icc _ _).prod
    (ZSpan.setFinite_inter basis Metric.isBounded_closedBall)

end BoundedRegion

end CategoryTheory.Triangulated.StabilityCondition.Wall.Spherical
