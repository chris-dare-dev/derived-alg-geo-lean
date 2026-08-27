/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.RealForm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Spherical walls in the `exp(β + iω)` chart

For a real vector space `V` with a symmetric bilinear form `q` — standing for
`NS(X) ⊗ ℝ` with the intersection form — the vector

```
℧ = exp(β + iω) = (1, β + iω, (β + iω)²/2)
```

pairs against a class `δ = (r, Δ, s)` of the real Mukai extension `ℝ ⊕ V ⊕ ℝ`.
This file computes that pairing and names the locus

```
H(δ) = { (β, ω) : (℧, δ) ∈ ℝ_{≤0} }
```

together with the complement of the union of these loci over classes with
`⟪δ, δ⟫ = -2` and positive rank.

## What this is a theorem about, and what it is not

Everything here is arithmetic in a real vector space carrying a symmetric
bilinear form. There is **no** K3 surface: no Néron–Severi group, no ample
cone, no Hodge index theorem, no Mukai vector of an object, no stability
condition and no `Stab(X)`. `Mukai.RealExtension V` is a triple, not `N(X) ⊗ ℝ`, and
`chamber` is not claimed to be the image of anything under a map from a space
of stability conditions.

In particular the Hodge index theorem is **not** used and not assumed. Where
the geometric theory would invoke it — to say that `q` is negative definite on
`ω^⊥` — the statements that need it carry it as an explicit hypothesis, and
none of the statements *in this file* needs it. That is why this file stops
where it does: the local-finiteness theorem, which is the first statement that
genuinely consumes negative-definiteness and lattice discreteness, is deliberately
left to a follow-up rather than stated here with hypotheses nothing here can
discharge.

This is the same discipline `Walls/Numerical/Basic.lean` applies to tilt walls
and `LinearAlgebra/Lattice/Mukai/Basic.lean` applies to the integral Mukai
extension.

## Not the same walls as `Walls/Numerical`

`Walls/Numerical/Basic.lean` is the **tilt-stability** wall structure: a
numerical class is a triple of reals `(ch₀, ch₁·H, ch₂)`, the parameter space
is the `(s, t)` half plane, and the walls are nested conics. This file is a
different structure with the same name attached: the parameter space is a pair
`(β, ω)` of vectors, the index set is the spherical classes, and a wall is a
real half-space rather than a circle. The two files share no declaration and
neither imports the other. Do not merge them.

## The real extension is a twin of `Mukai.pairing`, not a generalisation

`Mukai.pairing` is `ℤ`-valued on `ℤ × N × ℤ` for `b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ`. The
chart lives over `ℝ`, so the formulas below are restated rather than reused.
Generalising `Mukai/Basic.lean` over a base ring would be the tidier fix and is
deliberately not done here: it would rewrite three merged modules and their
audit records for a file that does not yet need the generality.

The two are connected by `IntegralComparison`, which supplies the missing datum
— an additive map `N →+ V` carrying `b` to `q` — and by
`isSpherical_map_iff`, which says the two sphericity conditions agree
across it. Nothing here constructs an `IntegralComparison`; producing one is
the geometric obligation of exhibiting `NS(X)` with its intersection form, and
`Mukai/Basic.lean` says the same thing about its own identification.

## Main results

* `two_mul_rk_mul_pairingRe` — **the identity.** `2r·Re(℧,δ)` collapses to
  `⟪δ,δ⟫ + r²·q(ω,ω) − q(Δ − rβ, Δ − rβ)`, with no side condition. Bridgeland's
  formula `(⋆)` is this divided by `2r`, and is therefore conditional on
  `r ≠ 0` in a way the undivided form is not.
* `pairingIm_eq_of_symm` — `Im(℧,δ) = q(Δ − rβ, ω)`. This is the statement that a wall
  meets the real axis exactly on `ω^⊥`.
* `mem_wall_iff_of_isSpherical` — membership of `H(δ)` for spherical `δ` of
  positive rank, in the form
  `q(Δ − rβ, ω) = 0 ∧ r²·q(ω,ω) ≤ 2 + q(Δ − rβ, Δ − rβ)`.
  This is the shape the local-finiteness argument consumes.
* `corank_eq_of_isSpherical` — the third coordinate of a spherical class is
  determined by the other two once `r ≠ 0`.
* `pairingRe_of_rk_eq_zero` — at rank zero the identity degenerates to `0 = 0`
  and the real part is the *affine* expression `q(β,Δ) − s`. This is the
  reason the index set is `Δ⁺` rather than `Δ`, recorded rather than left to
  inference.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Wall.Spherical

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-! ### The real Mukai extension -/

/-- The Mukai pairing over `ℝ`, built from a bilinear form `q` on the middle
summand.

This file used to declare the type and this pairing a second time, as
`RealMukai` and `pairing`: the same `ℝ × V × ℝ`, the same
`q c c' - r*s' - r'*s`, the same `[AddCommGroup V] [Module ℝ V]` and the same
bilinear form as `Mukai.RealExtension` and `Mukai.realPairing`. The two
docstrings named each other instead of one importing the other. They are now
one, and what is local to this file is the wall arithmetic below.

Note `Mukai.realForm` is *half* the self-pairing, so sphericality below reads
`selfPairing q δ = -2` rather than `realForm q δ = -2`. -/
abbrev pairing (v w : Mukai.RealExtension V) : ℝ := Mukai.realPairing q v w

@[simp]
theorem pairing_mk (r : ℝ) (c : V) (s : ℝ) (r' : ℝ) (c' : V) (s' : ℝ) :
    pairing q (r, c, s) (r', c', s') = q c c' - r * s' - r' * s :=
  rfl

/-- `⟪v, v⟫`. -/
def selfPairing (v : Mukai.RealExtension V) : ℝ := pairing q v v

theorem selfPairing_eq_pairing (v : Mukai.RealExtension V) :
    selfPairing q v = pairing q v v :=
  rfl

@[simp]
theorem selfPairing_mk (r : ℝ) (c : V) (s : ℝ) :
    selfPairing q (r, c, s) = q c c - 2 * (r * s) := by
  simp only [selfPairing, pairing_mk]
  ring

/-! ### The chart

`exp(β + iω) = (1, β + iω, (β + iω)²/2)`, split into real and imaginary parts.
Squaring gives `(β + iω)² = q(β,β) − q(ω,ω) + 2i·q(β,ω)`, so the halves are as
below. Both are elements of `Mukai.RealExtension V`; the pairing against a real class is
computed componentwise because the Mukai form is extended `ℂ`-bilinearly. -/

/-- The real part of `exp(β + iω)`.

`noncomputable` because `Real` division is: the `/2` comes from `(β + iω)²/2`
and there is no way around it. `chartIm` needs no such marker. -/
noncomputable def chartRe (β ω : V) : Mukai.RealExtension V :=
  (1, β, (q β β - q ω ω) / 2)

/-- The imaginary part of `exp(β + iω)`. -/
def chartIm (β ω : V) : Mukai.RealExtension V :=
  (0, ω, q β ω)

/-- `Re (℧, δ)` for `℧ = exp(β + iω)`. Inherits `noncomputable` from
`chartRe`. -/
noncomputable def pairingRe (β ω : V) (δ : Mukai.RealExtension V) : ℝ :=
  pairing q (chartRe q β ω) δ

/-- `Im (℧, δ)` for `℧ = exp(β + iω)`. -/
def pairingIm (β ω : V) (δ : Mukai.RealExtension V) : ℝ :=
  pairing q (chartIm q β ω) δ

theorem pairingRe_eq (β ω : V) (δ : Mukai.RealExtension V) :
    pairingRe q β ω δ = q β δ.2.1 - δ.2.2 - δ.1 * ((q β β - q ω ω) / 2) := by
  simp only [pairingRe, pairing, Mukai.realPairing, chartRe, one_mul]

theorem pairingIm_eq (β ω : V) (δ : Mukai.RealExtension V) :
    pairingIm q β ω δ = q ω δ.2.1 - δ.1 * q β ω := by
  simp only [pairingIm, pairing, Mukai.realPairing, chartIm, zero_mul, sub_zero]

/-! ### The two identities

`pairingIm_eq_of_symm` and `two_mul_rk_mul_pairingRe` are the whole computational content
of the file. Both need symmetry of `q`; nothing above this point does. -/

/-- **The imaginary part is `q(Δ − rβ, ω)`.** So `(℧, δ)` is real exactly when
`Δ − rβ` is `q`-orthogonal to `ω`. -/
theorem pairingIm_eq_of_symm (hq : ∀ x y : V, q x y = q y x) (β ω : V)
    (δ : Mukai.RealExtension V) :
    pairingIm q β ω δ = q (δ.2.1 - δ.1 • β) ω := by
  rw [pairingIm_eq]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [hq ω δ.2.1, hq β ω]

/-- **The identity.** `2r·Re(℧, δ)` collapses to
`⟪δ, δ⟫ + r²·q(ω,ω) − q(Δ − rβ, Δ − rβ)`.

Stated multiplied through by `2r`, so it holds for **every** `r`, including
`r = 0`, with no side condition. Bridgeland's `(⋆)` is this divided by `2r`;
see `pairingRe_eq_of_rk_ne_zero` for that form and `pairingRe_of_rk_eq_zero` for
what the identity does — and does not — say at rank zero. -/
theorem two_mul_rk_mul_pairingRe (hq : ∀ x y : V, q x y = q y x) (β ω : V)
    (δ : Mukai.RealExtension V) :
    2 * δ.1 * pairingRe q β ω δ
      = selfPairing q δ + δ.1 ^ 2 * q ω ω
        - q (δ.2.1 - δ.1 • β) (δ.2.1 - δ.1 • β) := by
  rw [pairingRe_eq, selfPairing_eq_pairing, pairing, Mukai.realPairing]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [hq δ.2.1 β]
  ring

/-- Bridgeland's `(⋆)`: the divided form, valid only for `r ≠ 0`. -/
theorem pairingRe_eq_of_rk_ne_zero (hq : ∀ x y : V, q x y = q y x) (β ω : V)
    {δ : Mukai.RealExtension V} (hr : δ.1 ≠ 0) :
    pairingRe q β ω δ
      = (selfPairing q δ + δ.1 ^ 2 * q ω ω
          - q (δ.2.1 - δ.1 • β) (δ.2.1 - δ.1 • β)) / (2 * δ.1) := by
  rw [← two_mul_rk_mul_pairingRe q hq]
  field_simp

/-- At rank zero the identity carries no information: both sides vanish
identically. -/
theorem two_mul_rk_mul_pairingRe_of_rk_eq_zero (hq : ∀ x y : V, q x y = q y x)
    (β ω : V) {δ : Mukai.RealExtension V} (hr : δ.1 = 0) :
    2 * δ.1 * pairingRe q β ω δ = 0 ∧
      selfPairing q δ + δ.1 ^ 2 * q ω ω
        - q (δ.2.1 - δ.1 • β) (δ.2.1 - δ.1 • β) = 0 := by
  refine ⟨by rw [hr]; ring, ?_⟩
  rw [← two_mul_rk_mul_pairingRe q hq, hr]; ring

/-- What the real part actually is at rank zero: an **affine** expression in
`β`, with no quadratic term and no dependence on `ω` at all.

This is why the index set of walls is `Δ⁺` — spherical classes of positive rank
— rather than all of `Δ`. A rank-zero class still cuts out a locus, but the
quadric picture that `two_mul_rk_mul_pairingRe` describes degenerates, and the
sphericity hypothesis `⟪δ,δ⟫ = -2` reads `q Δ Δ = -2` with `s` unconstrained. -/
theorem pairingRe_of_rk_eq_zero (β ω : V) {δ : Mukai.RealExtension V} (hr : δ.1 = 0) :
    pairingRe q β ω δ = q β δ.2.1 - δ.2.2 := by
  rw [pairingRe_eq, hr]; ring

/-! ### Spherical classes -/

/-- `⟪δ, δ⟫ = -2`, over `ℝ`. The real-coefficient twin of `Mukai.IsSpherical`;
`isSpherical_map_iff` below identifies the two. -/
def IsSpherical (δ : Mukai.RealExtension V) : Prop := selfPairing q δ = -2

theorem isSpherical_iff (δ : Mukai.RealExtension V) :
    IsSpherical q δ ↔ selfPairing q δ = -2 :=
  Iff.rfl

/-- `Δ⁺`: the spherical classes of positive rank. -/
def sphericalPlus : Set (Mukai.RealExtension V) :=
  {δ | IsSpherical q δ ∧ 0 < δ.1}

theorem mem_sphericalPlus_iff (δ : Mukai.RealExtension V) :
    δ ∈ sphericalPlus q ↔ IsSpherical q δ ∧ 0 < δ.1 :=
  Iff.rfl

theorem isSpherical_of_mem_sphericalPlus {δ : Mukai.RealExtension V}
    (h : δ ∈ sphericalPlus q) : IsSpherical q δ :=
  h.1

theorem rk_pos_of_mem_sphericalPlus {δ : Mukai.RealExtension V}
    (h : δ ∈ sphericalPlus q) : 0 < δ.1 :=
  h.2

/-- **The third coordinate of a spherical class is determined by the other
two**, once the rank is nonzero.

So a finiteness statement about spherical classes needs no separate control on
`s`: bounding `(r, Δ)` bounds `δ`. -/
theorem corank_eq_of_isSpherical {δ : Mukai.RealExtension V} (hs : IsSpherical q δ)
    (hr : δ.1 ≠ 0) :
    δ.2.2 = (q δ.2.1 δ.2.1 + 2) / (2 * δ.1) := by
  have h : q δ.2.1 δ.2.1 - δ.1 * δ.2.2 - δ.1 * δ.2.2 = -2 := hs
  have h2 : 2 * δ.1 * δ.2.2 = q δ.2.1 δ.2.1 + 2 := by linarith
  rw [eq_div_iff (mul_ne_zero two_ne_zero hr)]
  linarith [h2]

/-! ### The walls, and the chamber they cut out -/

/-- `H(δ)` in the `(β, ω)` chart: the locus where `(℧, δ)` is real and
non-positive.

Defined for every `δ`, not only for spherical ones of positive rank — the
sphericity and rank hypotheses belong to the theorems, not to the definition. -/
def wall (δ : Mukai.RealExtension V) : Set (V × V) :=
  {p | pairingIm q p.1 p.2 δ = 0 ∧ pairingRe q p.1 p.2 δ ≤ 0}

theorem mem_wall_iff (δ : Mukai.RealExtension V) (p : V × V) :
    p ∈ wall q δ ↔ pairingIm q p.1 p.2 δ = 0 ∧ pairingRe q p.1 p.2 δ ≤ 0 :=
  Iff.rfl

/-- The chamber cut out by a set `S` of classes: the points of the chart on no
wall of `S`. Bridgeland's `L(X)` is `chamber q (sphericalPlus q)`. -/
def chamber (S : Set (Mukai.RealExtension V)) : Set (V × V) :=
  {p | ∀ δ ∈ S, p ∉ wall q δ}

theorem mem_chamber_iff (S : Set (Mukai.RealExtension V)) (p : V × V) :
    p ∈ chamber q S ↔ ∀ δ ∈ S, p ∉ wall q δ :=
  Iff.rfl

theorem chamber_antitone {S T : Set (Mukai.RealExtension V)} (h : S ⊆ T) :
    chamber q T ⊆ chamber q S :=
  fun _ hp δ hδ => hp δ (h hδ)

theorem chamber_eq_compl_iUnion (S : Set (Mukai.RealExtension V)) :
    chamber q S = (⋃ δ ∈ S, wall q δ)ᶜ := by
  ext p
  simp [chamber, Set.mem_compl_iff]

/-- **Membership of a spherical wall, in the form the finiteness argument
consumes.**

The first conjunct puts `Δ − rβ` in `ω^⊥`; the second is the inequality that,
together with negative-definiteness of `q` on `ω^⊥` and a positive lower bound
on `q(ω,ω)`, bounds `r` and then `Δ`. Neither of those two extra hypotheses
appears here, because neither is needed for the equivalence itself. -/
theorem mem_wall_iff_of_isSpherical (hq : ∀ x y : V, q x y = q y x)
    {δ : Mukai.RealExtension V} (hs : IsSpherical q δ) (hr : 0 < δ.1) (p : V × V) :
    p ∈ wall q δ ↔
      q (δ.2.1 - δ.1 • p.1) p.2 = 0 ∧
        δ.1 ^ 2 * q p.2 p.2
          ≤ 2 + q (δ.2.1 - δ.1 • p.1) (δ.2.1 - δ.1 • p.1) := by
  rw [mem_wall_iff, pairingIm_eq_of_symm q hq]
  refine and_congr_right fun _ => ?_
  have key := two_mul_rk_mul_pairingRe q hq p.1 p.2 δ
  rw [(isSpherical_iff q δ).1 hs] at key
  constructor
  · intro h
    have h2 : 2 * δ.1 * pairingRe q p.1 p.2 δ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith [key]
  · intro h
    have h2 : 2 * δ.1 * pairingRe q p.1 p.2 δ ≤ 0 := by linarith [key]
    nlinarith [h2, hr]

/-! ### The bridge to the integral Mukai extension

`Mukai/Basic.lean` builds `ℤ × N × ℤ` with an integral form; this file builds
`ℝ × V × ℝ` with a real one. `IntegralComparison` is the datum that relates
them, and it is **supplied, never constructed** — producing one is the geometric
obligation of exhibiting `NS(X)` with its intersection form. -/

variable {N : Type*} [AddCommGroup N] (b : N →ₗ[ℤ] N →ₗ[ℤ] ℤ)

/-- An additive map from the middle summand of the integral extension to the
middle summand of the real one, carrying `b` to `q`.

`compat` is where the content is; it is stated on all of `N`, so unlike
`IntegralMukaiData.b_spec` this is a genuine comparison of forms and not a
constraint on the image of a single map. -/
structure IntegralComparison where
  /-- The map on middle summands. -/
  toFun : N →+ V
  /-- The forms agree across it. -/
  compat : ∀ x y : N, q (toFun x) (toFun y) = (b x y : ℝ)

variable {q b}

/-- The induced map on Mukai extensions. -/
def IntegralComparison.map (c : IntegralComparison q b)
    (v : Mukai.MukaiLattice N) : Mukai.RealExtension V :=
  ((v.1 : ℝ), c.toFun v.2.1, (v.2.2 : ℝ))

@[simp]
theorem IntegralComparison.map_fst (c : IntegralComparison q b)
    (v : Mukai.MukaiLattice N) : (c.map v).1 = (v.1 : ℝ) :=
  rfl

/-- The comparison is an isometry onto its image: the real pairing of two
mapped classes is the integral pairing, cast. -/
theorem pairing_map (c : IntegralComparison q b) (v w : Mukai.MukaiLattice N) :
    pairing q (c.map v) (c.map w) = (Mukai.pairing b v w : ℝ) := by
  simp only [pairing, Mukai.realPairing, IntegralComparison.map, Mukai.pairing, c.compat]
  push_cast
  ring

theorem selfPairing_map (c : IntegralComparison q b) (v : Mukai.MukaiLattice N) :
    selfPairing q (c.map v) = (Mukai.selfPairing b v : ℝ) := by
  rw [selfPairing_eq_pairing, pairing_map, Mukai.selfPairing_eq_pairing]

/-- **The two sphericity conditions agree.** -/
theorem isSpherical_map_iff (c : IntegralComparison q b)
    (v : Mukai.MukaiLattice N) :
    IsSpherical q (c.map v) ↔ Mukai.IsSpherical b v := by
  rw [isSpherical_iff, selfPairing_map, Mukai.isSpherical_iff,
    show ((-2 : ℤ) : ℝ) = -2 by norm_num |>.symm, Int.cast_inj]

end CategoryTheory.Triangulated.StabilityCondition.Wall.Spherical
