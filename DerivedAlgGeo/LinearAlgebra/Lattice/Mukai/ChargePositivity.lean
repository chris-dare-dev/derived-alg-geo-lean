/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.CentralCharge

/-!
# Boundary positivity for exponential Mukai charges

This file isolates the Hodge-index calculation governing the real part of
`Z(β,ω)` when its imaginary part vanishes. Bridgeland's K3 Lemma 6.2
(`math/0307164`, §6) is one specialization; the core and its exact-margin
interface contain no K3 normalization and are isolated from every sheaf.

## The boundary

`charge_im` reads the imaginary part of `Z(β,ω)` off `expCharge_apply`:

```
Im Z (r, c, s) = b ω c - r * b β ω = (c - r•β) · ω
```

so `Im Z = 0` says exactly that `c - r•β` is orthogonal to `ω`. That is the
case Lemma 6.2 has to work for; every other object of the tilted heart has
`Im Z > 0`, or is torsion, and needs none of this file.

## The identity

Everything then rests on one algebraic identity, `two_mul_re_expCharge`:

```
2 * r * Re Z (r, c, s)
  = - b (c - r•β) (c - r•β)  +  2 * realForm b (r, c, s)  +  r^2 * b ω ω
```

It is `ring` once `expCharge_apply` and `realForm_apply` are unfolded. Its use
is that the first summand is `≥ 0` by the Hodge index theorem — the orthogonal
complement of `ω` is negative semi-definite, which is
`PeriodDomain.nonpos_of_sigPos_eq_one` — so

```
2 * r * Re Z ≥ 2 * realForm b v + r^2 * b ω ω.
```

## Why there are two conclusions, and where `1 ≤ r` comes from

`re_expCharge_pos_of_nonneg` is the non-spherical case: `realForm b v ≥ 0`
makes the bound positive using only `b ω ω > 0`.

`re_expCharge_pos_of_neg_one` is the spherical case, `realForm b v = -1` — the
paper's `v(E)² = -2`, halved by this repository's convention (see
`Mukai/RealForm.lean`). There the bound is `r^2 * b ω ω - 2`, so positivity
needs `r^2 * b ω ω > 2`.

Bridgeland states the hypothesis as `ω² > 2`. That is sufficient **only because
`r` is an integer rank**, so `1 ≤ r`: over the reals `0 < r` leaves
`r^2 * b ω ω` arbitrarily small. The hypothesis is stated as `1 ≤ r` here
rather than left implicit.

## What is not here

No sheaf, no heart, no stability function. In particular the input
`-1 ≤ realForm b v` is a hypothesis: for the Mukai vector of a `μ`-stable sheaf
it is the paper's Lemma 5.1, which runs through Serre duality and
Riemann–Roch and hence through finite-dimensional `Hom`, and is not in this
repository. See #740 and #332.

## General lower bounds

Bridgeland's K3 argument uses the uniform bound `realForm b v ≥ -1` and the
rank-independent sufficient hypothesis `ω² > 2`; see Lemmas 5.1 and 6.2 of
<https://arxiv.org/abs/math/0307164>. Those constants are geometric input,
not part of the Hodge-index calculation. The calculation itself only needs

```
0 < 2 * realForm b v + r² * ω².
```

The theorems below therefore expose that sharp margin first, then derive a
rank-sensitive version from an arbitrary lower bound `realForm b v ≥ -δ`, and
only finally recover the uniform K3 statement. This also covers settings with
a stronger lower bound, such as the abelian-surface case discussed in §15 of
the same paper, without changing the charge or duplicating the proof.

For a general smooth projective surface, the usual tilted charge is written
as an integral of `exp(-(D+iH)) * ch`; see Arcara--Miles,
<https://arxiv.org/abs/1401.6149>. K3 and other K-trivial treatments may instead
package the Todd correction into the Mukai vector; see Arcara--Bertram,
<https://arxiv.org/abs/0708.2247>. This file deliberately sees neither choice:
it starts from an abstract triple and bilinear form. Todd normalization belongs
in the geometric class map that constructs that triple, not in a boolean flag
on the boundary inequality.

The arbitrary-`δ` and exact-margin statements are formal consequences of the
displayed Hodge-index estimate. They do **not** assert that every surface has a
uniform bound; a geometric child must prove whichever margin or lower-bound
hypothesis it supplies.
-/

open QuadraticMap

namespace Mukai

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (b : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (β ω : V)

/-- **The imaginary part of `Z(β,ω)`, expanded.**  The closed form claimed by
Lemma 6.2 is `im_expCharge_eq_apply_sub_smul`, immediately below; this is the
same quantity with `b ω (c - r•β)` multiplied out, which is the shape
`expCharge_apply` hands over. -/
theorem im_expCharge (hb : ∀ x y : V, b x y = b y x) (r : ℝ) (c : V) (s : ℝ) :
    (expCharge b β ω (r, c, s)).im = b ω c - r * b β ω := by
  rw [expCharge_apply b β ω hb]
  simp

/-- **`Im Z(β,ω)` IS the intersection of `c - r•β` with `ω`.**

This is the form every case of Lemma 6.2 reads: cases 1--3 conclude
`Im Z > 0` by testing `c - r•β` against `ω`, and case 4 is the boundary
`Im Z = 0`, which this makes an orthogonality outright rather than after a
rearrangement.

`im_expCharge` proves the same equation with the right-hand side multiplied
out.  Both are wanted: that one matches what `expCharge_apply` produces, this
one matches what the Hodge index theorem consumes. -/
theorem im_expCharge_eq_apply_sub_smul (hb : ∀ x y : V, b x y = b y x)
    (r : ℝ) (c : V) (s : ℝ) :
    (expCharge b β ω (r, c, s)).im = b ω (c - r • β) := by
  rw [im_expCharge b β ω hb]
  simp only [map_sub, map_smul, smul_eq_mul]
  rw [hb ω β]

/-- The orthogonality that `Im Z = 0` encodes, in the form the Hodge index
theorem consumes. -/
theorem apply_sub_smul_eq_zero_of_im_eq_zero (hb : ∀ x y : V, b x y = b y x)
    {r : ℝ} {c : V} {s : ℝ} (him : (expCharge b β ω (r, c, s)).im = 0) :
    b ω (c - r • β) = 0 := by
  rw [← im_expCharge_eq_apply_sub_smul b β ω hb r c s]
  exact him

/-- **The positive case, which is what cases 1--3 of Lemma 6.2 conclude.**

Those three cases differ only in why `c - r•β` meets `ω` positively — torsion
on a curve, torsion in dimension zero, or a torsion-free sheaf strictly above
the cutoff.  Once that is known, the charge lands in the open upper half plane
for the same one-line reason, which is this. -/
theorem im_expCharge_pos (hb : ∀ x y : V, b x y = b y x)
    {r : ℝ} {c : V} {s : ℝ} (h : 0 < b ω (c - r • β)) :
    0 < (expCharge b β ω (r, c, s)).im := by
  rw [im_expCharge_eq_apply_sub_smul b β ω hb]
  exact h

/-- The same statement without strictness, for a case that only knows the
cutoff is not crossed downward. -/
theorem im_expCharge_nonneg (hb : ∀ x y : V, b x y = b y x)
    {r : ℝ} {c : V} {s : ℝ} (h : 0 ≤ b ω (c - r • β)) :
    0 ≤ (expCharge b β ω (r, c, s)).im := by
  rw [im_expCharge_eq_apply_sub_smul b β ω hb]
  exact h

/-- **The identity Lemma 6.2's hard case rests on.**

Purely algebraic: `expCharge_apply` and `realForm_apply` unfolded, then `ring`.
The point is that it exhibits `2 * r * Re Z` as a Hodge-index term plus the
Mukai square plus `r^2 * ω^2`. -/
theorem two_mul_re_expCharge (hb : ∀ x y : V, b x y = b y x) (r : ℝ) (c : V) (s : ℝ) :
    2 * r * (expCharge b β ω (r, c, s)).re
      = -b (c - r • β) (c - r • β) + 2 * realForm b (r, c, s) + r ^ 2 * b ω ω := by
  rw [expCharge_apply b β ω hb, realForm_apply]
  simp only [map_sub, map_smul, smul_eq_mul, LinearMap.sub_apply, LinearMap.smul_apply,
    realPairing_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im]
  rw [hb c β]
  ring

section HodgeIndex

variable [FiniteDimensional ℝ V]

/-- The Hodge-index bound, specialised to the boundary. -/
theorem two_mul_re_expCharge_ge (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1) (hω : 0 < b ω ω)
    {r : ℝ} {c : V} {s : ℝ} (him : (expCharge b β ω (r, c, s)).im = 0) :
    2 * realForm b (r, c, s) + r ^ 2 * b ω ω
      ≤ 2 * r * (expCharge b β ω (r, c, s)).re := by
  have horth : polar (⇑(LinearMap.BilinMap.toQuadraticMap b)) ω (c - r • β) = 0 := by
    rw [LinearMap.BilinMap.polar_toQuadraticMap, hb (c - r • β) ω,
      apply_sub_smul_eq_zero_of_im_eq_zero b β ω hb him]
    ring
  have hnonpos : LinearMap.BilinMap.toQuadraticMap b (c - r • β) ≤ 0 :=
    PeriodDomain.nonpos_of_sigPos_eq_one _ hsigPos (u := ω) (by simpa using hω) horth
  rw [two_mul_re_expCharge b β ω hb]
  simp only [LinearMap.BilinMap.toQuadraticMap_apply] at hnonpos
  linarith

/-- **The sharp boundary-margin criterion.**

On the boundary `Im Z = 0`, Hodge index gives

`2 * realForm b v + r² * ω² ≤ 2 * r * Re Z(v)`.

Thus positive rank and positivity of the left-hand side are the exact inputs
used by this argument. No lower-bound constant, integrality of the rank, or
K3 normalization appears here. -/
theorem re_expCharge_pos_of_boundary_margin (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1) (hω : 0 < b ω ω)
    {r : ℝ} (hr : 0 < r) {c : V} {s : ℝ}
    (him : (expCharge b β ω (r, c, s)).im = 0)
    (hmargin : 0 < 2 * realForm b (r, c, s) + r ^ 2 * b ω ω) :
    0 < (expCharge b β ω (r, c, s)).re := by
  have hge := two_mul_re_expCharge_ge b β ω hb hsigPos hω him
  nlinarith

/-- **Boundary positivity from an arbitrary quadratic lower bound.**

If `realForm b v ≥ -δ`, the sharp margin is positive as soon as
`2δ < r² * ω²`. This rank-sensitive threshold is strictly more general than
the familiar K3 hypothesis `ω² > 2`: it allows any real lower bound and uses
the actual positive rank of the class.

The parameter `δ` is not required to be nonnegative. A negative value simply
records a positive lower bound for `realForm`; the two displayed hypotheses
already say exactly what the proof needs. -/
theorem re_expCharge_pos_of_lower_bound (δ : ℝ)
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1) (hω : 0 < b ω ω)
    {r : ℝ} (hr : 0 < r) {c : V} {s : ℝ}
    (him : (expCharge b β ω (r, c, s)).im = 0)
    (hv : -δ ≤ realForm b (r, c, s))
    (hthreshold : 2 * δ < r ^ 2 * b ω ω) :
    0 < (expCharge b β ω (r, c, s)).re := by
  apply re_expCharge_pos_of_boundary_margin b β ω hb hsigPos hω hr him
  linarith

/-- A rank-independent threshold for integral positive ranks.

When `1 ≤ r`, the uniform inequality `2δ < ω²` implies the rank-sensitive
condition `2δ < r² * ω²`. Geometric children whose factors have integral
positive rank can use this form; children with better rank information should
prefer `re_expCharge_pos_of_lower_bound`. -/
theorem re_expCharge_pos_of_lower_bound_of_one_le_rank (δ : ℝ)
    (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1) (hω : 0 < b ω ω)
    (hωδ : 2 * δ < b ω ω) {r : ℝ} (hr : 1 ≤ r) {c : V} {s : ℝ}
    (him : (expCharge b β ω (r, c, s)).im = 0)
    (hv : -δ ≤ realForm b (r, c, s)) :
    0 < (expCharge b β ω (r, c, s)).re := by
  have hr0 : (0 : ℝ) < r := by linarith
  have hsq : b ω ω ≤ r ^ 2 * b ω ω := by nlinarith [sq_nonneg (r - 1)]
  exact re_expCharge_pos_of_lower_bound b β ω δ hb hsigPos hω hr0 him hv
    (lt_of_lt_of_le hωδ hsq)

/-- **Lemma 6.2, non-spherical case.** A class of nonnegative Mukai square on
the boundary has `Re Z > 0`, on the strength of `ω² > 0` alone. -/
theorem re_expCharge_pos_of_nonneg (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1) (hω : 0 < b ω ω)
    {r : ℝ} (hr : 0 < r) {c : V} {s : ℝ}
    (him : (expCharge b β ω (r, c, s)).im = 0) (hv : 0 ≤ realForm b (r, c, s)) :
    0 < (expCharge b β ω (r, c, s)).re := by
  have hpos : 0 < r ^ 2 * b ω ω := by positivity
  exact re_expCharge_pos_of_lower_bound b β ω 0 hb hsigPos hω hr him (by simpa using hv)
    (by simpa using hpos)

/-- **Lemma 6.2, spherical case.** For a class of Mukai square `-1` — the
paper's `v(E)² = -2` in this repository's halved convention — the boundary
still has `Re Z > 0`, but now `ω² > 2` is needed, and it is enough only because
`1 ≤ r`. -/
theorem re_expCharge_pos_of_neg_one (hb : ∀ x y : V, b x y = b y x)
    (hsigPos : sigPos (LinearMap.BilinMap.toQuadraticMap b) = 1) (hω : 2 < b ω ω)
    {r : ℝ} (hr : 1 ≤ r) {c : V} {s : ℝ}
    (him : (expCharge b β ω (r, c, s)).im = 0) (hv : -1 ≤ realForm b (r, c, s)) :
    0 < (expCharge b β ω (r, c, s)).re := by
  have hω0 : 0 < b ω ω := by linarith
  exact re_expCharge_pos_of_lower_bound_of_one_le_rank b β ω 1 hb hsigPos hω0
    (by simpa using hω) hr him (by simpa using hv)

end HodgeIndex

end Mukai
