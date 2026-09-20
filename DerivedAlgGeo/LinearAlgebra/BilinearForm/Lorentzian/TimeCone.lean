/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.BilinearForm.HodgeIndex

/-!
# The time cone of a Hodge-definite pairing

`HodgeIndex.lean` gives a `DivisorSpace` — a real vector space with a symmetric
pairing — and `HodgeDefinite e`, which says `e² > 0` together with negative
definiteness on `e^⊥`.  A pairing carrying that certificate is Lorentzian, and
this file records the structure that follows from it alone: the splitting of a
vector into a coordinate along `e` and a part orthogonal to `e`, the sign
identity that splitting produces, and the two inequalities that run opposite to
their Euclidean counterparts.

## What is proved

* `pair_self_eq_timeCoord_sq_add` — the splitting identity
  `x² = t(x)² + s(x)²` for a unit reference vector, where `spacePart_self_nonpos`
  gives `s(x)² ≤ 0`.  So the coordinate along `e` dominates:
  `pair_self_le_timeCoord_sq`.
* `pair_mul_pair_le_sq` — **reverse Cauchy–Schwarz**, `x² · y² ≤ ⟨x, y⟩²`
  whenever `x² > 0`.  The inequality points the other way from the Euclidean
  one, and it is immediate from the existing `HodgeDefinite.of_pair_pos` and
  `HodgeDefinite.toHodgeIndex`: a vector of positive square carries its own
  Hodge certificate, and `HodgeIndex.index_le` at that vector is the statement.
* `pair_pos_of_isFuture` — two vectors of positive square with positive
  coordinate along `e` pair positively.  The proof is elementary and avoids
  Cauchy–Schwarz on `e^⊥` entirely: the explicit combination
  `t(y) • x - t(x) • y` is orthogonal to `e`, so its square is nonpositive, and
  expanding that square *is* the inequality.
* `sqrt_add_sqrt_le_sqrt_pair_add` — the **reverse triangle inequality**, the
  statement the cone exists to carry.

## What is not here

No `Lorentzian` structure, class or certificate is introduced.  `HodgeDefinite e`
is carried as a hypothesis on each theorem, so this file adds no new carrier and
nothing downstream has a new obligation.  Unit normalization `e² = 1` is likewise
a per-theorem hypothesis rather than a field; a caller with `e² > 0` rescales.

Nothing here is named for Minkowski space, for special relativity, or for any
surface.  `IsFuture` is a predicate on a pair of vectors in a real quadratic
space, and no claim is made that it is the set of ample classes of anything.

The diagonal model `diag(1, -1, …, -1)` and its Hodge certificate are a separate
concern and are not in this file.
-/

universe w

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

noncomputable section

variable {D : Type w} [AddCommGroup D] [Module ℝ D]

namespace DivisorSpace

variable (S : DivisorSpace D)

/-! ### Bilinearity of the pairing

`HodgeIndex.lean` exposes `pair` with symmetry and the two zero lemmas, and
expands bilinearity inline where it needs it.  These stay `private`: promoting
them is a change to the owner of `pair`, and the repository asks for two
independent consumers before a root moves. -/

private theorem pair_add_left (x y z : D) :
    S.pair (x + y) z = S.pair x z + S.pair y z := by
  simp only [pair, map_add, LinearMap.add_apply]

private theorem pair_add_right (x y z : D) :
    S.pair x (y + z) = S.pair x y + S.pair x z := by
  simp only [pair, map_add]

private theorem pair_sub_left (x y z : D) :
    S.pair (x - y) z = S.pair x z - S.pair y z := by
  simp only [pair, map_sub, LinearMap.sub_apply]

private theorem pair_sub_right (x y z : D) :
    S.pair x (y - z) = S.pair x y - S.pair x z := by
  simp only [pair, map_sub]

private theorem pair_smul_left (a : ℝ) (x y : D) :
    S.pair (a • x) y = a * S.pair x y := by
  simp only [pair, map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem pair_smul_right (a : ℝ) (x y : D) :
    S.pair x (a • y) = a * S.pair x y := by
  simp only [pair, map_smul, smul_eq_mul]

/-- Expansion of the square of a sum. -/
private theorem pair_self_add (x y : D) :
    S.pair (x + y) (x + y) = S.pair x x + 2 * S.pair x y + S.pair y y := by
  simp only [S.pair_add_left, S.pair_add_right]
  rw [S.pair_comm y x]
  ring

/-! ### The orthogonal splitting -/

/-- The coordinate of `x` along a reference vector `e`. -/
def timeCoord (e x : D) : ℝ := S.pair e x

/-- The part of `x` orthogonal to a unit reference vector `e`. -/
def spacePart (e x : D) : D := x - S.timeCoord e x • e

theorem timeCoord_apply (e x : D) : S.timeCoord e x = S.pair e x := rfl

theorem spacePart_apply (e x : D) :
    S.spacePart e x = x - S.timeCoord e x • e := rfl

/-- The splitting recovers the vector it split. -/
theorem timeCoord_smul_add_spacePart (e x : D) :
    S.timeCoord e x • e + S.spacePart e x = x := by
  simp only [spacePart]
  abel

/-- The space part is orthogonal to a unit reference vector. -/
theorem pair_spacePart_eq_zero {e : D} (he : S.pair e e = 1) (x : D) :
    S.pair e (S.spacePart e x) = 0 := by
  simp only [spacePart, timeCoord, S.pair_sub_right, S.pair_smul_right, he, mul_one,
    sub_self]

/-- The splitting identity: the square of a vector is the square of its
coordinate along a unit `e` plus the square of its space part. -/
theorem pair_self_eq_timeCoord_sq_add {e : D} (he : S.pair e e = 1) (x : D) :
    S.pair x x
      = S.timeCoord e x ^ 2 + S.pair (S.spacePart e x) (S.spacePart e x) := by
  have hs : S.pair (S.spacePart e x) (S.spacePart e x)
      = S.pair x x - S.timeCoord e x ^ 2 := by
    simp only [spacePart, timeCoord, S.pair_sub_left, S.pair_sub_right,
      S.pair_smul_left, S.pair_smul_right, he]
    rw [S.pair_comm x e]
    ring
  rw [hs]
  ring

/-- The space part of any vector has nonpositive square. -/
theorem spacePart_self_nonpos {e : D} (h : S.HodgeDefinite e)
    (he : S.pair e e = 1) (x : D) :
    S.pair (S.spacePart e x) (S.spacePart e x) ≤ 0 :=
  h.toHodgeIndex.pair_self_nonpos_of_orthogonal (S.pair_spacePart_eq_zero he x)

/-- The coordinate along `e` dominates the square. -/
theorem pair_self_le_timeCoord_sq {e : D} (h : S.HodgeDefinite e)
    (he : S.pair e e = 1) (x : D) :
    S.pair x x ≤ S.timeCoord e x ^ 2 := by
  have hsplit := S.pair_self_eq_timeCoord_sq_add he x
  have hnonpos := S.spacePart_self_nonpos h he x
  linarith

/-! ### Reverse Cauchy–Schwarz -/

/-- **Reverse Cauchy–Schwarz.**  On a Hodge-definite pairing, a vector of
positive square satisfies the Cauchy–Schwarz inequality with the sense
reversed, against *every* other vector.

No unit normalization is needed: `HodgeDefinite.of_pair_pos` transports the
certificate from `e` to `x`, and `HodgeIndex.index_le` at `x` is the statement.

`FiniteDimensional ℝ D` is inherited from `HodgeDefinite.of_pair_pos`, which
routes through the signature theory of the associated quadratic form.  It is
the only finite-dimensionality hypothesis in this file, and the future-cone
results below deliberately do not depend on it: `sqrt_mul_sqrt_le_pair` proves
the special case they need by an elementary argument instead. -/
theorem pair_mul_pair_le_sq [FiniteDimensional ℝ D] {e : D}
    (h : S.HodgeDefinite e) {x : D} (hx : 0 < S.pair x x) (y : D) :
    S.pair x x * S.pair y y ≤ S.pair x y ^ 2 :=
  (h.of_pair_pos hx).toHodgeIndex.index_le y

/-! ### The future cone -/

/-- `x` lies in the future cone of `e`: it has positive square and positive
coordinate along `e`.

This is a predicate on two vectors of a real quadratic space.  It is not
claimed to describe an ample cone, a positive cone, or any geometric locus. -/
def IsFuture (e x : D) : Prop := 0 < S.pair x x ∧ 0 < S.timeCoord e x

theorem isFuture_iff (e x : D) :
    S.IsFuture e x ↔ 0 < S.pair x x ∧ 0 < S.pair e x := Iff.rfl

/-- A positive multiple of a future vector is a future vector. -/
theorem isFuture_smul {e x : D} (hx : S.IsFuture e x) {a : ℝ} (ha : 0 < a) :
    S.IsFuture e (a • x) := by
  obtain ⟨hxx, hax⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [S.pair_smul_left, S.pair_smul_right]
    positivity
  · simp only [timeCoord, S.pair_smul_right] at hax ⊢
    positivity

/-- The one computation both future-cone inequalities run on.

With `a` and `b` the coordinates of `x` and `y` along `e`, the combination
`b • x - a • y` is orthogonal to `e`, so the caller's certificate makes its
square nonpositive.  Expanding that square is the displayed inequality.  No
unit normalization and no finite-dimensionality is used. -/
private theorem futureCombination_le {e : D} (h : S.HodgeDefinite e)
    {x y : D} (hx : S.IsFuture e x) (hy : S.IsFuture e y) :
    0 < S.pair e x * S.pair e y ∧
      S.pair e y ^ 2 * S.pair x x + S.pair e x ^ 2 * S.pair y y
        ≤ 2 * (S.pair e x * S.pair e y) * S.pair x y := by
  have hax : 0 < S.pair e x := hx.2
  have hby : 0 < S.pair e y := hy.2
  refine ⟨mul_pos hax hby, ?_⟩
  set a : ℝ := S.pair e x with ha
  set b : ℝ := S.pair e y with hb
  have horth : S.pair e (b • x - a • y) = 0 := by
    simp only [S.pair_sub_right, S.pair_smul_right, ← ha, ← hb]
    ring
  have hnonpos : S.pair (b • x - a • y) (b • x - a • y) ≤ 0 :=
    h.toHodgeIndex.pair_self_nonpos_of_orthogonal horth
  have hexp : S.pair (b • x - a • y) (b • x - a • y)
      = b ^ 2 * S.pair x x - 2 * (a * b) * S.pair x y + a ^ 2 * S.pair y y := by
    simp only [S.pair_sub_left, S.pair_sub_right, S.pair_smul_left,
      S.pair_smul_right]
    rw [S.pair_comm y x]
    ring
  rw [hexp] at hnonpos
  linarith

/-- **Two future vectors pair positively.**

The witness is explicit: with `a` and `b` the coordinates of `x` and `y` along
`e`, the combination `b • x - a • y` is orthogonal to `e`, so Hodge definiteness
makes its square nonpositive.  Expanding that square gives
`b² x² + a² y² ≤ 2ab ⟨x, y⟩`, and the left side is positive. -/
theorem pair_pos_of_isFuture {e : D} (h : S.HodgeDefinite e)
    {x y : D} (hx : S.IsFuture e x) (hy : S.IsFuture e y) :
    0 < S.pair x y := by
  obtain ⟨hab, hnonpos⟩ := S.futureCombination_le h hx hy
  have h1 : 0 < S.pair e y ^ 2 * S.pair x x := mul_pos (pow_pos hy.2 2) hx.1
  have h2 : 0 < S.pair e x ^ 2 * S.pair y y := mul_pos (pow_pos hx.2 2) hy.1
  by_contra hcon
  rw [not_lt] at hcon
  nlinarith [hab, hcon, h1, h2]

/-- The future cone is closed under addition. -/
theorem isFuture_add {e : D} (h : S.HodgeDefinite e)
    {x y : D} (hx : S.IsFuture e x) (hy : S.IsFuture e y) :
    S.IsFuture e (x + y) := by
  have hxy := S.pair_pos_of_isFuture h hx hy
  refine ⟨?_, ?_⟩
  · rw [S.pair_self_add]
    linarith [hx.1, hy.1]
  · have hax := hx.2
    have hby := hy.2
    simp only [timeCoord, S.pair_add_right] at hax hby ⊢
    linarith

/-! ### The reverse triangle inequality -/

/-- The product of the lengths of two future vectors is at most their pairing.

Proved from `futureCombination_le` and the arithmetic-geometric mean
inequality — in the form `(b·A - a·B)² ≥ 0` for `A`, `B` the two lengths —
rather than from `pair_mul_pair_le_sq`, so that no finite-dimensionality
hypothesis reaches the reverse triangle inequality below. -/
theorem sqrt_mul_sqrt_le_pair {e : D} (h : S.HodgeDefinite e)
    {x y : D} (hx : S.IsFuture e x) (hy : S.IsFuture e y) :
    Real.sqrt (S.pair x x) * Real.sqrt (S.pair y y) ≤ S.pair x y := by
  obtain ⟨hab, hle⟩ := S.futureCombination_le h hx hy
  have hxsq : Real.sqrt (S.pair x x) ^ 2 = S.pair x x := Real.sq_sqrt hx.1.le
  have hysq : Real.sqrt (S.pair y y) ^ 2 = S.pair y y := Real.sq_sqrt hy.1.le
  nlinarith [hab, hle, hxsq, hysq,
    sq_nonneg (S.pair e y * Real.sqrt (S.pair x x)
      - S.pair e x * Real.sqrt (S.pair y y))]

/-- **The reverse triangle inequality.**  On a Hodge-definite pairing the
length of a sum of future vectors is at least the sum of their lengths — the
opposite of the Euclidean inequality. -/
theorem sqrt_add_sqrt_le_sqrt_pair_add {e : D} (h : S.HodgeDefinite e)
    {x y : D} (hx : S.IsFuture e x) (hy : S.IsFuture e y) :
    Real.sqrt (S.pair x x) + Real.sqrt (S.pair y y)
      ≤ Real.sqrt (S.pair (x + y) (x + y)) := by
  have hprod := S.sqrt_mul_sqrt_le_pair h hx hy
  have hxy := S.pair_pos_of_isFuture h hx hy
  have hxsq : Real.sqrt (S.pair x x) ^ 2 = S.pair x x := Real.sq_sqrt hx.1.le
  have hysq : Real.sqrt (S.pair y y) ^ 2 = S.pair y y := Real.sq_sqrt hy.1.le
  have hnonneg : 0 ≤ Real.sqrt (S.pair x x) + Real.sqrt (S.pair y y) := by
    positivity
  rw [show S.pair (x + y) (x + y)
      = S.pair x x + 2 * S.pair x y + S.pair y y from S.pair_self_add x y]
  rw [Real.le_sqrt hnonneg (by linarith [hx.1, hy.1])]
  nlinarith [hprod, hxsq, hysq]

end DivisorSpace

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial
