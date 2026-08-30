/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Numerical walls in the `(s, t)` half plane

For a surface with polarisation `H`, tilt stability is parametrised by a point
`(s, t)` with `t > 0`, and the twisted charge of a numerical class
`v = (r, c, d)` — standing for `(ch₀, ch₁·H, ch₂)` — is

```
Re Z = -d + s·c - (s²/2)·r + (t²/2)·r,      Im Z = t·(c - s·r).
```

A **numerical wall** for a pair `(v, w)` is the locus where the two charges are
real-proportional. The theorem this file is built around is that the wall
equation collapses to

```
minA·(s² + t²) + 2·minB·s + 2·minC = 0
```

where `minA, minB, minC` are the three `2 × 2` minors of the matrix with rows
`v` and `w`. So **every numerical wall is cut out by a conic with no `s·t` term
and centre on the `s`-axis** — the statement the "walls are nested semicircles"
picture rests on.

Read that as a statement about the *equation*, not about the solution set. In
the half plane `t ≠ 0` the equation has four cases, and only the first two are
walls in the geometric sense:

* `minA ≠ 0` and `minB² - 2·minA·minC > 0` — the circle centred at
  `(-minB/minA, 0)` with that radius squared over `minA²` (`wall_circle_eq`);
* `minA = 0` and `minB ≠ 0` — the vertical line `s = -minC/minB`
  (`wall_line_eq`);
* `minA ≠ 0` and `minB² - 2·minA·minC ≤ 0`, or `minA = minB = 0 ≠ minC` —
  **empty**. For the first: `v = (0, 1, 0)` and `w = (-1, 0, 1)` have minors
  `(1, 0, 1)`, so the equation is `s² + t² + 2 = 0`. At `= 0` the only
  solution has `minA·t = 0`, which `t ≠ 0` excludes;
* `minA = minB = minC = 0` — the **whole** half plane, since `wallExpr` then
  vanishes identically. `wall_subset_of_crossZero` and `wall_eq_of_meet`
  exclude this case by hypothesis for exactly that reason.

## What this is a theorem about, and what it is not

Everything here is arithmetic on triples of real numbers. There is **no**
surface: no coherent sheaf, no Chern character, no polarisation, no
Bogomolov–Gieseker inequality. `NumClass` is a triple, not `ch(E)`, and the
identification is geometry that Mathlib cannot express at the pin — CLAUDE.md
§4 closes that lane, and nothing here reopens it.

In particular **no discriminant hypothesis is assumed anywhere below**, because
none is needed: the wall equation is an identity. Where the geometric theory
would invoke Bogomolov–Gieseker, these statements simply carry the numerical
hypothesis they actually use (`minA ≠ 0`, `t ≠ 0`) as an explicit hypothesis of
the theorem. Nothing is axiomatised.

The discriminant does appear in the prose at `minorCross_eq_zero_of_two_walls`
and `wall_eq_of_meet`, to say what the charge hypothesis costs and what
nesting would need. It is discussion, not a hypothesis: no statement below
mentions it.

## Main results

* `wallExpr_eq` — the collapse. Proved as an identity, with no side conditions.
* `wall_iff_circle` — the circle/line form, for `t ≠ 0`.
* `wall_circle_eq` — centre `(-minB/minA, 0)` and radius² `(minB² - 2·minA·minC)/minA²`.
* `minA_add_smul` and friends — a wall depends only on `w` modulo `v`.
* `charge_eq_zero_iff` — where the charge degenerates, hence where all walls
  of a fixed `v` concur.
* `eq_of_two_walls` — two walls through a common point with non-proportional
  minor vectors pin down that point uniquely.
* `wall_eq_of_meet` — distinct walls of a fixed `v` are **disjoint**. This is
  the separation half of Bertram's nested wall theorem; the ordering half
  needs the discriminant and is not proved here.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

/-- A numerical class `(r, c, d)`.

A triple of reals. It is **not** `ch(E)` for a sheaf `E`; see the module
docstring. -/
abbrev NumClass : Type := ℝ × ℝ × ℝ

namespace NumClass

/-- The rank coordinate. -/
def rk (v : NumClass) : ℝ := v.1

/-- The degree coordinate, standing for `ch₁ · H`. -/
def deg (v : NumClass) : ℝ := v.2.1

/-- The second coordinate, standing for `ch₂`. -/
def ch2 (v : NumClass) : ℝ := v.2.2

end NumClass

open NumClass

/-! ### The twisted charge -/

/-- The real part of the twisted charge at `(s, t)`. -/
noncomputable def reZ (s t : ℝ) (v : NumClass) : ℝ :=
  -v.ch2 + s * v.deg - (s ^ 2 / 2) * v.rk + (t ^ 2 / 2) * v.rk

/-- The imaginary part of the twisted charge at `(s, t)`. -/
def imZ (s t : ℝ) (v : NumClass) : ℝ := t * (v.deg - s * v.rk)

/-! ### The three minors

`minA`, `minB`, `minC` are the `2 × 2` minors of `!![v.rk, v.deg, v.ch2;
w.rk, w.deg, w.ch2]`. Each is alternating and bilinear, which is what makes a
wall depend only on `w` modulo `v`. -/

/-- The rank–degree minor. -/
def minA (v w : NumClass) : ℝ := v.rk * w.deg - v.deg * w.rk

/-- The `ch₂`–rank minor. -/
def minB (v w : NumClass) : ℝ := v.ch2 * w.rk - v.rk * w.ch2

/-- The degree–`ch₂` minor. -/
def minC (v w : NumClass) : ℝ := v.deg * w.ch2 - v.ch2 * w.deg

/-- The wall expression: the cross product of the two charges, which vanishes
exactly when they are real-proportional. -/
noncomputable def wallExpr (s t : ℝ) (v w : NumClass) : ℝ :=
  reZ s t v * imZ s t w - imZ s t v * reZ s t w

/-! ### The collapse

The whole geometry of numerical walls follows from this one identity. -/

/-- **The wall expression collapses to a circle equation.**

An identity: no hypothesis on `s`, `t`, `v` or `w`. Everything quadratic in
`s` and `t` beyond `s² + t²` cancels. -/
theorem wallExpr_eq (s t : ℝ) (v w : NumClass) :
    wallExpr s t v w
      = t * (minC v w + s * minB v w + ((s ^ 2 + t ^ 2) / 2) * minA v w) := by
  simp only [wallExpr, reZ, imZ, minA, minB, minC, rk, deg, ch2]
  ring

/-- For `t ≠ 0` the wall is cut out by a circle equation in `(s, t)`. -/
theorem wall_iff_circle {s t : ℝ} (ht : t ≠ 0) (v w : NumClass) :
    wallExpr s t v w = 0 ↔
      minA v w * (s ^ 2 + t ^ 2) + 2 * minB v w * s + 2 * minC v w = 0 := by
  rw [wallExpr_eq, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h ht
    · linarith
  · intro h
    exact Or.inr (by linarith)

/-- **Centre and radius.** When the rank–degree minor is nonzero the wall is
the circle centred at `(-minB/minA, 0)` with radius squared
`(minB² - 2·minA·minC)/minA²`.

Stated in cleared form — both sides multiplied through by `minA²` — so that no
division appears and the equivalence is an honest polynomial identity plus one
use of `minA ≠ 0`. -/
theorem wall_circle_eq {s t : ℝ} (ht : t ≠ 0) {v w : NumClass}
    (hA : minA v w ≠ 0) :
    wallExpr s t v w = 0 ↔
      (minA v w * s + minB v w) ^ 2 + (minA v w * t) ^ 2
        = minB v w ^ 2 - 2 * minA v w * minC v w := by
  rw [wall_iff_circle ht]
  constructor
  · intro h
    linear_combination (minA v w) * h
  · intro h
    have key : minA v w *
        (minA v w * (s ^ 2 + t ^ 2) + 2 * minB v w * s + 2 * minC v w) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp key).resolve_left hA

/-- A vertical wall: when the rank–degree minor vanishes but the `ch₂`–rank one
does not, the wall is the line `s = -minC/minB`. -/
theorem wall_line_eq {s t : ℝ} (ht : t ≠ 0) {v w : NumClass}
    (hA : minA v w = 0) (hB : minB v w ≠ 0) :
    wallExpr s t v w = 0 ↔ s = -(minC v w) / minB v w := by
  rw [wall_iff_circle ht, hA]
  rw [eq_div_iff hB]
  constructor <;> intro h <;> linarith

/-! ### A wall sees only `w` modulo `v`

Each minor is alternating, so adding a multiple of `v` to `w` changes nothing.
This is why walls are indexed by classes modulo `v` rather than by classes. -/

/-- Scalar shift of `w` by `v`, componentwise. -/
def shift (k : ℝ) (v w : NumClass) : NumClass :=
  (w.rk + k * v.rk, w.deg + k * v.deg, w.ch2 + k * v.ch2)

@[simp]
theorem minA_shift (k : ℝ) (v w : NumClass) : minA v (shift k v w) = minA v w := by
  simp only [minA, shift, rk, deg]; ring

@[simp]
theorem minB_shift (k : ℝ) (v w : NumClass) : minB v (shift k v w) = minB v w := by
  simp only [minB, shift, rk, ch2]; ring

@[simp]
theorem minC_shift (k : ℝ) (v w : NumClass) : minC v (shift k v w) = minC v w := by
  simp only [minC, shift, deg, ch2]; ring

/-- The wall for `w` and for `w + k·v` is the same wall. -/
theorem wallExpr_shift (s t k : ℝ) (v w : NumClass) :
    wallExpr s t v (shift k v w) = wallExpr s t v w := by
  rw [wallExpr_eq, wallExpr_eq, minA_shift, minB_shift, minC_shift]

/-! ### The minor vector is orthogonal to `v`

The fact that makes disjointness true, and the one the "two walls through one
point" section below does without.

`(minA, minB, minC)` is the cross product `v × w` with its coordinates
reversed: `(v × w) = (minC, minB, minA)`. A cross product is orthogonal to
both factors, so every minor vector built from a **common** `v` lies in the
plane `v^⊥`. Two of them plus one more linear condition is three conditions on
a 3-dimensional space, and generically that forces proportionality — which is
the whole content of `minorCross_eq_zero_of_two_walls`. -/

/-- **The minor vector is orthogonal to `v`.**

Stated with the coordinates paired as they actually appear — `ch₂` against
`minA`, `deg` against `minB`, `rk` against `minC` — because
`(minA, minB, minC)` is the cross product with coordinates *reversed*. -/
theorem minor_orth (v w : NumClass) :
    v.ch2 * minA v w + v.deg * minB v w + v.rk * minC v w = 0 := by
  simp only [minA, minB, minC, rk, deg, ch2]; ring

/-! ### Degeneracy of the charge -/

/-- The charge of `v` vanishes at `(s, t)`, `t ≠ 0`, exactly when `v` is the
rank-scaled point `r · (1, s, (s² + t²)/2)`.

This locus is **not** where a wall stops being a circle — that is governed by
the minors, and the module docstring lists the four cases. It is where *every*
wall of `v` passes through at once: at such a point `minor_orth` turns the
wall equation into an identity, so no `w` is excluded and the walls of `v`
concur. `wall_eq_of_meet_needs_charge` exhibits that failure explicitly, and it
is the locus the geometric theory excludes. -/
theorem charge_eq_zero_iff {s t : ℝ} (ht : t ≠ 0) (v : NumClass) :
    (reZ s t v = 0 ∧ imZ s t v = 0) ↔
      (v.deg = s * v.rk ∧ v.ch2 = ((s ^ 2 + t ^ 2) / 2) * v.rk) := by
  simp only [reZ, imZ, rk, deg, ch2]
  constructor
  · rintro ⟨hre, him⟩
    have hd : v.2.1 - s * v.1 = 0 := (mul_eq_zero.mp him).resolve_left ht
    refine ⟨by linarith, ?_⟩
    linear_combination (-1 : ℝ) * hre + s * hd
  · rintro ⟨hd, hc⟩
    constructor
    · rw [hd, hc]; ring
    · rw [hd]; ring

/-! ### Two walls through one point

If two walls meet at `(s, t)` and their minor vectors are **not** proportional
in the `(A, B)` slot, then that meeting point is forced. This is the algebraic
half of "walls for a fixed `v` are disjoint".

The disjointness theorem follows, and is proved in the next section. It needs
exactly the extra input this section lacks: that both minor vectors are cross
products against a **common** `v`, hence both orthogonal to it. That is
`minor_orth`, and it is a one-line `ring` identity. -/

/-- Two walls meeting at a common point determine `s` and `s² + t²`, provided
the `(A, B)` cross term is nonzero. -/
theorem eq_of_two_walls {s t : ℝ} (ht : t ≠ 0) {v w₁ w₂ : NumClass}
    (h₁ : wallExpr s t v w₁ = 0) (h₂ : wallExpr s t v w₂ = 0)
    (hD : minA v w₁ * minB v w₂ - minA v w₂ * minB v w₁ ≠ 0) :
    s = -(minA v w₁ * minC v w₂ - minA v w₂ * minC v w₁)
          / (minA v w₁ * minB v w₂ - minA v w₂ * minB v w₁) := by
  rw [wall_iff_circle ht] at h₁ h₂
  rw [eq_div_iff hD]
  linear_combination (-(minA v w₂) / 2) * h₁ + (minA v w₁ / 2) * h₂

/-! ## Disjointness of the walls of a fixed class

Two distinct walls for the same `v` never meet — away from the locus where
`v`'s own charge degenerates, which `charge_eq_zero_iff` already identifies.
This is the separation half of Bertram's nested wall theorem; the ordering
half is discussed at `wall_eq_of_meet` and is not proved here.

The proof is four linear eliminations and no geometry. Write `Aᵢ, Bᵢ, Cᵢ` for
the minors of `(v, wᵢ)` and `u = s² + t²`. A meeting point gives two circle
equations; `minor_orth` gives two orthogonality relations:

```
Aᵢ·u + 2Bᵢ·s + 2Cᵢ = 0        (both walls pass through (s, t))
ch₂·Aᵢ + deg·Bᵢ + rk·Cᵢ = 0    (minor_orth, the common v)
```

Eliminating pairwise turns those four into

```
(deg − s·rk)·crossAB = 0     and     (ch₂ − (u/2)·rk)·crossAB = 0
```

and `charge_eq_zero_iff` says those two coefficients vanish **together**
exactly when `v`'s charge vanishes at `(s, t)`. So off that locus
`crossAB = 0`, and the other two cross terms follow immediately.

The `ℝ³` rank argument the previous section's docstring anticipated is
therefore never needed as such: the two orthogonality relations do its work,
and the degenerate case comes out as an explicit hypothesis rather than as a
genericity assumption. -/

/-- The `A`–`B` cross term of the two minor vectors. Vanishing of all three
cross terms is exactly proportionality. -/
def crossAB (v w₁ w₂ : NumClass) : ℝ := minA v w₁ * minB v w₂ - minA v w₂ * minB v w₁

/-- The `A`–`C` cross term of the two minor vectors. -/
def crossAC (v w₁ w₂ : NumClass) : ℝ := minA v w₁ * minC v w₂ - minA v w₂ * minC v w₁

/-- The `B`–`C` cross term of the two minor vectors. -/
def crossBC (v w₁ w₂ : NumClass) : ℝ := minB v w₁ * minC v w₂ - minB v w₂ * minC v w₁

/-! The three cross terms are antisymmetric in `w₁`, `w₂`. That is what lets
`wall_eq_of_meet` get its reverse inclusion from the same lemma.

**Deliberately not `@[simp]`.** An antisymmetry lemma whose two sides are the
same head symbol with permuted arguments rewrites forever: `simp` takes
`crossAB v w₂ w₁` to `-crossAB v w₁ w₂`, then the inner term back again. Marking
these `@[simp]` was the first version here, and `lake exe runLinter` rejected
all three with `maximum recursion depth has been reached` -- a loop `lake build`
does not see, because nothing in this file happened to call `simp` on one. -/

theorem crossAB_swap (v w₁ w₂ : NumClass) :
    crossAB v w₂ w₁ = -crossAB v w₁ w₂ := by simp only [crossAB]; ring

theorem crossAC_swap (v w₁ w₂ : NumClass) :
    crossAC v w₂ w₁ = -crossAC v w₁ w₂ := by simp only [crossAC]; ring

theorem crossBC_swap (v w₁ w₂ : NumClass) :
    crossBC v w₂ w₁ = -crossBC v w₁ w₂ := by simp only [crossBC]; ring

/-- **The disjointness theorem, algebraic core.** Two walls for the same `v`
that meet at a point where `v`'s charge does not vanish have proportional
minor vectors — so they are the same wall.

The charge hypothesis is not a genericity dodge, and it costs less than it
looks. Solving `charge_eq_zero_iff` for `v` of nonzero rank gives
`s = deg/rk` and `t² = -(deg² - 2·rk·ch₂)/rk²`, so writing `Δ` for the
Bogomolov–Gieseker discriminant `deg² - 2·rk·ch₂` the excluded locus is

* a single point of each half plane when `Δ < 0`, and
* **empty** when `Δ ≥ 0`.

Bogomolov–Gieseker puts the geometric classes in the second case, where the
hypothesis holds automatically. It is stated as a hypothesis rather than
derived because `Δ ≥ 0` is a theorem about sheaves and `NumClass` is a triple;
see the module docstring. -/
theorem minorCross_eq_zero_of_two_walls {s t : ℝ} (ht : t ≠ 0) {v w₁ w₂ : NumClass}
    (hv : ¬(reZ s t v = 0 ∧ imZ s t v = 0))
    (h₁ : wallExpr s t v w₁ = 0) (h₂ : wallExpr s t v w₂ = 0) :
    crossAB v w₁ w₂ = 0 ∧ crossAC v w₁ w₂ = 0 ∧ crossBC v w₁ w₂ = 0 := by
  rw [wall_iff_circle ht] at h₁ h₂
  have o₁ := minor_orth v w₁
  have o₂ := minor_orth v w₂
  -- The two eliminations. Each is a linear combination of the four hypotheses.
  have key₁ : (v.deg - s * v.rk) * crossAB v w₁ w₂ = 0 := by
    simp only [crossAB]
    linear_combination (minA v w₁) * o₂ - (minA v w₂) * o₁
      - (v.rk / 2) * (minA v w₁ * h₂ - minA v w₂ * h₁)
  have key₂ : (v.ch2 - ((s ^ 2 + t ^ 2) / 2) * v.rk) * crossAB v w₁ w₂ = 0 := by
    simp only [crossAB]
    linear_combination (minB v w₂) * o₁ - (minB v w₁) * o₂
      - (v.rk / 2) * (minB v w₂ * h₁ - minB v w₁ * h₂)
  -- `hv`, read through `charge_eq_zero_iff`, says the two coefficients above
  -- are not both zero.
  have hv' : ¬(v.deg = s * v.rk ∧ v.ch2 = ((s ^ 2 + t ^ 2) / 2) * v.rk) := fun h =>
    hv ((charge_eq_zero_iff ht v).mpr h)
  have hAB : crossAB v w₁ w₂ = 0 := by
    by_cases hd : v.deg = s * v.rk
    · have hc : v.ch2 - ((s ^ 2 + t ^ 2) / 2) * v.rk ≠ 0 := fun h =>
        hv' ⟨hd, by linarith⟩
      exact (mul_eq_zero.mp key₂).resolve_left hc
    · have hc : v.deg - s * v.rk ≠ 0 := fun h => hd (by linarith)
      exact (mul_eq_zero.mp key₁).resolve_left hc
  refine ⟨hAB, ?_, ?_⟩
  · -- `s · crossAB + crossAC = 0`, from the two circle equations alone.
    simp only [crossAB] at hAB
    simp only [crossAC]
    linear_combination (minA v w₁ / 2) * h₂ - (minA v w₂ / 2) * h₁ - s * hAB
  · -- `u · crossAB = 2 · crossBC`, likewise.
    simp only [crossAB] at hAB
    simp only [crossBC]
    linear_combination ((s ^ 2 + t ^ 2) / 2) * hAB
      - (minB v w₂ / 2) * h₁ + (minB v w₁ / 2) * h₂

/-! ### From proportional minors to equal loci

With the cross terms gone, each coordinate of one minor vector times the other
wall's circle expression is symmetric. So a single nonzero coordinate of `w₁`'s
minor vector is enough to push `w₁`'s wall into `w₂`'s, and the reverse
inclusion is the same lemma with the arguments swapped — the cross terms are
antisymmetric, so they stay zero. -/

/-- One inclusion. If the cross terms vanish and `w₁`'s minor vector is not the
zero vector, every point of `w₁`'s wall is a point of `w₂`'s. -/
theorem wall_subset_of_crossZero {v w₁ w₂ : NumClass}
    (hAB : crossAB v w₁ w₂ = 0) (hAC : crossAC v w₁ w₂ = 0) (hBC : crossBC v w₁ w₂ = 0)
    (hn : ¬(minA v w₁ = 0 ∧ minB v w₁ = 0 ∧ minC v w₁ = 0))
    {s t : ℝ} (ht : t ≠ 0) (h : wallExpr s t v w₁ = 0) :
    wallExpr s t v w₂ = 0 := by
  rw [wall_iff_circle ht] at h ⊢
  simp only [crossAB] at hAB
  simp only [crossAC] at hAC
  simp only [crossBC] at hBC
  -- For each coordinate `X`, `X₁ · circ₂ = X₂ · circ₁`; the right side is `0`.
  by_cases hA : minA v w₁ = 0
  · by_cases hB : minB v w₁ = 0
    · have hC : minC v w₁ ≠ 0 := fun hC => hn ⟨hA, hB, hC⟩
      have : minC v w₁ * (minA v w₂ * (s ^ 2 + t ^ 2) + 2 * minB v w₂ * s
          + 2 * minC v w₂) = 0 := by
        linear_combination (-(s ^ 2 + t ^ 2)) * hAC - 2 * s * hBC + minC v w₂ * h
      exact (mul_eq_zero.mp this).resolve_left hC
    · have : minB v w₁ * (minA v w₂ * (s ^ 2 + t ^ 2) + 2 * minB v w₂ * s
          + 2 * minC v w₂) = 0 := by
        linear_combination (-(s ^ 2 + t ^ 2)) * hAB + 2 * hBC + minB v w₂ * h
      exact (mul_eq_zero.mp this).resolve_left hB
  · have : minA v w₁ * (minA v w₂ * (s ^ 2 + t ^ 2) + 2 * minB v w₂ * s
        + 2 * minC v w₂) = 0 := by
      linear_combination 2 * s * hAB + 2 * hAC + minA v w₂ * h
    exact (mul_eq_zero.mp this).resolve_left hA

/-- **Disjointness of the walls of a fixed class — the separation half of
Bertram's nested wall theorem.** Two walls for the same numerical class `v`
that meet at a single point, away from the degenerate locus of `v`'s own
charge, are the **same wall** — they agree at every point of the half plane.

Contrapositively: distinct numerical walls for a fixed `v` are disjoint.

**Disjointness is not yet nesting**, and the gap is stated rather than
narrated. Nesting is an ordering claim — that of any two walls one lies inside
the other — and disjoint circles centred on a common axis can equally well sit
side by side. What rules that out is that the walls of a fixed `v` form a
coaxial *pencil*: `minor_orth` writes every wall of `v` of nonzero rank as
`minA·((s² + t²) - 2·ch₂/rk) + 2·minB·(s - deg/rk) = 0`, so all of them pass
through the base locus of `charge_eq_zero_iff`, and a coaxial pencil with no
real base point is nested. That base point is real exactly when the
Bogomolov–Gieseker discriminant is negative, so nesting needs the discriminant
input this file declines to assume — see the module docstring. Only the
disjointness clause is proved here.

Both minor vectors are required to be nonzero. A zero minor vector is not a
wall — `wallExpr` vanishes identically — so excluding it excludes nothing the
statement is about. -/
theorem wall_eq_of_meet {s t : ℝ} (ht : t ≠ 0) {v w₁ w₂ : NumClass}
    (hv : ¬(reZ s t v = 0 ∧ imZ s t v = 0))
    (h₁ : wallExpr s t v w₁ = 0) (h₂ : wallExpr s t v w₂ = 0)
    (hn₁ : ¬(minA v w₁ = 0 ∧ minB v w₁ = 0 ∧ minC v w₁ = 0))
    (hn₂ : ¬(minA v w₂ = 0 ∧ minB v w₂ = 0 ∧ minC v w₂ = 0))
    {s' t' : ℝ} (ht' : t' ≠ 0) :
    wallExpr s' t' v w₁ = 0 ↔ wallExpr s' t' v w₂ = 0 := by
  obtain ⟨hAB, hAC, hBC⟩ := minorCross_eq_zero_of_two_walls ht hv h₁ h₂
  have hAB' : crossAB v w₂ w₁ = 0 := by rw [crossAB_swap, hAB, neg_zero]
  have hAC' : crossAC v w₂ w₁ = 0 := by rw [crossAC_swap, hAC, neg_zero]
  have hBC' : crossBC v w₂ w₁ = 0 := by rw [crossBC_swap, hBC, neg_zero]
  exact ⟨wall_subset_of_crossZero hAB hAC hBC hn₁ ht',
         wall_subset_of_crossZero hAB' hAC' hBC' hn₂ ht'⟩

/-! ### The charge hypothesis is load-bearing

`wall_eq_of_meet` excludes the point where `v`'s own charge vanishes. That is
not a technical convenience, and the exclusion is not vacuous either way — the
witnesses below are explicit.

Take `v = (2, 0, 1)` and the point `(s, t) = (0, 1)`. Then `reZ = -1 + 1 = 0`
and `imZ = 0`, so the charge degenerates there; and the wall equation
`minA·(s² + t²) + 2·minB·s + 2·minC = 0` becomes `minA + 2·minC = 0`, which
`minor_orth` makes automatic for **every** `w`. So at that one point *all*
walls of `v` meet, and disjointness fails as badly as it possibly could.

That `v` is exactly a class the geometric theory excludes: its discriminant is
`deg² - 2·rk·ch₂ = 0 - 2·2·1 = -4 < 0`, which no Bogomolov–Gieseker semistable
class has. The hypothesis is load-bearing here and vacuous there.

`w₁ = (0, 1, 0)` gives the unit circle and `w₂ = (1, 0, 0)` the line `s = 0`.
They meet at `(0, 1)`, both minor vectors are nonzero, and they are different
walls — `(0, 2)` is on the second and not the first. Every hypothesis of
`wall_eq_of_meet` except the charge one holds. -/

/-- The degenerate class of the worked counterexample: `v = (2, 0, 1)`. -/
def degV : NumClass := (2, 0, 1)

/-- `v`'s charge really does vanish at `(0, 1)`. -/
theorem degV_charge_eq_zero : reZ 0 1 degV = 0 ∧ imZ 0 1 degV = 0 := by
  constructor <;> norm_num [reZ, imZ, degV, rk, deg, ch2]

/-- **Dropping the charge hypothesis makes `wall_eq_of_meet` false.** Two walls
of `degV` with nonzero minor vectors meet at `(0, 1)` and disagree at `(0, 2)`. -/
theorem wall_eq_of_meet_needs_charge :
    ∃ w₁ w₂ : NumClass,
      wallExpr 0 1 degV w₁ = 0 ∧ wallExpr 0 1 degV w₂ = 0 ∧
      ¬(minA degV w₁ = 0 ∧ minB degV w₁ = 0 ∧ minC degV w₁ = 0) ∧
      ¬(minA degV w₂ = 0 ∧ minB degV w₂ = 0 ∧ minC degV w₂ = 0) ∧
      wallExpr 0 2 degV w₂ = 0 ∧ wallExpr 0 2 degV w₁ ≠ 0 := by
  refine ⟨(0, 1, 0), (1, 0, 0), ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [wallExpr, reZ, imZ, minA, minB, minC, degV, rk, deg, ch2]

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
