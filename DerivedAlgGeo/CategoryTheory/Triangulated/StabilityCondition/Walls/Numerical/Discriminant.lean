/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical.Basic

/-!
# The Bogomolov discriminant of a numerical class

For `v = (r, c, d)` in `NumClass` — standing for `(ch₀, ch₁·H, ch₂)` — the
**discriminant** is

```
Δ(v) = c² - 2·r·d.
```

`Basic.lean` proves that distinct numerical walls of a fixed `v` are disjoint
(`wall_eq_of_meet`), but only away from the point where `v`'s own charge
degenerates, and its module docstring records in prose that the excluded locus
is "a single point of each half plane when `Δ < 0`, and **empty** when
`Δ ≥ 0`", with Bogomolov–Gieseker putting the geometric classes in the second
case. This file makes that a theorem.

## What the discriminant buys, exactly

`discr_eq_neg_of_charge_eq_zero` is the quantitative statement: wherever the
charge of `v` vanishes at some `(s, t)` with `t ≠ 0`, the discriminant is
forced to the value `-(r²t²)`. Read contrapositively with `Δ(v) ≥ 0` that is
`charge_ne_zero_of_discr_nonneg`, which discharges the hypothesis
`wall_eq_of_meet` takes — so `wall_eq_of_meet_of_discr_nonneg` is the form
downstream lanes should cite: a class with nonnegative discriminant has
pairwise disjoint walls across the *whole* half plane, with no excluded point.

The sign asymmetry is the content. `Δ(v) ≥ 0` is what Bogomolov–Gieseker
supplies for a semistable class on a polarised surface, and it is exactly the
hypothesis that empties the degenerate locus.

## This file is geometry-free, and that is enforced

No sheaf, no variety, no polarisation, no Bogomolov–Gieseker inequality.
`NumClass` is a triple of reals and `discr` is a real-valued function of it;
nothing below assumes `0 ≤ discr v` for any particular `v`, it is always a
hypothesis. The bridge from a geometric class to a `NumClass`, and the proof
that `Δ ≥ 0` holds for semistable classes, live on the `AlgebraicGeometry`
side and are a separate lane.

`degV = (2, 0, 1)`, the counterexample class of `Basic.lean`, has
`discr_degV : Δ = -4`. That is what makes `wall_eq_of_meet_needs_charge`
compatible with `wall_eq_of_meet_of_discr_nonneg` rather than a refutation of
it: the counterexample lives strictly in the `Δ < 0` regime this file's
hypothesis excludes.

## Main results

* `NumClass.discr` — the discriminant, with `discr_eq` for rewriting.
* `discr_eq_neg_of_charge_eq_zero` — the quantitative form.
* `charge_ne_zero_of_discr_nonneg` — the hypothesis discharge.
* `wall_eq_of_meet_of_discr_nonneg` — disjointness with no excluded point.
* `discr_degV` — the counterexample class really is in the `Δ < 0` regime.
* `NumClass.scale` and `discr_scale` — the discriminant is a quadratic form.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

open NumClass

namespace NumClass

/-- **The Bogomolov discriminant** `Δ(v) = c² - 2·r·d` of a numerical class. -/
def discr (v : NumClass) : ℝ := v.deg ^ 2 - 2 * v.rk * v.ch2

/-- `discr` unfolded, for rewriting. -/
theorem discr_eq (v : NumClass) : v.discr = v.deg ^ 2 - 2 * v.rk * v.ch2 := rfl

/-- At rank zero the discriminant is the square of the degree. -/
theorem discr_of_rk_eq_zero {v : NumClass} (h : v.rk = 0) : v.discr = v.deg ^ 2 := by
  rw [discr_eq, h]; ring

/-- Componentwise scaling of a numerical class. Defined here rather than in
`Basic.lean` because the discriminant is its only consumer. -/
def scale (c : ℝ) (v : NumClass) : NumClass := (c * v.rk, c * v.deg, c * v.ch2)

@[simp]
theorem scale_rk (c : ℝ) (v : NumClass) : (scale c v).rk = c * v.rk := rfl

@[simp]
theorem scale_deg (c : ℝ) (v : NumClass) : (scale c v).deg = c * v.deg := rfl

@[simp]
theorem scale_ch2 (c : ℝ) (v : NumClass) : (scale c v).ch2 = c * v.ch2 := rfl

/-- **The discriminant is a quadratic form**: it scales by `c²`. -/
theorem discr_scale (c : ℝ) (v : NumClass) : (scale c v).discr = c ^ 2 * v.discr := by
  simp only [discr_eq, scale_rk, scale_deg, scale_ch2]; ring

end NumClass

/-! ### Where the charge degenerates, the discriminant is negative -/

/-- **The quantitative form.** If the charge of `v` vanishes at `(s, t)` with
`t ≠ 0`, then `Δ(v) = -(r²t²)`.

The proof goes through `charge_eq_zero_iff`, which solves the vanishing for the
two coordinates `deg` and `ch₂` in terms of `rk`; substituting both into the
discriminant leaves `-(r²t²)` after `ring`. -/
theorem discr_eq_neg_of_charge_eq_zero {s t : ℝ} (ht : t ≠ 0) {v : NumClass}
    (h : reZ s t v = 0 ∧ imZ s t v = 0) :
    v.discr = -(v.rk ^ 2 * t ^ 2) := by
  obtain ⟨hd, hc⟩ := (charge_eq_zero_iff ht v).mp h
  rw [NumClass.discr_eq, hd, hc]; ring

/-- **The hypothesis discharge.** A nonzero class with nonnegative discriminant
has nowhere-vanishing charge on the whole half plane.

`discr_eq_neg_of_charge_eq_zero` turns the assumed vanishing into
`0 ≤ -(r²t²)`, which with `t ≠ 0` forces `r = 0`; `charge_eq_zero_iff` then
collapses the other two coordinates as well, contradicting `v ≠ 0`. -/
theorem charge_ne_zero_of_discr_nonneg {s t : ℝ} (ht : t ≠ 0) {v : NumClass}
    (hv : v ≠ (0, 0, 0)) (hd : 0 ≤ v.discr) :
    ¬(reZ s t v = 0 ∧ imZ s t v = 0) := by
  intro h
  rw [discr_eq_neg_of_charge_eq_zero ht h] at hd
  have ht2 : 0 < t ^ 2 := lt_of_le_of_ne (sq_nonneg t) (Ne.symm (pow_ne_zero 2 ht))
  have hrk2 : v.rk ^ 2 ≤ 0 := by nlinarith [sq_nonneg v.rk]
  have hrk : v.rk = 0 := sq_eq_zero_iff.mp (le_antisymm hrk2 (sq_nonneg _))
  obtain ⟨hdg, hch⟩ := (charge_eq_zero_iff ht v).mp h
  refine hv ?_
  have hd0 : v.deg = 0 := by rw [hdg, hrk, mul_zero]
  have hc0 : v.ch2 = 0 := by rw [hch, hrk, mul_zero]
  exact Prod.ext hrk (Prod.ext hd0 hc0)

/-- **Disjointness of walls, with no excluded point.** This is
`wall_eq_of_meet` with its charge hypothesis replaced by the two inputs the
geometric theory actually supplies: the class is nonzero, and its
Bogomolov discriminant is nonnegative.

Downstream lanes should cite this rather than `wall_eq_of_meet`: it is the same
conclusion with a hypothesis a semistable class satisfies, instead of one about
a point of the half plane. -/
theorem wall_eq_of_meet_of_discr_nonneg {s t : ℝ} (ht : t ≠ 0) {v w₁ w₂ : NumClass}
    (hv : v ≠ (0, 0, 0)) (hdisc : 0 ≤ v.discr)
    (h₁ : wallExpr s t v w₁ = 0) (h₂ : wallExpr s t v w₂ = 0)
    (hn₁ : ¬(minA v w₁ = 0 ∧ minB v w₁ = 0 ∧ minC v w₁ = 0))
    (hn₂ : ¬(minA v w₂ = 0 ∧ minB v w₂ = 0 ∧ minC v w₂ = 0))
    {s' t' : ℝ} (ht' : t' ≠ 0) :
    wallExpr s' t' v w₁ = 0 ↔ wallExpr s' t' v w₂ = 0 :=
  wall_eq_of_meet ht (charge_ne_zero_of_discr_nonneg ht hv hdisc) h₁ h₂ hn₁ hn₂ ht'

/-! ### The counterexample class is in the negative regime

`Basic.lean` exhibits `degV = (2, 0, 1)` with two genuinely different walls
meeting at `(0, 1)`, which is what makes the charge hypothesis of
`wall_eq_of_meet` load-bearing. Its discriminant is `-4`, so it is excluded by
`wall_eq_of_meet_of_discr_nonneg` — the two statements are compatible, and this
is the check. -/

/-- The counterexample class of `Basic.lean` has discriminant `-4`. -/
theorem discr_degV : degV.discr = -4 := by
  norm_num [NumClass.discr_eq, degV, rk, deg, ch2]

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
