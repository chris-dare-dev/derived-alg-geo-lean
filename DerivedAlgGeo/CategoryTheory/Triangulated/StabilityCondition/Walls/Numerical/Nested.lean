/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical.Discriminant

/-!
# Nesting of the numerical walls of a fixed class

`Basic.lean` proves that distinct walls of a fixed `v` are **disjoint**
(`wall_eq_of_meet`) and says at that declaration, in these words, that
"disjointness is not yet nesting": disjoint circles centred on a common axis can
equally well sit side by side. `Discriminant.lean` then supplied the input that
removes the excluded point. This file spends the same input on the ordering
claim.

## The coordinates, and the one identity everything runs on

For a wall of `v` with `rk v ≠ 0` and `minA v w ≠ 0`, `wall_circle_eq` gives a
circle; name its centre and radius squared `wallCentre` and `wallRadiusSq`, and
name

```
wallOffset v w = minB v w / minA v w + deg v / rk v
```

Then `wallRadiusSq_eq_offset` says, writing `k = Δ(v) / rk(v)²`,

```
wallRadiusSq = wallOffset² - k,     wallCentre = deg v / rk v - wallOffset.
```

This is the **coaxial-pencil normal form**: every wall of `v` is `a² - k` for
its own offset `a`, with `k` a constant of the class. `minor_orth` is what
supplies it — the three minors of a fixed `v` satisfy one linear relation, and
dividing it by `minA` is exactly the substitution the normal form needs.

The rest is `nesting_identity`,

```
(a₁a₂ - k)² - (a₁² - k)(a₂² - k) = k(a₁ - a₂)²,
```

one `ring` call, and the observation that `Δ(v) ≥ 0` makes `k ≥ 0`, so the
right-hand side is nonnegative and the two radii can never "cross".

## Two families, and why the split is real rather than an artefact

The walls of `v` do **not** all nest in one another. The vertical wall
`s = deg v / rk v` — the `minA = 0` case of `wall_line_eq` — separates them into
two families, and nesting holds *within* a family. That is Maciocia's form of
the theorem, and it is not a weakening of it.

`walls_not_nested_of_opposite_offset` exhibits the failure explicitly, in the
idiom `Basic.lean` uses for `wall_eq_of_meet_needs_charge`: `v = (1, 0, -1)` has
`Δ = 2 ≥ 0`, and the two walls `w₁ = (0, 1, -2)`, `w₂ = (0, 1, 2)` have equal
radii `2` and centres `∓2`, so they are disjoint and **side by side**, not
nested. Their offsets are `2` and `-2`. So the same-family hypothesis
`0 < wallOffset v w₁ * wallOffset v w₂` is load-bearing, and dropping it makes
the theorem false rather than merely unprovable.

## Square roots do not appear

Both conclusions are stated without `Real.sqrt`. "One circle lies inside the
other" is `|c₁ - c₂| ≤ |r₁ - r₂|`; squaring twice turns that into the two
polynomial inequalities below, which is what `nlinarith` can actually close and
what a downstream consumer can actually use.

## Still no geometry

Arithmetic on triples of reals. No sheaf, no surface, no polarisation. `Δ(v) ≥ 0`
is a hypothesis, as it is in `Discriminant.lean`; nothing here proves
Bogomolov–Gieseker or assumes it.

## Main results

* `wallCentre`, `wallRadiusSq`, `wallOffset` — the coaxial coordinates.
* `wallRadiusSq_eq_offset` and `wallCentre_eq_sub_offset` — the normal form.
* `nesting_identity` — the `ring` identity the ordering rests on.
* `nested_of_offsets` — the real-arithmetic core, stated without walls.
* `walls_nested_of_discr_nonneg` — the theorem.
* `walls_not_nested_of_opposite_offset` — the same-family hypothesis is
  load-bearing.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall

open NumClass

/-! ### The coaxial coordinates -/

/-- The centre of the wall of `v` through `w`, as a point `(wallCentre, 0)` of
the `s`-axis. Junk unless `minA v w ≠ 0`; see `wall_circle_eq`. -/
noncomputable def wallCentre (v w : NumClass) : ℝ := -(minB v w) / minA v w

/-- The squared radius of the wall of `v` through `w`. Junk unless
`minA v w ≠ 0`, and **not** assumed nonnegative: the `minA ≠ 0` case of
`Basic.lean` splits on exactly that sign. -/
noncomputable def wallRadiusSq (v w : NumClass) : ℝ :=
  (minB v w ^ 2 - 2 * minA v w * minC v w) / minA v w ^ 2

/-- The position of the wall of `v` through `w` in the coaxial pencil. This is
the only coordinate the nesting argument uses. -/
noncomputable def wallOffset (v w : NumClass) : ℝ := minB v w / minA v w + v.deg / v.rk

@[simp]
theorem wallCentre_eq (v w : NumClass) : wallCentre v w = -(minB v w) / minA v w := rfl

@[simp]
theorem wallRadiusSq_eq (v w : NumClass) :
    wallRadiusSq v w = (minB v w ^ 2 - 2 * minA v w * minC v w) / minA v w ^ 2 := rfl

@[simp]
theorem wallOffset_eq (v w : NumClass) :
    wallOffset v w = minB v w / minA v w + v.deg / v.rk := rfl

/-! ### The normal form -/

/-- **The centre in terms of the offset.** Immediate from the definitions; it is
what makes two centres differ by `a₂ - a₁`. -/
theorem wallCentre_eq_sub_offset (v w : NumClass) :
    wallCentre v w = v.deg / v.rk - wallOffset v w := by
  simp only [wallCentre_eq, wallOffset_eq, neg_div]
  ring

/-- **The coaxial normal form.** Every wall of `v` has squared radius
`a² - Δ(v)/rk(v)²` for its own offset `a`.

This is the only place `minor_orth` is used, and it is where it is spent:
`ch₂·minA + deg·minB + rk·minC = 0` solves for `minC`, and substituting that
into `wallRadiusSq` collapses it to the displayed form. -/
theorem wallRadiusSq_eq_offset {v w : NumClass} (hrk : v.rk ≠ 0) (hA : minA v w ≠ 0) :
    wallRadiusSq v w = wallOffset v w ^ 2 - v.discr / v.rk ^ 2 := by
  have h := minor_orth v w
  have hC : minC v w = -(v.ch2 * minA v w + v.deg * minB v w) / v.rk := by
    field_simp
    linarith [h]
  simp only [wallRadiusSq_eq, wallOffset_eq, NumClass.discr_eq, hC]
  field_simp
  ring

/-! ### The arithmetic core -/

/-- **The identity the ordering rests on.** One `ring` call, and everything else
in this file is bookkeeping around it. -/
theorem nesting_identity (a₁ a₂ k : ℝ) :
    (a₁ * a₂ - k) ^ 2 - (a₁ ^ 2 - k) * (a₂ ^ 2 - k) = k * (a₁ - a₂) ^ 2 := by ring

/-- **Nesting, as a statement about reals.** Two members of a coaxial pencil
with constant `k ≥ 0`, both with nonnegative squared radius and offsets of the
same sign, satisfy the two square-root-free nesting inequalities.

The hypothesis `0 < a₁ * a₂` is the same-family condition; without it the
conclusion is false, as `walls_not_nested_of_opposite_offset` shows. -/
theorem nested_of_offsets {a₁ a₂ k : ℝ} (hk0 : 0 ≤ k)
    (h₁ : k ≤ a₁ ^ 2) (h₂ : k ≤ a₂ ^ 2) (hfam : 0 < a₁ * a₂) :
    (a₂ - a₁) ^ 2 ≤ (a₁ ^ 2 - k) + (a₂ ^ 2 - k) ∧
      4 * (a₁ ^ 2 - k) * (a₂ ^ 2 - k) ≤
        ((a₂ - a₁) ^ 2 - (a₁ ^ 2 - k) - (a₂ ^ 2 - k)) ^ 2 := by
  have hprod : k * k ≤ a₁ ^ 2 * a₂ ^ 2 := mul_le_mul h₁ h₂ hk0 (hk0.trans h₁)
  have hU : 0 ≤ a₁ * a₂ - k := by nlinarith [hprod, hfam, hk0]
  refine ⟨by nlinarith [hU], ?_⟩
  nlinarith [nesting_identity a₁ a₂ k, mul_nonneg hk0 (sq_nonneg (a₁ - a₂))]

/-! ### The theorem -/

/-- **Bertram's nested wall theorem, ordering half.** Two walls of a class of
nonnegative Bogomolov discriminant, lying on the same side of the vertical wall,
are nested: the distance between their centres is at most the difference of
their radii.

Both conclusions are the square-root-free form. The first says the circles are
not separated; the second, together with the first, says one contains the other
rather than the two crossing.

`Basic.lean`'s `wall_eq_of_meet` supplies disjointness and explicitly declines
this claim for want of the discriminant input. `Discriminant.lean` supplies the
input; this is what it buys. -/
theorem walls_nested_of_discr_nonneg {v w₁ w₂ : NumClass}
    (hrk : v.rk ≠ 0) (hdisc : 0 ≤ v.discr)
    (hA₁ : minA v w₁ ≠ 0) (hA₂ : minA v w₂ ≠ 0)
    (hR₁ : 0 ≤ wallRadiusSq v w₁) (hR₂ : 0 ≤ wallRadiusSq v w₂)
    (hfam : 0 < wallOffset v w₁ * wallOffset v w₂) :
    (wallCentre v w₁ - wallCentre v w₂) ^ 2 ≤ wallRadiusSq v w₁ + wallRadiusSq v w₂ ∧
      4 * wallRadiusSq v w₁ * wallRadiusSq v w₂ ≤
        ((wallCentre v w₁ - wallCentre v w₂) ^ 2
          - wallRadiusSq v w₁ - wallRadiusSq v w₂) ^ 2 := by
  have e₁ := wallRadiusSq_eq_offset hrk hA₁
  have e₂ := wallRadiusSq_eq_offset hrk hA₂
  have hk0 : 0 ≤ v.discr / v.rk ^ 2 := div_nonneg hdisc (sq_nonneg _)
  have hc : wallCentre v w₁ - wallCentre v w₂ = wallOffset v w₂ - wallOffset v w₁ := by
    rw [wallCentre_eq_sub_offset v w₁, wallCentre_eq_sub_offset v w₂]; ring
  have h₁ : v.discr / v.rk ^ 2 ≤ wallOffset v w₁ ^ 2 := by rw [e₁] at hR₁; linarith
  have h₂ : v.discr / v.rk ^ 2 ≤ wallOffset v w₂ ^ 2 := by rw [e₂] at hR₂; linarith
  obtain ⟨n₁, n₂⟩ := nested_of_offsets hk0 h₁ h₂ hfam
  rw [hc, e₁, e₂]
  exact ⟨n₁, n₂⟩

/-! ### The same-family hypothesis is load-bearing

Not a technical convenience. The witnesses below have nonnegative discriminant
and both radii positive, and they are still not nested — they are side by side
across the vertical wall. -/

/-- **Dropping the same-family hypothesis makes `walls_nested_of_discr_nonneg`
false.** `v = (1, 0, -1)` has `Δ = 2`; the two walls `(0, 1, -2)` and
`(0, 1, 2)` have radii squared `2` and centres `∓2`, so the squared distance
between the centres is `16` while the radii sum to `4`. -/
theorem walls_not_nested_of_opposite_offset :
    ∃ v w₁ w₂ : NumClass,
      v.rk ≠ 0 ∧ 0 ≤ v.discr ∧ minA v w₁ ≠ 0 ∧ minA v w₂ ≠ 0 ∧
      0 ≤ wallRadiusSq v w₁ ∧ 0 ≤ wallRadiusSq v w₂ ∧
      wallOffset v w₁ * wallOffset v w₂ < 0 ∧
      ¬((wallCentre v w₁ - wallCentre v w₂) ^ 2
        ≤ wallRadiusSq v w₁ + wallRadiusSq v w₂) := by
  refine ⟨(1, 0, -1), (0, 1, -2), (0, 1, 2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [wallCentre_eq, wallRadiusSq_eq, wallOffset_eq, NumClass.discr_eq,
      minA, minB, minC, rk, deg, ch2]

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall
