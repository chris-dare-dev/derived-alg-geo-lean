/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.BogomolovGieseker
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Numerical.Nested

/-!
# Transporting a polarised surface class to the `(s, t)` plane

`Walls/Numerical/Basic.lean` does all its wall geometry on `NumClass`, a triple
of reals, and says of it: "It is **not** `ch(E)` for a sheaf `E`." This file
supplies the map that makes it one, on the `AlgebraicGeometry` side where both
halves are visible, and spends Bogomolov–Gieseker to discharge the two
hypotheses that file declines to assume.

## The normalisation, derived rather than guessed

`Basic.lean`'s charge is

```
reZ s t v = -v.ch2 + s·v.deg - (s²/2)·v.rk + (t²/2)·v.rk,   imZ s t v = t·(v.deg - s·v.rk)
```

Matching term by term against the surface tilt charge

```
Z_{β,α}(E) = -∫ch₂^β + (α²/2)·∫H²·ch₀ + i·∫H·ch₁^β,        s = β,  t = α
```

forces

```
rk ↔ ∫H² · rank(E)        deg ↔ ∫c₁(E)·H        ch2 ↔ ∫ch₂(E)
```

**The rank slot is weighted by `∫H²`.** That is the content of this file and
the thing to get right.

## Why the naive reading is wrong

Taking `(rank E, ∫c₁·H, ∫ch₂)` does not satisfy the charge formula, and its
`NumClass.discr` is `(∫c₁·H)² − 2·rank·∫ch₂`, which is **neither** `∫Δ(E)` nor
anything Bogomolov–Gieseker bounds. Turning it into `∫Δ(E)` would need
`(∫c₁·H)² = ∫c₁²`, which is equality in Hodge index *together with* `∫H² = 1`.

So `discr_toNumClass` is stated against `Surface.discrH`, **not** against
`∫Δ(E)`. An earlier draft of this lane claimed the latter; it is false, and it
fails on this lane's own K3 witness — `4d²c²` against `2dc²`. Recorded here so
the mistake is not made a third time.

With the weighted reading the identity is exact: `discr` of the transported
class *is* `Surface.discrH`, and `Surface.discrH_nonneg` supplies its
nonnegativity for a semistable class.

## The bridge is one-way

This is the first module to import the `Walls` lane from `AlgebraicGeometry`,
and the direction is the permitted one. Nothing under `CategoryTheory/**` is
edited or added to; if a lemma were needed there it belongs in the wall lane,
not here, and `scripts/check_layering.py` holds the boundary.

Every declaration quantifies over `N`. Nothing here says a wall is a wall *for
an object*, that an object changes semistability across one, or anything about
mass or `Hom`.

## Main results

* `Surface.toNumClass` and its three component lemmas, plus `toNumClass_add`.
* `Surface.discr_toNumClass` — the identity the bridge turns on.
* `Surface.toNumClass_ne_zero_of_rank_ne_zero` — nonzero rank suffices.
* `Surface.charge_ne_zero_of_semistable` — the charge hypothesis, discharged.
* `Surface.wall_eq_of_meet_of_semistable` — walls disjoint, with no excluded
  point.
* `Surface.walls_nested_of_semistable` — walls nested, within a family.
* `Examples.toNumClass_k3` and `Examples.discr_toNumClass_k3` — the worked
  instance, with the `∫H² = 2d` factor visible on both sides.
-/

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition

universe u v

namespace AlgebraicGeometry.Numerical

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]

namespace Surface

variable (V : NumericalVarietyData 2 A N) (P : Polarization V.ring)

/-- **A polarised surface class as a point of the `(s, t)` wall plane.**

The rank slot carries `∫H²`; see the module docstring for the term-by-term
derivation, and for why the unweighted reading does not satisfy the charge
formula. -/
noncomputable def toNumClass (E : N) : Wall.NumClass :=
  (((V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) : ℚ) : ℝ),
    ((degH V P E : ℚ) : ℝ),
    ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ))

@[simp]
theorem toNumClass_rk (E : N) :
    (toNumClass V P E).rk = ((V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) : ℚ) : ℝ) := rfl

@[simp]
theorem toNumClass_deg (E : N) : (toNumClass V P E).deg = ((degH V P E : ℚ) : ℝ) := rfl

@[simp]
theorem toNumClass_ch2 (E : N) :
    (toNumClass V P E).ch2 = ((V.ring.degree (V.chComp E 2) : ℚ) : ℝ) := rfl

/-- The transport is additive, because rank, `degH` and `ch₂` all are. -/
theorem toNumClass_add (E F : N) :
    toNumClass V P (E + F)
      = ((toNumClass V P E).rk + (toNumClass V P F).rk,
          (toNumClass V P E).deg + (toNumClass V P F).deg,
          (toNumClass V P E).ch2 + (toNumClass V P F).ch2) := by
  have hch : V.chComp (E + F) 2 = V.chComp E 2 + V.chComp F 2 := V.chComp_add E F 2
  simp only [toNumClass, Wall.NumClass.rk, Wall.NumClass.deg, Wall.NumClass.ch2,
    degH_add, map_add, hch, Prod.mk.injEq]
  push_cast
  refine ⟨by ring, by ring, by ring⟩

/-- **The identity the bridge turns on.** The wall-plane discriminant of a
transported class is exactly the tilt discriminant `Surface.discrH`.

Both sides are `deg² − 2·rk·ch₂` once the transport is unfolded, so this is a
match of conventions rather than a computation — but it is a match that only
holds with the `∫H²` weight in the rank slot.

**Not** `∫Δ(E)`: see the module docstring. -/
theorem discr_toNumClass (E : N) :
    Wall.NumClass.discr (toNumClass V P E) = ((discrH V P E : ℚ) : ℝ) := by
  simp only [Wall.NumClass.discr_eq, toNumClass_rk, toNumClass_deg, toNumClass_ch2,
    discrH_eq]
  push_cast
  ring

/-- A class of nonzero rank transports to a nonzero triple: the rank slot is
`∫H² · rank E`, and `∫H² > 0` is the `Polarization`'s own field. -/
theorem toNumClass_ne_zero_of_rank_ne_zero {E : N} (hr : V.rank E ≠ 0) :
    toNumClass V P E ≠ (0, 0, 0) := by
  intro h
  have h1 : ((V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) : ℚ) : ℝ) = 0 :=
    congrArg (fun w => Wall.NumClass.rk w) h
  have hH : (0 : ℚ) < V.ring.degree (P.cls ^ 2) := P.degree_pow_pos
  have h2 : (V.ring.degree (P.cls ^ 2) * (V.rank E : ℚ) : ℚ) = 0 := by exact_mod_cast h1
  rcases mul_eq_zero.mp h2 with hc | hc
  · exact absurd hc (ne_of_gt hH)
  · exact hr (by exact_mod_cast hc)

/-! ### Spending Bogomolov–Gieseker on the wall structure -/

variable {V P}

/-- The transported discriminant of a semistable class is nonnegative — the
composite of `discr_toNumClass` with `Surface.discrH_nonneg`. -/
theorem discr_toNumClass_nonneg {E : N} (B : BogomolovGiesekerData V P)
    (hI : HodgeIndexStatement V P) (hE : B.Semistable E) :
    0 ≤ Wall.NumClass.discr (toNumClass V P E) := by
  rw [discr_toNumClass]
  exact_mod_cast discrH_nonneg B hI hE

/-- **The charge hypothesis of `wall_eq_of_meet`, discharged.**

`Basic.lean` states it as a hypothesis because, in its words, "`Δ ≥ 0` is a
theorem about sheaves and `NumClass` is a triple". Here the class comes from a
sheaf-level datum, so the theorem is available and the hypothesis is not needed.

The only `t`-dependence left is `t ≠ 0`, which is the half-plane condition. -/
theorem charge_ne_zero_of_semistable {E : N} (B : BogomolovGiesekerData V P)
    (hI : HodgeIndexStatement V P) (hE : B.Semistable E)
    (hne : toNumClass V P E ≠ (0, 0, 0)) {s t : ℝ} (ht : t ≠ 0) :
    ¬(Wall.reZ s t (toNumClass V P E) = 0 ∧ Wall.imZ s t (toNumClass V P E) = 0) :=
  Wall.charge_ne_zero_of_discr_nonneg ht hne (discr_toNumClass_nonneg B hI hE)

/-- **Distinct numerical walls of a semistable class of nonzero rank are
disjoint, with no excluded point.**

This is `wall_eq_of_meet` with its charge hypothesis supplied rather than
assumed. Nonzero rank is what makes the class a nonzero triple. -/
theorem wall_eq_of_meet_of_semistable {E : N} (B : BogomolovGiesekerData V P)
    (hI : HodgeIndexStatement V P) (hE : B.Semistable E) (hr : V.rank E ≠ 0)
    {s t : ℝ} (ht : t ≠ 0) {w₁ w₂ : Wall.NumClass}
    (h₁ : Wall.wallExpr s t (toNumClass V P E) w₁ = 0)
    (h₂ : Wall.wallExpr s t (toNumClass V P E) w₂ = 0)
    (hn₁ : ¬(Wall.minA (toNumClass V P E) w₁ = 0 ∧ Wall.minB (toNumClass V P E) w₁ = 0
      ∧ Wall.minC (toNumClass V P E) w₁ = 0))
    (hn₂ : ¬(Wall.minA (toNumClass V P E) w₂ = 0 ∧ Wall.minB (toNumClass V P E) w₂ = 0
      ∧ Wall.minC (toNumClass V P E) w₂ = 0))
    {s' t' : ℝ} (ht' : t' ≠ 0) :
    Wall.wallExpr s' t' (toNumClass V P E) w₁ = 0
      ↔ Wall.wallExpr s' t' (toNumClass V P E) w₂ = 0 :=
  Wall.wall_eq_of_meet_of_discr_nonneg ht (toNumClass_ne_zero_of_rank_ne_zero V P hr)
    (discr_toNumClass_nonneg B hI hE) h₁ h₂ hn₁ hn₂ ht'

/-- **Bertram nesting for a semistable geometric class.**

`walls_nested_of_discr_nonneg` with `0 ≤ discr` supplied by Bogomolov–Gieseker
instead of hypothesised. The same-family hypothesis is kept: it is load-bearing,
and the wall lane carries the counterexample that shows so. The `minA ≠ 0` and
`0 ≤ wallRadiusSq` hypotheses are kept too — nothing here discharges them. -/
theorem walls_nested_of_semistable {E : N} (B : BogomolovGiesekerData V P)
    (hI : HodgeIndexStatement V P) (hE : B.Semistable E)
    (hrk : (toNumClass V P E).rk ≠ 0) {w₁ w₂ : Wall.NumClass}
    (hA₁ : Wall.minA (toNumClass V P E) w₁ ≠ 0)
    (hA₂ : Wall.minA (toNumClass V P E) w₂ ≠ 0)
    (hR₁ : 0 ≤ Wall.wallRadiusSq (toNumClass V P E) w₁)
    (hR₂ : 0 ≤ Wall.wallRadiusSq (toNumClass V P E) w₂)
    (hfam : 0 < Wall.wallOffset (toNumClass V P E) w₁
      * Wall.wallOffset (toNumClass V P E) w₂) :
    (Wall.wallCentre (toNumClass V P E) w₁
          - Wall.wallCentre (toNumClass V P E) w₂) ^ 2
        ≤ Wall.wallRadiusSq (toNumClass V P E) w₁
          + Wall.wallRadiusSq (toNumClass V P E) w₂ ∧
      4 * Wall.wallRadiusSq (toNumClass V P E) w₁
          * Wall.wallRadiusSq (toNumClass V P E) w₂
        ≤ ((Wall.wallCentre (toNumClass V P E) w₁
              - Wall.wallCentre (toNumClass V P E) w₂) ^ 2
          - Wall.wallRadiusSq (toNumClass V P E) w₁
          - Wall.wallRadiusSq (toNumClass V P E) w₂) ^ 2 :=
  Wall.walls_nested_of_discr_nonneg hrk (discr_toNumClass_nonneg B hI hE)
    hA₁ hA₂ hR₁ hR₂ hfam

end Surface

/-! ### The worked instance -/

namespace Examples

open AlgebraicGeometry.Numerical.Examples

/-- The transport on the rank-one K3 model, evaluated. Every slot carries the
polarisation degree `∫H² = 2d`: the rank slot by the weighting, the degree slot
through `degH`, and `ch₂` through `∫H²` in `surfaceDegree`. -/
theorem toNumClass_k3 (d : ℕ) (hd : d ≠ 0) (E : SurfaceNum) :
    Surface.toNumClass (k3NumericalVariety d) (k3Polarization d hd) E
      = ((2 * (d : ℝ) * (E 0 : ℝ)), (2 * (d : ℝ) * (E 1 : ℝ)),
          ((E 2 : ℝ) * (2 * (d : ℝ)))) := by
  have hHsq : (k3NumericalVariety d).ring.degree ((k3Polarization d hd).cls ^ 2)
      = 2 * (d : ℚ) := surfaceDegree_Hsq _
  have hch2 : (k3NumericalVariety d).ring.degree ((k3NumericalVariety d).chComp E 2)
      = (E 2 : ℚ) * (2 * (d : ℚ)) := by
    show (surfaceNumericalRing (2 * (d : ℚ))).degree
      (algebraMap ℚ SurfaceRing (k3ChCoeff E 2) * H ^ 2) = _
    rw [NumericalRingData.degree_algebraMap_mul, surfaceDegree_Hsq]
    rfl
  have hrank : ((k3NumericalVariety d).rank E : ℚ) = (E 0 : ℚ) := rfl
  simp only [Surface.toNumClass, hHsq, hch2, hrank, degH_k3 d hd E, Prod.mk.injEq]
  push_cast
  refine ⟨by ring, by ring, by ring⟩

/-- Both sides of `discr_toNumClass` on the K3 model, as one explicit rational:
`Δ = 4d²·(E 1)² − 8d²·(E 0)·(E 2)`.

The `∫H² = 2d` factor is present twice on the rank–`ch₂` term and squared on the
degree term, which is exactly the weighting the naive transport would lose. -/
theorem discr_toNumClass_k3 (d : ℕ) (hd : d ≠ 0) (E : SurfaceNum) :
    Wall.NumClass.discr
        (Surface.toNumClass (k3NumericalVariety d) (k3Polarization d hd) E)
      = 4 * (d : ℝ) ^ 2 * (E 1 : ℝ) ^ 2 - 8 * (d : ℝ) ^ 2 * (E 0 : ℝ) * (E 2 : ℝ) := by
  rw [Wall.NumClass.discr_eq, toNumClass_k3 d hd E]
  show (2 * (d : ℝ) * (E 1 : ℝ)) ^ 2
    - 2 * (2 * (d : ℝ) * (E 0 : ℝ)) * ((E 2 : ℝ) * (2 * (d : ℝ))) = _
  ring

end Examples

end AlgebraicGeometry.Numerical
