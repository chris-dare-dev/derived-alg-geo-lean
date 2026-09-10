/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Spherical.Basic
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PeriodDomain

/-!
# The two wall notions, compared

The library carries two developments of spherical walls over the same
exponential chart, and until now nothing related them.

* `Walls/Spherical/Basic.lean` works in the `(β, ω)` chart and defines
  `wall q δ`, Bridgeland's `H(δ)`: the locus where `(℧, δ)` is **real and
  non-positive**.  Its finiteness lives in `Spherical/Finiteness.lean`.
* `QuadraticForm/PeriodDomain.lean` works with planes and defines
  `PeriodDomain.wall Q δ`: the positive planes **orthogonal** to `δ`.  Its
  finiteness lives in `QuadraticForm/WallFiniteness.lean` and
  `QuadraticForm/WallRegion.lean`.

`Spherical/Basic.lean` now spells the chart with `Mukai.expRe` and
`Mukai.expIm` rather than redeclaring it, so the two are chart-for-chart the
same and the comparison below is about the loci alone.

## The two are not equal, and the difference is the content

`chartPlane` is the plane the period-domain layer sees.  Orthogonality to it is
the vanishing of **both** pairings, whereas `wall` asks the imaginary one to
vanish and the real one to be non-positive.  So

```text
chartPlane β ω ∈ PeriodDomain.wall δ  ↔  (β, ω) ∈ wall q δ ∧ Re(℧, δ) = 0,
```

which is `mem_periodDomainWall_iff_mem_wall`.  The period-domain wall is the
sub-locus of the spherical half-wall where the charge vanishes rather than
merely turning real, and the inclusion goes one way only.

That asymmetry is the honest content of this file.  It is also why the two
finiteness theorems are not restatements of each other: the spherical one counts
classes that *destabilize* somewhere on a region, the period-domain one counts
classes of *vanishing* charge at a point.

## What is not claimed

No stability condition, heart, or semistable object appears.  Both `wall`
notions are subsets of linear-algebraic data, and nothing here says either one
is the locus where a moduli problem changes.
-/

open QuadraticMap

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- The plane spanned by the real and imaginary parts of `exp(β + iω)`: the
`(β, ω)` chart as the period-domain layer sees it. -/
def chartPlane (β ω : V) : Submodule ℝ (Mukai.RealExtension V) :=
  PeriodDomain.pairSpan (chartRe q β ω) (chartIm q β ω)

theorem chartPlane_eq_span (β ω : V) :
    chartPlane q β ω =
      Submodule.span ℝ ({chartRe q β ω, chartIm q β ω} : Set (Mukai.RealExtension V)) := rfl

/-- The chart plane is positive as soon as `ω² > 0`; the `β`-field is
unconstrained.  This is `Mukai.isPositivePair_exp` said in the chart. -/
theorem isPositivePlane_chartPlane (hq : ∀ x y : V, q x y = q y x) {omega : V}
    (homega : 0 < q omega omega) (beta : V) :
    PeriodDomain.IsPositivePlane (Mukai.realForm q) (chartPlane q beta omega) :=
  Mukai.isPositivePair_exp q beta omega hq homega

/-- **Orthogonality to the chart plane is the vanishing of both pairings.** -/
theorem mem_periodDomainWall_iff (hq : ∀ x y : V, q x y = q y x) {beta omega : V}
    (homega : 0 < q omega omega) (δ : Mukai.RealExtension V) :
    chartPlane q beta omega ∈ PeriodDomain.wall (Mukai.realForm q) δ ↔
      pairingRe q beta omega δ = 0 ∧ pairingIm q beta omega δ = 0 := by
  rw [PeriodDomain.mem_wall_iff_mem_orthogonal
      (isPositivePlane_chartPlane q hq homega beta),
    chartPlane_eq_span, PeriodDomain.mem_orthogonal_span_pair_iff,
    Mukai.polar_realForm q hq, Mukai.polar_realForm q hq]
  rfl

/-- **The period-domain wall is the sub-locus of the spherical wall where the
real pairing also vanishes.**

`wall q δ` asks `Im(℧, δ) = 0` and `Re(℧, δ) ≤ 0`; the period-domain wall asks
both to vanish.  So one is contained in the other, and the containment is
strict wherever the real pairing is negative. -/
theorem mem_periodDomainWall_iff_mem_wall (hq : ∀ x y : V, q x y = q y x)
    {beta omega : V} (homega : 0 < q omega omega) (δ : Mukai.RealExtension V) :
    chartPlane q beta omega ∈ PeriodDomain.wall (Mukai.realForm q) δ ↔
      (beta, omega) ∈ wall q δ ∧ pairingRe q beta omega δ = 0 := by
  rw [mem_periodDomainWall_iff q hq homega, mem_wall_iff]
  constructor
  · rintro ⟨hre, him⟩
    exact ⟨⟨him, le_of_eq hre⟩, hre⟩
  · rintro ⟨⟨him, -⟩, hre⟩
    exact ⟨hre, him⟩

/-- **A point of the period-domain wall is a point of the spherical wall.**  The
converse fails: a class can be real and strictly negative against `℧` without
having vanishing charge. -/
theorem mem_wall_of_mem_periodDomainWall (hq : ∀ x y : V, q x y = q y x)
    {beta omega : V} (homega : 0 < q omega omega) {δ : Mukai.RealExtension V}
    (h : chartPlane q beta omega ∈ PeriodDomain.wall (Mukai.realForm q) δ) :
    (beta, omega) ∈ wall q δ :=
  ((mem_periodDomainWall_iff_mem_wall q hq homega δ).mp h).1

/-- The chamber of a set of classes contains every point whose plane avoids all
their period-domain walls only when the real pairing is controlled; stated the
other way round, a point of the chamber has no class of vanishing charge. -/
theorem not_mem_periodDomainWall_of_mem_chamber (hq : ∀ x y : V, q x y = q y x)
    {beta omega : V} (homega : 0 < q omega omega) {T : Set (Mukai.RealExtension V)}
    (h : (beta, omega) ∈ chamber q T) {δ : Mukai.RealExtension V} (hδ : δ ∈ T) :
    chartPlane q beta omega ∉ PeriodDomain.wall (Mukai.realForm q) δ :=
  fun hw => h δ hδ (mem_wall_of_mem_periodDomainWall q hq homega hw)

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical
