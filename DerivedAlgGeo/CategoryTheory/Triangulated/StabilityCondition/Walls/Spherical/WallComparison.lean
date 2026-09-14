/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Spherical.Basic
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.OrthogonalityLocus
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PositiveFrame

/-!
# Positive frames, positive planes, and the two numerical loci

The library carries two different loci over the same exponential chart.

* `Walls/Spherical/Basic.lean` works in the `(β, ω)` chart and defines
  `nonpositiveRayLocus q δ`, Bridgeland's `H(δ)`: the locus where `(℧, δ)` is **real and
  non-positive**.  Its finiteness lives in `Spherical/Finiteness.lean`.
* `QuadraticForm/PositivePlane.lean` works with planes and defines
  `PeriodDomain.orthogonalityLocus Q δ`: the positive planes **orthogonal** to `δ`.  Its
  finiteness lives in `QuadraticForm/OrthogonalityFiniteness.lean` and
  `QuadraticForm/OrthogonalityRegion.lean`.

`Spherical/Basic.lean` now spells the chart with `Mukai.expRe` and
`Mukai.expIm` rather than redeclaring it, so the two are chart-for-chart the
same and the comparison below is about the loci alone.

## The two are not equal, and the difference is the content

`chartFrame` retains the ordered real and imaginary vectors. `chartPlane` is
obtained from it by the neutral `framePlane` forgetful map. Orthogonality is
the vanishing of **both** pairings, whereas `nonpositiveRayLocus` asks the imaginary one to
vanish and the real one to be non-positive.  So

```text
chartPlane β ω ∈ PeriodDomain.orthogonalityLocus δ  ↔  (β, ω) ∈ nonpositiveRayLocus q δ ∧ Re(℧, δ) = 0,
```

which is `mem_orthogonalityLocus_iff_mem_nonpositiveRayLocus`. The orthogonality locus is the
sub-locus of the spherical nonpositive-ray locus where the charge vanishes rather than
merely turning real, and the inclusion goes one way only.

That asymmetry is the honest content of this file.  It is also why the two
finiteness theorems are not restatements of each other: the spherical one counts
classes whose signed-ray locus meets a region, while the positive-plane one
counts classes of vanishing charge at a point.

## What is not claimed

No stability condition, heart, or semistable object appears. Nothing here says
either locus is where a moduli problem changes.
-/

open QuadraticMap

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable (q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)

/-- The ordered frame of real and imaginary parts of `exp(β + iω)`. -/
def chartFrame (β ω : V) : Mukai.RealExtension V × Mukai.RealExtension V :=
  (chartRe q β ω, chartIm q β ω)

/-- The plane obtained by forgetting the ordered basis of `chartFrame`. -/
def chartPlane (β ω : V) : Submodule ℝ (Mukai.RealExtension V) :=
  PeriodDomain.framePlane (chartFrame q β ω)

theorem chartPlane_eq_framePlane (β ω : V) :
    chartPlane q β ω = PeriodDomain.framePlane (chartFrame q β ω) := rfl

theorem chartPlane_eq_span (β ω : V) :
    chartPlane q β ω =
      Submodule.span ℝ ({chartRe q β ω, chartIm q β ω} : Set (Mukai.RealExtension V)) := rfl

/-- The chart retains a positive ordered frame before its basis is forgotten. -/
theorem isPositiveFrame_chartFrame (hq : ∀ x y : V, q x y = q y x) {omega : V}
    (homega : 0 < q omega omega) (beta : V) :
    PeriodDomain.IsPositiveFrame (Mukai.realForm q)
      (chartFrame q beta omega).1 (chartFrame q beta omega).2 :=
  Mukai.isPositiveFrame_exp q beta omega hq homega

/-- The chart plane is positive as soon as `ω² > 0`; the `β`-field is
unconstrained.  This is `Mukai.isPositiveFrame_exp` said in the chart. -/
theorem isPositivePlane_chartPlane (hq : ∀ x y : V, q x y = q y x) {omega : V}
    (homega : 0 < q omega omega) (beta : V) :
    PeriodDomain.IsPositivePlane (Mukai.realForm q) (chartPlane q beta omega) := by
  exact PeriodDomain.isPositivePlane_framePlane
    (isPositiveFrame_chartFrame q hq homega beta)

/-- **Orthogonality to the chart plane is the vanishing of both pairings.** -/
theorem mem_chartPlane_orthogonalityLocus_iff (hq : ∀ x y : V, q x y = q y x) {beta omega : V}
    (homega : 0 < q omega omega) (δ : Mukai.RealExtension V) :
    chartPlane q beta omega ∈ PeriodDomain.orthogonalityLocus (Mukai.realForm q) δ ↔
      pairingRe q beta omega δ = 0 ∧ pairingIm q beta omega δ = 0 := by
  rw [PeriodDomain.mem_orthogonalityLocus_iff_mem_orthogonal
      (isPositivePlane_chartPlane q hq homega beta),
    chartPlane_eq_span, PeriodDomain.mem_orthogonal_span_pair_iff,
    Mukai.polar_realForm q hq, Mukai.polar_realForm q hq]
  rfl

/-- **The orthogonality locus is the sub-locus of the spherical nonpositiveRayLocus where the
real pairing also vanishes.**

`nonpositiveRayLocus q δ` asks `Im(℧, δ) = 0` and `Re(℧, δ) ≤ 0`; the orthogonality locus asks
both to vanish.  So one is contained in the other, and the containment is
strict wherever the real pairing is negative. -/
theorem mem_orthogonalityLocus_iff_mem_nonpositiveRayLocus (hq : ∀ x y : V, q x y = q y x)
    {beta omega : V} (homega : 0 < q omega omega) (δ : Mukai.RealExtension V) :
    chartPlane q beta omega ∈ PeriodDomain.orthogonalityLocus (Mukai.realForm q) δ ↔
      (beta, omega) ∈ nonpositiveRayLocus q δ ∧ pairingRe q beta omega δ = 0 := by
  rw [mem_chartPlane_orthogonalityLocus_iff q hq homega,
    mem_nonpositiveRayLocus_iff]
  constructor
  · rintro ⟨hre, him⟩
    exact ⟨⟨him, le_of_eq hre⟩, hre⟩
  · rintro ⟨⟨him, -⟩, hre⟩
    exact ⟨hre, him⟩

/-- **A point of the orthogonality locus is a point of the spherical nonpositiveRayLocus.**  The
converse fails: a class can be real and strictly negative against `℧` without
having vanishing charge. -/
theorem mem_nonpositiveRayLocus_of_mem_orthogonalityLocus (hq : ∀ x y : V, q x y = q y x)
    {beta omega : V} (homega : 0 < q omega omega) {δ : Mukai.RealExtension V}
    (h : chartPlane q beta omega ∈ PeriodDomain.orthogonalityLocus (Mukai.realForm q) δ) :
    (beta, omega) ∈ nonpositiveRayLocus q δ :=
  ((mem_orthogonalityLocus_iff_mem_nonpositiveRayLocus q hq homega δ).mp h).1

/-- A point avoiding every signed-ray locus also avoids every orthogonality
locus indexed by the same classes. -/
theorem not_mem_orthogonalityLocus_of_mem_signedRayRegularLocus (hq : ∀ x y : V, q x y = q y x)
    {beta omega : V} (homega : 0 < q omega omega) {T : Set (Mukai.RealExtension V)}
    (h : (beta, omega) ∈ signedRayRegularLocus q T) {δ : Mukai.RealExtension V} (hδ : δ ∈ T) :
    chartPlane q beta omega ∉ PeriodDomain.orthogonalityLocus (Mukai.realForm q) δ :=
  fun hw => h δ hδ (mem_nonpositiveRayLocus_of_mem_orthogonalityLocus q hq homega hw)

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Spherical
