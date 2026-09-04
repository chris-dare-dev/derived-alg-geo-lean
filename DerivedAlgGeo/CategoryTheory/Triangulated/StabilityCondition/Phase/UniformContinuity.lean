/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.NormalizedShift
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.UniformSpace.Compact

/-!
# Uniform continuity of normalized phase shifts

`Slicing.IsLocallyFinite`
(`WeakStabilityCondition/StabilityCondition/Foundation/StabilityCondition.lean`) quantifies **one**
radius `η` over
**all** centres `t`: every window `(t - η, t + η)` must have finite-length
objects. A normalized shift distorts windows, so transporting local finiteness
across the action needs a *uniform* bound on that distortion, not a pointwise
one.

Uniform continuity is not automatic for a continuous bijection of `ℝ`. It
holds here because of `map_add_one`: `f` commutes with `x ↦ x + 1`, so its
behaviour on all of `ℝ` is determined by a compact window, and the modulus
obtained there transfers everywhere by integer translation. `map_add_int` is
that transfer, and `uniformContinuous` is the argument.

`exists_radius` packages the uniform window estimate needed to transport
local finiteness.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

namespace NormalizedShift

/-! ## Integer translation -/

theorem map_add_nat (f : NormalizedShift) : ∀ (n : ℕ) (x : ℝ),
    f.toOrderIso (x + n) = f.toOrderIso x + n := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    have hx : x + ((k : ℕ) + 1 : ℝ) = (x + k) + 1 := by ring
    push_cast
    rw [hx, f.map_add_one, ih x]
    ring

theorem map_sub_nat (f : NormalizedShift) (m : ℕ) (x : ℝ) :
    f.toOrderIso (x - m) = f.toOrderIso x - m := by
  have h := map_add_nat f m (x - m)
  simp only [sub_add_cancel] at h
  linarith

/-- `f` commutes with translation by any integer, not just by `1`. -/
theorem map_add_int (f : NormalizedShift) (n : ℤ) (x : ℝ) :
    f.toOrderIso (x + n) = f.toOrderIso x + n := by
  obtain ⟨m, hm | hm⟩ := n.eq_nat_or_neg <;> subst hm
  · exact_mod_cast map_add_nat f m x
  · have := map_sub_nat f m x
    push_cast
    rw [show x + -(m : ℝ) = x - m by ring, this]
    ring

/-! ## Uniform continuity -/

/-- A normalized shift is **uniformly** continuous.

Continuity alone is free (`OrderIso.continuous`); uniformity is not, and a
general continuous bijection of `ℝ` does not have it. The `+1`-equivariance is
what buys it: fix a modulus on the compact window `[-1, 2]`, then move any
pair of nearby points into that window by an integer translation, which
`map_add_int` says `f` respects exactly. -/
theorem uniformContinuous (f : NormalizedShift) :
    UniformContinuous f.toOrderIso := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hcont : ContinuousOn f.toOrderIso (Set.Icc (-1 : ℝ) 2) :=
    (OrderIso.continuous f.toOrderIso).continuousOn
  have huc := (isCompact_Icc (a := (-1 : ℝ)) (b := 2)).uniformContinuousOn_of_continuous hcont
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδ'⟩ := huc ε hε
  refine ⟨min δ 1, lt_min hδ one_pos, ?_⟩
  intro x y hxy
  have hxy1 : |x - y| < 1 := lt_of_lt_of_le (by rwa [Real.dist_eq] at hxy) (min_le_right _ _)
  have hxyd : |x - y| < δ := lt_of_lt_of_le (by rwa [Real.dist_eq] at hxy) (min_le_left _ _)
  set n : ℤ := ⌊y⌋ with hn
  have hy0 : (0 : ℝ) ≤ y - n := by have := Int.floor_le y; linarith
  have hy1 : y - n < 1 := by have := Int.lt_floor_add_one y; linarith
  have hx1 : -1 ≤ x - n := by cases abs_lt.mp hxy1 with | intro h1 h2 => linarith
  have hx2 : x - (n : ℝ) ≤ 2 := by cases abs_lt.mp hxy1 with | intro h1 h2 => linarith
  have hmemy : y - (n : ℝ) ∈ Set.Icc (-1 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hmemx : x - (n : ℝ) ∈ Set.Icc (-1 : ℝ) 2 := ⟨hx1, hx2⟩
  have hd : dist (x - (n : ℝ)) (y - (n : ℝ)) < δ := by
    rw [Real.dist_eq]; simpa using hxyd
  have hkey := hδ' (x - (n : ℝ)) hmemx (y - (n : ℝ)) hmemy hd
  have ex : f.toOrderIso (x - (n : ℝ)) = f.toOrderIso x - n := by
    have := map_add_int f (-n) x
    push_cast at this ⊢
    rw [show x + -(n : ℝ) = x - n by ring] at this
    rw [this]; ring
  have ey : f.toOrderIso (y - (n : ℝ)) = f.toOrderIso y - n := by
    have := map_add_int f (-n) y
    push_cast at this ⊢
    rw [show y + -(n : ℝ) = y - n by ring] at this
    rw [this]; ring
  rw [ex, ey, Real.dist_eq] at hkey
  rw [Real.dist_eq]
  simpa using hkey

/-- Windows can be shrunk uniformly: given a target width `w` and a ceiling
`M`, there is a radius `η < M` such that `f`
carries *every* window `(t - η, t + η)` into an interval of width `< w`.

The quantifier order is the whole point — one `η` for all centres `t`. That is
what `IsLocallyFinite` demands and what pointwise continuity would not give. -/
theorem exists_radius (f : NormalizedShift) {w M : ℝ} (hw : 0 < w) (hM : 0 < M) :
    ∃ η : ℝ, 0 < η ∧ η < M ∧ ∀ t : ℝ,
      f.toOrderIso (t + η) - f.toOrderIso (t - η) < w := by
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuous_iff.mp f.uniformContinuous w hw
  have hη0 : 0 < min (δ / 3) (M / 2) := lt_min (by linarith) (by linarith)
  refine ⟨min (δ / 3) (M / 2), hη0, lt_of_le_of_lt (min_le_right _ _) (by linarith), ?_⟩
  intro t
  set η := min (δ / 3) (M / 2) with hηdef
  have hle : η ≤ δ / 3 := min_le_left _ _
  have hd : dist (t + η) (t - η) < δ := by
    rw [Real.dist_eq, show t + η - (t - η) = 2 * η by ring, abs_of_pos (by linarith)]
    linarith
  have hkey := hδ' hd
  have hlt : f.toOrderIso (t - η) < f.toOrderIso (t + η) :=
    f.toOrderIso.lt_iff_lt.mpr (by linarith)
  rw [Real.dist_eq, abs_of_pos (by linarith)] at hkey
  exact hkey

end NormalizedShift

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
