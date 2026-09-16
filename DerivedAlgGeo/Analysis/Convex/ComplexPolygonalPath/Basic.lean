/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Analysis.Complex.PhaseFiniteSums
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Order.Interval.Set.Monotone

/-!
# Finite polygonal paths in the complex plane

The carrier for a finite polygonal path -- `n` edges presented as `n + 1`
vertices `Fin (n + 1) → ℂ` -- together with its Euclidean `length`, the two
real continuous linear functionals on `ℂ` that the perimeter arguments support
against, and the supporting-hyperplane form of strict clockwise convexity.

## Main declarations

* `crossFunctional r`, the oriented area functional `z ↦ r × z`, and
  `unitRay θ`, the unit vector at angle `θ`.
* `length`, the Euclidean length of a finite path, and
  `norm_last_sub_zero_le_length`: the chord is no longer than the path.
* `exists_strict_support_at_interior`: at an interior vertex of a path whose
  upper-half-plane edge arguments strictly decrease, some real-linear
  functional attains a strict unique maximum there.

## Placement

This is neutral planar geometry and imports no category theory and no
stability. It was the `ComplexPolygonalPath` block of
`StabilityCondition/Weak/Foundation/StabilityFunction/HNPolygon.lean` until
MO1.13 (#1324); nothing in it mentions an object, a filtration or a stability
function, and the Harder--Narasimhan *reading* of these statements -- that the
vertices are subobject charges and the edges are semistable-factor charges --
is the adapter that stayed behind in `HNPolygon.lean`.

The perimeter comparison built on this carrier is the sibling
`ComplexPolygonalPath/Perimeter.lean`.

`Analysis/` is a new top-level subject, added to `KNOWN_SUBJECTS` in
`scripts/check_layering.py` as the conscious act rule 6 requires. The pinned
Mathlib revision has no polygonal-chain length and no perimeter at all
(`Mathlib.Geometry.Polygon.Basic` supplies a vertex tuple with edges and a
boundary, and stops there), so there was no Mathlib owner to reuse; the
convexity API these files do consume, `convexHull`, is owned at that revision
by `Mathlib/Analysis/Convex/Hull.lean`, which is what names the subject.

Declaration names and the `CategoryTheory.Triangulated.ComplexPolygonalPath`
namespace are unchanged, per standing decision 1 of the cutover ledger.
-/

open Complex
open scoped BigOperators

namespace CategoryTheory.Triangulated

noncomputable section

namespace ComplexPolygonalPath

/-- The oriented area functional `z ↦ r × z`, regarded as a continuous
real-linear functional on the complex plane. -/
def crossFunctional (r : ℂ) : ℂ →L[ℝ] ℝ :=
  r.re • Complex.imCLM - r.im • Complex.reCLM

@[simp]
theorem crossFunctional_apply (r z : ℂ) :
    crossFunctional r z = r.re * z.im - r.im * z.re := by
  simp [crossFunctional]

/-- The unit complex vector at angle `θ`. -/
def unitRay (θ : ℝ) : ℂ :=
  (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

@[simp]
theorem unitRay_re (θ : ℝ) : (unitRay θ).re = Real.cos θ := by
  simp only [unitRay, add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, mul_one, sub_zero, add_zero]

@[simp]
theorem unitRay_im (θ : ℝ) : (unitRay θ).im = Real.sin θ := by
  simp only [unitRay, add_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, mul_one, zero_add, add_zero]

/-- A unit ray at an angle strictly between `0` and `π` lies in the open
upper half-plane. -/
theorem unitRay_mem_semiClosedUpperHalfPlane {θ : ℝ} (hθ₀ : 0 < θ)
    (hθπ : θ < Real.pi) : unitRay θ ∈ semiClosedUpperHalfPlane := by
  rw [semiClosedUpperHalfPlane]
  exact Or.inl (by
    change 0 < (unitRay θ).im
    rw [unitRay_im]
    exact Real.sin_pos_of_pos_of_lt_pi hθ₀ hθπ)

/-- On the principal upper-half-plane branch, the argument of `unitRay θ` is
literally `θ`. -/
theorem arg_unitRay {θ : ℝ} (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) :
    Complex.arg (unitRay θ) = θ := by
  unfold unitRay
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_cos_add_sin_mul_I ⟨by linarith [Real.pi_pos], hθπ.le⟩

/-- The cross functional is positive on a vector of strictly larger
upper-half-plane argument. -/
theorem crossFunctional_pos_of_arg_lt {r z : ℂ}
    (hr : r ∈ semiClosedUpperHalfPlane) (hz : z ∈ semiClosedUpperHalfPlane)
    (harg : Complex.arg r < Complex.arg z) :
    0 < crossFunctional r z := by
  rw [crossFunctional_apply]
  exact cross_pos_of_arg_lt (arg_pos_of_mem_semiClosedUpperHalfPlane hr)
    (semiClosedUpperHalfPlane_ne_zero hr) (semiClosedUpperHalfPlane_ne_zero hz) harg

/-- The cross functional is negative on a vector of strictly smaller
upper-half-plane argument. -/
theorem crossFunctional_neg_of_arg_lt {r z : ℂ}
    (hr : r ∈ semiClosedUpperHalfPlane) (hz : z ∈ semiClosedUpperHalfPlane)
    (harg : Complex.arg z < Complex.arg r) :
    crossFunctional r z < 0 := by
  have hpos := cross_pos_of_arg_lt (arg_pos_of_mem_semiClosedUpperHalfPlane hz)
    (semiClosedUpperHalfPlane_ne_zero hz) (semiClosedUpperHalfPlane_ne_zero hr) harg
  rw [crossFunctional_apply]
  linarith

/-- At every interior vertex of a finite path whose upper-half-plane edge
arguments strictly decrease, some real-linear functional has a strict unique
maximum among the path vertices.  This is the supporting-hyperplane form of
strict clockwise convexity. -/
theorem exists_strict_support_at_interior {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (harg : StrictAnti (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc)))
    (k : Fin (n + 1)) (hk₀ : 0 < k) (hkn : k < Fin.last n) :
    ∃ l : ℂ →L[ℝ] ℝ, ∀ j, j ≠ k → l (z j) < l (z k) := by
  let iPrev : Fin n := ⟨k.1 - 1, by omega⟩
  let iNext : Fin n := ⟨k.1, by omega⟩
  have hiPrev_lt_iNext : iPrev < iNext := by
    simp only [iPrev, iNext, Fin.mk_lt_mk]
    omega
  have hargNext_lt_argPrev :
      Complex.arg (z iNext.succ - z iNext.castSucc) <
        Complex.arg (z iPrev.succ - z iPrev.castSucc) :=
    harg hiPrev_lt_iNext
  let θ : ℝ :=
    (Complex.arg (z iPrev.succ - z iPrev.castSucc) +
      Complex.arg (z iNext.succ - z iNext.castSucc)) / 2
  have hargNext_lt_θ : Complex.arg (z iNext.succ - z iNext.castSucc) < θ := by
    dsimp [θ]
    linarith
  have hθ_lt_argPrev : θ < Complex.arg (z iPrev.succ - z iPrev.castSucc) := by
    dsimp [θ]
    linarith
  have hθ₀ : 0 < θ :=
    (arg_pos_of_mem_semiClosedUpperHalfPlane (hedge iNext)).trans hargNext_lt_θ
  have hθπ : θ < Real.pi :=
    hθ_lt_argPrev.trans_le (Complex.arg_le_pi _)
  let r : ℂ := unitRay θ
  let l : ℂ →L[ℝ] ℝ := crossFunctional r
  have hr : r ∈ semiClosedUpperHalfPlane := by
    exact unitRay_mem_semiClosedUpperHalfPlane hθ₀ hθπ
  have hr_arg : Complex.arg r = θ := by
    exact arg_unitRay hθ₀ hθπ
  have hstep_before : ∀ m : Fin (n + 1), m < k →
      l (z m) < l (z (Order.succ m)) := by
    intro m hm
    let i : Fin n := ⟨m.1, by omega⟩
    have hi_le : i ≤ iPrev := by
      simp only [i, iPrev, Fin.mk_le_mk]
      omega
    have hθ_lt_arg_i : θ < Complex.arg (z i.succ - z i.castSucc) :=
      hθ_lt_argPrev.trans_le (harg.antitone hi_le)
    have hpos : 0 < l (z i.succ - z i.castSucc) := by
      exact crossFunctional_pos_of_arg_lt hr (hedge i) (by
        rw [hr_arg]
        exact hθ_lt_arg_i)
    have hm_eq : m = i.castSucc := by
      apply Fin.ext
      rfl
    rw [hm_eq, Fin.orderSucc_castSucc]
    rw [map_sub] at hpos
    linarith
  have hstep_after : ∀ m : Fin (n + 1), k < m →
      l (z m) < l (z (Order.pred m)) := by
    intro m hm
    let i : Fin n := ⟨m.1 - 1, by omega⟩
    have hi_ge : iNext ≤ i := by
      simp only [iNext, i, Fin.mk_le_mk]
      omega
    have harg_i_lt_θ : Complex.arg (z i.succ - z i.castSucc) < θ :=
      (harg.antitone hi_ge).trans_lt hargNext_lt_θ
    have hneg : l (z i.succ - z i.castSucc) < 0 := by
      exact crossFunctional_neg_of_arg_lt hr (hedge i) (by
        rw [hr_arg]
        exact harg_i_lt_θ)
    have hm_eq : m = i.succ := by
      apply Fin.ext
      simp only [i, Fin.succ_mk]
      omega
    rw [hm_eq, Fin.orderPred_succ]
    rw [map_sub] at hneg
    linarith
  have hmono : StrictMonoOn (fun j : Fin (n + 1) ↦ l (z j)) (Set.Iic k) :=
    strictMonoOn_Iic_of_lt_succ hstep_before
  have hanti : StrictAntiOn (fun j : Fin (n + 1) ↦ l (z j)) (Set.Ici k) :=
    strictAntiOn_Ici_of_lt_pred hstep_after
  refine ⟨l, fun j hj ↦ ?_⟩
  rcases lt_or_gt_of_ne hj with hjk | hkj
  · exact hmono (Set.mem_Iic.mpr hjk.le) (Set.mem_Iic.mpr le_rfl) hjk
  · exact hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hkj.le) hkj

/-- The sum of the directed edges of a finite path is its endpoint
displacement. -/
theorem sum_edges_eq_last_sub_zero {n : ℕ} (z : Fin (n + 1) → ℂ) :
    ∑ i : Fin n, (z i.succ - z i.castSucc) = z (Fin.last n) - z 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      let z' : Fin (n + 1) → ℂ := fun i ↦ z i.castSucc
      rw [Fin.sum_univ_castSucc]
      rw [show (∑ x : Fin n, (z x.castSucc.succ - z x.castSucc.castSucc)) =
        z' (Fin.last n) - z' 0 by simpa [z'] using ih z']
      change z (Fin.last n).castSucc - z 0 +
          (z (Fin.last n).succ - z (Fin.last n).castSucc) =
        z (Fin.last (n + 1)) - z 0
      have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        rfl
      rw [hlast]
      ring

/-- For an upper-half-plane path with decreasing edge arguments, the
argument of its total displacement is bounded above by the argument of its
first edge. -/
theorem arg_last_sub_zero_le_arg_first {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hn : 0 < n)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (harg : Antitone (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc))) :
    Complex.arg (z (Fin.last n) - z 0) ≤
      Complex.arg (z (Fin.succ ⟨0, hn⟩) - z (Fin.castSucc ⟨0, hn⟩)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let s : Finset (Fin n) := Finset.univ
  have hs : s.Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [← sum_edges_eq_last_sub_zero]
  refine (arg_sum_le_sup_of_semiClosedUpperHalfPlane hs (fun i _ ↦ hedge i)).trans ?_
  apply Finset.sup'_le hs
  intro i _
  exact harg (Fin.zero_le i)

/-- For an upper-half-plane path with decreasing edge arguments, the
argument of its last edge is bounded above by the argument of its total
displacement. -/
theorem arg_last_edge_le_arg_last_sub_zero {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hn : 0 < n)
    (hedge : ∀ i : Fin n, z i.succ - z i.castSucc ∈ semiClosedUpperHalfPlane)
    (harg : Antitone (fun i : Fin n ↦
      Complex.arg (z i.succ - z i.castSucc))) :
    Complex.arg
        (z (Fin.succ ⟨n - 1, by omega⟩) - z (Fin.castSucc ⟨n - 1, by omega⟩)) ≤
      Complex.arg (z (Fin.last n) - z 0) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let s : Finset (Fin n) := Finset.univ
  have hs : s.Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  rw [← sum_edges_eq_last_sub_zero]
  have hlast_le_inf :
      Complex.arg (z (Fin.succ ⟨n - 1, by omega⟩) -
          z (Fin.castSucc ⟨n - 1, by omega⟩)) ≤
        s.inf' hs (Complex.arg ∘ fun i : Fin n ↦
          z i.succ - z i.castSucc) := by
    apply Finset.le_inf'
    intro i _
    exact harg (Fin.mk_le_mk.mpr (by omega))
  exact hlast_le_inf.trans
    (inf_le_arg_sum_of_semiClosedUpperHalfPlane hs (fun i _ ↦ hedge i))

/-- The Euclidean length of a finite path in the complex plane.  A path with
`n` edges is represented by its `n + 1` vertices. -/
def length {n : ℕ} (z : Fin (n + 1) → ℂ) : ℝ :=
  ∑ i : Fin n, ‖z i.succ - z i.castSucc‖

/-- The straight chord between the endpoints of a finite complex path is no
longer than the path.  This is the metric primitive used when an HN polygonal
boundary is refined by inserting further vertices. -/
theorem norm_last_sub_zero_le_length {n : ℕ} (z : Fin (n + 1) → ℂ) :
    ‖z (Fin.last n) - z 0‖ ≤ length z := by
  induction n with
  | zero => simp [length]
  | succ n ih =>
      let z' : Fin (n + 1) → ℂ := fun i ↦ z i.castSucc
      have htriangle :
          ‖z (Fin.last (n + 1)) - z 0‖ ≤
            ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ +
              ‖z (Fin.last n).castSucc - z 0‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le
          (z (Fin.last (n + 1)) - z (Fin.last n).castSucc)
          (z (Fin.last n).castSucc - z 0)
      calc
        ‖z (Fin.last (n + 1)) - z 0‖
            ≤ ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ +
                ‖z (Fin.last n).castSucc - z 0‖ := htriangle
        _ ≤ ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖ + length z' :=
          by
            simpa [z'] using add_le_add_left (ih z')
              ‖z (Fin.last (n + 1)) - z (Fin.last n).castSucc‖
        _ = length z := by
          unfold length
          rw [Fin.sum_univ_castSucc]
          simp [z', add_comm]

end ComplexPolygonalPath

end

end CategoryTheory.Triangulated
