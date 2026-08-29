/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.StabilityFunction.PhaseGeometry

/-!
# Finite sums in the semi-closed upper half-plane

This file extends the owner phase-geometry API from binary sums to nonempty
finite sums and records determinant formulations used by HN-polygon proofs.
-/

noncomputable section

open CategoryTheory Complex
open scoped BigOperators

namespace CategoryTheory.Triangulated

/-- Positive argument places a complex number in the semi-closed upper half-plane. -/
theorem mem_semiClosedUpperHalfPlane_of_arg_pos {z : ℂ}
    (hz : 0 < Complex.arg z) : z ∈ semiClosedUpperHalfPlane := by
  by_cases him : 0 < z.im
  · exact Or.inl him
  · right
    have him_nonpos : z.im ≤ 0 := le_of_not_gt him
    have him_zero : z.im = 0 := by
      by_contra hne
      have him_neg : z.im < 0 := lt_of_le_of_ne him_nonpos hne
      exact (not_lt_of_ge hz.le) (Complex.arg_neg_iff.mpr him_neg)
    refine ⟨him_zero, ?_⟩
    by_contra hre
    have hre_nonneg : 0 ≤ z.re := le_of_not_gt hre
    have hz_real : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him_zero)
    have harg_zero : Complex.arg z = 0 := by
      rw [hz_real, Complex.arg_ofReal_of_nonneg hre_nonneg]
    linarith

/-- A nonempty finite sum of upper-half-plane vectors stays in that half-plane. -/
theorem sum_mem_semiClosedUpperHalfPlane {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) {f : ι → ℂ}
    (hf : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane) :
    ∑ i ∈ s, f i ∈ semiClosedUpperHalfPlane := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simpa using hf j (Finset.mem_singleton_self j)
  | cons j s hjs hs ih =>
      rw [Finset.sum_cons]
      exact add_mem_semiClosedUpperHalfPlane
        (hf j (Finset.mem_cons_self j s))
        (ih (fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))))

/-- The argument of a nonempty upper-half-plane sum is at most the largest summand argument. -/
theorem arg_sum_le_sup_of_semiClosedUpperHalfPlane {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) {f : ι → ℂ}
    (hf : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane) :
    Complex.arg (∑ i ∈ s, f i) ≤ s.sup' hs (Complex.arg ∘ f) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp
  | cons j s hjs hs ih =>
      rw [Finset.sum_cons]
      have hfj := hf j (Finset.mem_cons_self j s)
      have hfs : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane :=
        fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))
      calc
        Complex.arg (f j + ∑ i ∈ s, f i)
            ≤ max (Complex.arg (f j)) (Complex.arg (∑ i ∈ s, f i)) :=
          arg_add_le_max hfj (sum_mem_semiClosedUpperHalfPlane hs hfs)
        _ ≤ max (Complex.arg (f j)) (s.sup' hs (Complex.arg ∘ f)) :=
          max_le_max_left _ (ih hfs)
        _ = max ((Complex.arg ∘ f) j) (s.sup' hs (Complex.arg ∘ f)) := rfl
        _ ≤ (Finset.cons j s hjs).sup'
              ⟨j, Finset.mem_cons_self j s⟩ (Complex.arg ∘ f) := by
          rw [Finset.sup'_cons hs]

/-- The argument of a nonempty upper-half-plane sum is at least the smallest summand argument. -/
theorem inf_le_arg_sum_of_semiClosedUpperHalfPlane {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) {f : ι → ℂ}
    (hf : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane) :
    s.inf' hs (Complex.arg ∘ f) ≤ Complex.arg (∑ i ∈ s, f i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton j => simp
  | cons j s hjs hs ih =>
      rw [Finset.sum_cons]
      have hfj := hf j (Finset.mem_cons_self j s)
      have hfs : ∀ i ∈ s, f i ∈ semiClosedUpperHalfPlane :=
        fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))
      calc
        (Finset.cons j s hjs).inf'
              ⟨j, Finset.mem_cons_self j s⟩ (Complex.arg ∘ f)
            = min ((Complex.arg ∘ f) j) (s.inf' hs (Complex.arg ∘ f)) := by
          rw [Finset.inf'_cons hs]
        _ ≤ min (Complex.arg (f j)) (Complex.arg (∑ i ∈ s, f i)) :=
          min_le_min_left _ (ih hfs)
        _ ≤ Complex.arg (f j + ∑ i ∈ s, f i) :=
          min_arg_le_arg_add hfj (sum_mem_semiClosedUpperHalfPlane hs hfs)

/-- Nondecreasing arguments give a nonnegative planar cross product. -/
theorem cross_nonneg_of_arg_le {z w : ℂ}
    (hzIm : 0 ≤ z.im) (hz : z ≠ 0) (hw : w ≠ 0)
    (harg : Complex.arg z ≤ Complex.arg w) :
    0 ≤ z.re * w.im - z.im * w.re := by
  simpa [phaseCross] using phaseCross_nonneg_of_arg_le hzIm hz hw harg

/-- A nonnegative cross product recovers the argument order in the upper half-plane. -/
theorem arg_le_of_cross_nonneg {z w : ℂ}
    (hz : z ≠ 0) (hw : w ≠ 0) (hwArg : 0 < Complex.arg w)
    (hcross : 0 ≤ z.re * w.im - z.im * w.re) :
    Complex.arg z ≤ Complex.arg w := by
  apply arg_le_of_phaseCross_nonneg hz hw hwArg
  simpa [phaseCross] using hcross

/-- Strictly increasing positive arguments give a positive planar cross product. -/
theorem cross_pos_of_arg_lt {z w : ℂ}
    (hzArg : 0 < Complex.arg z) (hz : z ≠ 0) (hw : w ≠ 0)
    (harg : Complex.arg z < Complex.arg w) :
    0 < z.re * w.im - z.im * w.re := by
  simpa [phaseCross] using phaseCross_pos_of_arg_lt hzArg hz hw harg

end CategoryTheory.Triangulated
