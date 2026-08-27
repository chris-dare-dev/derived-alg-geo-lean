/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityFunction.WeakCutoff

/-!
# The weak cutoff bounds the object's own slope, not only its factors' slopes

`hnTors W μ₀` and `hnFree W μ₀` are defined by the Harder--Narasimhan *extrema*
`μ⁻` and `μ⁺`.  Every consumer that wants to read a cutoff against a charge needs
the **object's own** slope instead, and the step between them is that
`W.slope E` lies between `μ⁻` and `μ⁺`.

This is `CutoffPhase.lean` for the weak, slope-indexed theory.

## Why this is not the strict proof

`CutoffPhase.lean` gets the strict statement from `HNPolygon.lean`'s
`phase_le_first` and `last_le_phase`, which read the HN filtration as a convex
polygonal path in `ℂ` and cite `ComplexPolygonalPath.arg_last_sub_zero_le_arg_first`.
That apparatus is `arg`-geometry on `semiClosedUpperHalfPlane` and does not
survive the weakening: the charges here may be `0`, where `arg` says nothing.

The weak statement instead falls straight out of the see-saw of
`WeakSlopeGeometry.lean`, by induction along the chain.  Each step adds one
factor charge to the running total, and the see-saw traps the new slope between
the factor's slope and the old total's — so `μ⁺` is never exceeded above and the
current factor's slope is never dropped below.  No polygon, and no convexity
argument.

One thing makes this *easier* than the strict case rather than harder:
`0 ∈ closedUpperHalfPlane`, so `charge_mem_closedUpperHalfPlane` holds for every
object including the zero one, and the induction carries no nonvanishing
side conditions.  In the strict theory that membership fails at `0` and the
bookkeeping is real.

## The payoff

`lt_slope_of_mem_hnTors` and `slope_le_of_mem_hnFree` are what a charge
comparison consumes, and unlike their strict counterparts they carry **no
positive-rank hypothesis**: a rank-zero object has slope `⊤`, which is above
every finite cutoff, so it needs no separate treatment.  On the strict side that
object has to be routed around through `mem_hnTors_of_rank_zero` instead.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

/-- **The slope of a sum lies between the slopes of its summands.**  The two
see-saws combined by `le_total`, in the form an induction over a filtration
consumes. -/
theorem chargeSlope_add_mem_uIcc {z w : ℂ} (hz : z ∈ closedUpperHalfPlane)
    (hw : w ∈ closedUpperHalfPlane) :
    min (chargeSlope z) (chargeSlope w) ≤ chargeSlope (z + w) ∧
      chargeSlope (z + w) ≤ max (chargeSlope z) (chargeSlope w) := by
  rcases le_total (chargeSlope z) (chargeSlope w) with h | h
  · obtain ⟨h₁, h₂⟩ := chargeSlope_le_add_le_of_le hz hw h
    exact ⟨by rw [min_eq_left h]; exact h₁, by rw [max_eq_right h]; exact h₂⟩
  · obtain ⟨h₁, h₂⟩ := chargeSlope_le_add_le_of_le hw hz h
    rw [add_comm] at h₁ h₂
    exact ⟨by rw [min_eq_right h]; exact h₁, by rw [max_eq_left h]; exact h₂⟩

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace WeakStabilityFunctionOn

variable (W : WeakStabilityFunctionOn (abelianDatum A))

/-- **Every object's charge lies in the closed upper half-plane**, the zero
object included: its charge is `0`, which the closed half-plane contains and the
semi-closed one does not.  This is the hypothesis-free membership the strict
theory cannot have. -/
theorem charge_mem_closedUpperHalfPlane (E : A) :
    W.charge E ∈ closedUpperHalfPlane := by
  by_cases h : IsZero E
  · rw [W.map_zero E h]
    exact Or.inr ⟨Complex.zero_im, le_of_eq Complex.zero_re⟩
  · exact W.charge_mem E h

end WeakStabilityFunctionOn

namespace AbelianWeakHNFiltration

variable {W : WeakStabilityFunctionOn (abelianDatum A)} {E : A}
variable (F : AbelianWeakHNFiltration W E)

/-- Each chain step is a short exact sequence with the corresponding factor as
its cokernel, so the charges add. -/
theorem charge_chain_succ (j : Fin F.n) :
    W.charge (F.chain j.succ : A) =
      W.charge (F.chain j.castSucc : A) + W.charge (F.factor j) :=
  W.additive _ (StabilityFunction.shortExact_of_mono
    (Subobject.ofLE (F.chain j.castSucc) (F.chain j.succ)
      (le_of_lt (F.chain_strictMono j.castSucc_lt_succ))))

/-- **The running total of an HN filtration stays inside the slope range.**

Induction along the chain.  At `k = 1` the term is the maximal destabilizing
subobject, whose slope is `μ⁺` exactly.  Each further step adds the next factor,
whose slope is below everything already accumulated, so the see-saw puts the new
total between that factor's slope and the old total's. -/
theorem μ_le_slope_chain_and_le_μPlus :
    ∀ k : ℕ, (hk : 0 < k) → (hkn : k ≤ F.n) →
      F.μ ⟨k - 1, by lia⟩ ≤ W.slope (F.chain ⟨k, by lia⟩ : A) ∧
        W.slope (F.chain ⟨k, by lia⟩ : A) ≤ F.μPlus := by
  intro k
  induction k with
  | zero => intro hk; exact absurd hk (lt_irrefl 0)
  | succ k ih =>
      intro _ hkn
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · -- Base case: the first chain term has slope exactly `μ⁺`.
        have h := F.μ_chain_one
        refine ⟨le_of_eq ?_, le_of_eq h⟩
        rw [h]
        rfl
      · -- Step: add the `k`-th factor to the running total.
        obtain ⟨ihlow, ihhigh⟩ := ih hk (by lia)
        set j : Fin F.n := ⟨k, by lia⟩ with hj
        have hcast : F.chain j.castSucc = F.chain ⟨k, by lia⟩ :=
          congrArg F.chain (Fin.ext (by simp [hj]))
        have hsucc : F.chain j.succ = F.chain ⟨k + 1, by lia⟩ :=
          congrArg F.chain (Fin.ext (by simp [hj]))
        have hadd : W.charge (F.chain ⟨k + 1, by lia⟩ : A) =
            W.charge (F.factor j) + W.charge (F.chain ⟨k, by lia⟩ : A) := by
          rw [← hsucc, F.charge_chain_succ j, hcast, add_comm]
        have hfactor : W.slope (F.factor j) = F.μ j := F.factor_slope j
        have hle : W.slope (F.factor j) ≤ W.slope (F.chain ⟨k, by lia⟩ : A) := by
          rw [hfactor]
          refine le_trans (le_of_lt (F.μ_anti (Fin.mk_lt_mk.mpr ?_))) ihlow
          simp
          lia
        obtain ⟨h₁, h₂⟩ := chargeSlope_le_add_le_of_le
          (W.charge_mem_closedUpperHalfPlane (F.factor j))
          (W.charge_mem_closedUpperHalfPlane (F.chain ⟨k, by lia⟩ : A)) hle
        rw [← hadd] at h₁ h₂
        refine ⟨?_, le_trans h₂ ihhigh⟩
        rw [show (⟨k + 1 - 1, by lia⟩ : Fin F.n) = j from Fin.ext (by simp [hj]),
          ← hfactor]
        exact h₁

/-- **The object's own slope does not exceed the highest HN slope.** -/
theorem slope_le_μPlus : W.slope E ≤ F.μPlus := by
  have hn := F.nonempty
  have h := (F.μ_le_slope_chain_and_le_μPlus F.n hn le_rfl).2
  rwa [F.chain_top, W.slope_eq_of_iso (asIso (⊤ : Subobject E).arrow)] at h

/-- **The lowest HN slope does not exceed the object's own slope.** -/
theorem μMinus_le_slope : F.μMinus ≤ W.slope E := by
  have hn := F.nonempty
  have h := (F.μ_le_slope_chain_and_le_μPlus F.n hn le_rfl).1
  rwa [F.chain_top, W.slope_eq_of_iso (asIso (⊤ : Subobject E).arrow)] at h

end AbelianWeakHNFiltration

namespace WeakStabilityFunctionOn

variable {W : WeakStabilityFunctionOn (abelianDatum A)} {μ₀ : WithTop ℝ}

/-- **An object of the torsion class has slope strictly above the cutoff.**

`hnTors` says every HN slope exceeds `μ₀`; this says the object's own does.  The
zero object is excluded because it has no filtration — `hnTors` admits it
separately.

Unlike `SlopeData.slopeOfPhase_lt_of_mem_hnTors`, there is no positive-rank
hypothesis: a rank-zero object has slope `⊤`, above every finite cutoff, and is
covered by the same statement. -/
theorem lt_slope_of_mem_hnTors (hHN : W.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (h : E ∈ hnTors W μ₀) : μ₀ < W.slope E := by
  obtain ⟨F⟩ := hHN E hE
  exact lt_of_lt_of_le ((mem_hnTors_iff_forall hHN hE).mp h F) F.μMinus_le_slope

/-- **An object of the torsion-free class has slope at most the cutoff.** -/
theorem slope_le_of_mem_hnFree (hHN : W.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (h : E ∈ hnFree W μ₀) : W.slope E ≤ μ₀ :=
  le_trans (Classical.choice (hHN E hE)).slope_le_μPlus
    ((mem_hnFree_iff_forall hHN hE).mp h _)

end WeakStabilityFunctionOn

end CategoryTheory.Triangulated
