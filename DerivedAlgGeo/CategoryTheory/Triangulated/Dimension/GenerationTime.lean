/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Generators
import Mathlib.Data.ENat.Lattice

/-!
# Generation time: the `ℕ∞`-valued extension-step count

For object properties `P Q` in a pretriangulated category, `P.generationTime Q : ℕ∞` is the
least `n` such that every object of `Q` is reachable from `P` by shifts, binary products,
retracts and at most `n` extensions -- that is, the least `n` with `Q ≤ P.triangEnvelopeIter n`
-- and `⊤` when there is no such `n`. It is the numerical layer on top of Mathlib's
`ObjectProperty.triangEnvelopeIter`, and it introduces no new closure operation.

## The order API

* `generationTime_le_coe_iff`: `P.generationTime Q ≤ n ↔ Q ≤ P.triangEnvelopeIter n`. The
  reverse direction is `sInf_le`; the forward direction uses that `ℕ∞` is well-ordered, so a
  nonempty defining set attains its infimum, and then `monotone'_triangEnvelopeIter`.
* Antitone in `P` (`generationTime_antitone_left`), monotone in `Q`
  (`generationTime_mono_right`).
* The degenerate values: `= 0` exactly when `Q` is already reachable with no extension
  (`generationTime_eq_zero_iff`, unfolded in `generationTime_eq_zero_iff'`), `P.generationTime P
  = 0` unconditionally (`generationTime_self`), and `= ⊤` exactly when no finite number of
  extensions suffices (`generationTime_eq_top_iff`).
* The bridges to Mathlib's predicates: `P` is a strong triangulated generator iff
  `P.generationTime ⊤ ≠ ⊤` (`isStrongTriangulatedGenerator_iff_generationTime_ne_top`), and then
  it is a classical one (`isClassicalTriangulatedGenerator_of_generationTime_ne_top`).

## No side conditions

Nothing here carries a `P.ContainsZero` or `P.Nonempty` hypothesis. Mathlib's
`monotone'_triangEnvelopeIter` has none at the pin -- it discharges the degenerate case
internally -- and carrying one would weaken every lemma downstream, including the Rouquier
dimension characterisations, which instantiate at `ObjectProperty.singleton G`, a property that
is *not* `ContainsZero`.

## Generation time is not subadditive

The bound `P.generationTime R ≤ P.generationTime Q + Q.generationTime R` is **false**, and the
shape of `triangEnvelopeIter_add` is not evidence for it. Reaching `R` from `P` through `Q` does
not compose additively in the extension count: `triangEnvelopeIter_add` says
`P.triangEnvelopeIter (n + m)` is the retract closure of extensions of a `P.triangEnvelopeIter n'`
by a `P.triangEnvelopeIter m`, with `n = n' + 1`, so the count is off by one at every composition
and the honest law is multiplicative in the `⟨-⟩`-index of Bondal--Van den Bergh, where
`⟨P⟩_{n + 1}` is `P.triangEnvelopeIter n`: composing `⟨-⟩_a` with `⟨-⟩_b` lands in `⟨-⟩_{a b}`
(Stacks 0FXA), which in extension counts reads `((a + 1) * (b + 1)) - 1`, not `a + b`. That
composition law is the deliverable of the follow-up issue on composition of iterated envelopes
and is not proved here; do not re-derive an additive bound from `triangEnvelopeIter_add`.
-/

universe v u

namespace CategoryTheory.ObjectProperty

open Pretriangulated

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Generation time.** The least `n : ℕ` with `Q ≤ P.triangEnvelopeIter n`, as an element of
`ℕ∞`; `⊤` when there is none. `sInf` over `ℕ∞` is total, and `sInf ∅ = ⊤` is the junk-value
convention. -/
noncomputable def generationTime (P Q : ObjectProperty C) : ℕ∞ :=
  sInf ((fun m : ℕ ↦ (m : ℕ∞)) '' {m | Q ≤ P.triangEnvelopeIter m})

/-- **The characterisation of generation time.** `P.generationTime Q ≤ n` exactly when `Q` is
reachable from `P` with at most `n` extensions. -/
theorem generationTime_le_coe_iff (P Q : ObjectProperty C) (n : ℕ) :
    P.generationTime Q ≤ n ↔ Q ≤ P.triangEnvelopeIter n := by
  constructor
  · intro h
    by_cases hne : ({m | Q ≤ P.triangEnvelopeIter m} : Set ℕ).Nonempty
    · obtain ⟨m, hm, hmeq⟩ := csInf_mem (hne.image (fun m : ℕ ↦ (m : ℕ∞)))
      have hmn : (m : ℕ∞) ≤ n := hmeq.trans_le h
      exact hm.trans (P.monotone'_triangEnvelopeIter (by exact_mod_cast hmn))
    · exfalso
      rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [generationTime, hne, Set.image_empty, sInf_empty, top_le_iff] at h
      exact ENat.coe_ne_top n h
  · intro h
    exact sInf_le ⟨n, h, rfl⟩

/-- Generation time is antitone in the generating property: more generators, fewer steps. -/
theorem generationTime_antitone_left {P P' : ObjectProperty C} (h : P ≤ P')
    (Q : ObjectProperty C) : P'.generationTime Q ≤ P.generationTime Q :=
  sInf_le_sInf (Set.image_mono fun m hm ↦ hm.trans (monotone_triangEnvelopeIter h m))

/-- Generation time is monotone in the generated property: more to reach, more steps. -/
theorem generationTime_mono_right (P : ObjectProperty C) {Q Q' : ObjectProperty C}
    (h : Q ≤ Q') : P.generationTime Q ≤ P.generationTime Q' :=
  sInf_le_sInf (Set.image_mono fun _ hm ↦ h.trans hm)

/-- Generation time is zero exactly when no extension is needed. -/
theorem generationTime_eq_zero_iff (P Q : ObjectProperty C) :
    P.generationTime Q = 0 ↔ Q ≤ P.triangEnvelopeIter 0 := by
  have := generationTime_le_coe_iff P Q 0
  rwa [Nat.cast_zero, nonpos_iff_eq_zero] at this

/-- Generation time is zero exactly when `Q` lies in the retract closure of binary products of
shifts of `P`: `generationTime_eq_zero_iff` with the zeroth envelope unfolded. -/
theorem generationTime_eq_zero_iff' (P Q : ObjectProperty C) :
    P.generationTime Q = 0 ↔ Q ≤ (P.shiftClosure ℤ).binaryProductsClosure.retractClosure := by
  rw [generationTime_eq_zero_iff, triangEnvelopeIter_zero]

/-- A property generates itself in no steps, unconditionally. -/
theorem generationTime_self (P : ObjectProperty C) : P.generationTime P = 0 :=
  (generationTime_eq_zero_iff P P).2 (P.le_triangEnvelopeIter 0)

/-- Generation time is infinite exactly when no finite number of extensions suffices. -/
theorem generationTime_eq_top_iff (P Q : ObjectProperty C) :
    P.generationTime Q = ⊤ ↔ ∀ n : ℕ, ¬ Q ≤ P.triangEnvelopeIter n := by
  constructor
  · intro h n hn
    have := (generationTime_le_coe_iff P Q n).2 hn
    rw [h, top_le_iff] at this
    exact ENat.coe_ne_top n this
  · intro h
    have hempty : {m | Q ≤ P.triangEnvelopeIter m} = (∅ : Set ℕ) :=
      Set.subset_empty_iff.1 fun m hm ↦ h m hm
    rw [generationTime, hempty, Set.image_empty, sInf_empty]

/-- **Strong generation is finite generation time.** `P` is a strong triangulated generator
exactly when `P.generationTime ⊤ ≠ ⊤`. -/
theorem isStrongTriangulatedGenerator_iff_generationTime_ne_top (P : ObjectProperty C) :
    P.IsStrongTriangulatedGenerator ↔ P.generationTime ⊤ ≠ ⊤ := by
  refine ⟨fun hs h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨n, hn⟩ := (isStrongTriangulatedGenerator_iff P).1 hs
    exact (generationTime_eq_top_iff P ⊤).1 h n (top_le_iff.2 hn)
  · by_contra hcon
    exact h ((generationTime_eq_top_iff P ⊤).2 fun n hn ↦
      hcon ((isStrongTriangulatedGenerator_iff P).2 ⟨n, top_le_iff.1 hn⟩))

/-- Finite generation time makes `P` a classical triangulated generator, through strong
generation. -/
theorem isClassicalTriangulatedGenerator_of_generationTime_ne_top (P : ObjectProperty C)
    (h : P.generationTime ⊤ ≠ ⊤) : P.IsClassicalTriangulatedGenerator :=
  ((isStrongTriangulatedGenerator_iff_generationTime_ne_top P).2 h).isClassicalTriangulatedGenerator

end CategoryTheory.ObjectProperty
