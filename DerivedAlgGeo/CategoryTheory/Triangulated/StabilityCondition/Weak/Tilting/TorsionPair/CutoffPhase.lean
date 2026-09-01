/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.HNPolygon
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Tilting.TorsionPair.StabilityFunction
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.SlopeThreshold

/-!
# The cutoff bounds the object's own phase, not only its factors' phases

`hnTors Z β` and `hnFree Z β` are defined by the Harder–Narasimhan *extrema*
`φ⁻` and `φ⁺`.  Every consumer that wants to read a cutoff against a charge
needs the object's own phase instead, and the step between them is the
statement that `Z.phase E` lies between `φ⁻` and `φ⁺`.

That statement is already proved.  `HNPolygon.lean` has it as
`AbelianHNFiltration.phase_le_first` and `AbelianHNFiltration.last_le_phase`,
stated with the extremal indices written out rather than as `φ⁺` and `φ⁻` — the
HN polygon's first and last edges — which is why it does not surface when one
greps `HarderNarasimhan.lean` for a bound on `Z.phase E`.  This file names them
in the `φ±` vocabulary and draws the two cutoff corollaries.

## Why this matters for Bridgeland's Lemma 6.2

Cases 1--3 of #740 conclude `Im Z(β,ω) > 0` from an object being in the torsion
class at the cutoff.  `Im Z` is a statement about the object, so "all HN phases
exceed `β`" has to become "*this object's* phase exceeds `β`" first.
`lt_phase_of_mem_hnTors` is that step, and it is the whole categorical content
of it — what remains after this is the translation from a phase inequality to a
slope inequality, which is `Slope.lean`'s `phase_le_iff_slope_le` and is not
here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace AbelianHNFiltration

variable {Z : StabilityFunction A} {E : A} (F : AbelianHNFiltration Z E)

/-- **The lowest HN phase does not exceed the object's own phase.**

`last_le_phase` with the extremal index named.  The two statements are the same
term: `phiMinus` is by definition the phase at index `n - 1`. -/
theorem phiMinus_le_phase : F.phiMinus ≤ Z.phase E :=
  F.last_le_phase

/-- **The object's own phase does not exceed the highest HN phase.** -/
theorem phase_le_phiPlus : Z.phase E ≤ F.phiPlus :=
  F.phase_le_first

end AbelianHNFiltration

namespace StabilityFunction

variable {Z : StabilityFunction A} {β : ℝ}

/-- **An object of the torsion class has phase strictly above the cutoff.**

`hnTors` says every HN phase exceeds `β`; this says the object's own phase does.
The zero object is excluded because it has no phase to speak of — `hnTors`
admits it separately. -/
theorem lt_phase_of_mem_hnTors (hHN : Z.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (h : E ∈ hnTors Z β) : β < Z.phase E := by
  obtain ⟨F⟩ := hHN E hE
  exact lt_of_lt_of_le ((mem_hnTors_iff_forall hHN hE).mp h F) F.phiMinus_le_phase

/-- **An object of the torsion-free class has phase at most the cutoff.** -/
theorem phase_le_of_mem_hnFree (hHN : Z.HasHNProperty) {E : A} (hE : ¬IsZero E)
    (h : E ∈ hnFree Z β) : Z.phase E ≤ β := by
  obtain ⟨F⟩ := hHN E hE
  exact le_trans F.phase_le_phiPlus ((mem_hnFree_iff_forall hHN hE).mp h F)

end StabilityFunction

namespace SlopeData

variable (D : SlopeData A)

/-- **The torsion class at a phase cutoff, read as a slope bound.**

The composite of `lt_phase_of_mem_hnTors` with `lt_phase_iff_slopeOfPhase_lt`, and the
statement cases 1--3 of Bridgeland's Lemma 6.2 actually consume: an object of the torsion
class, of positive rank, has slope strictly above the cutoff's slope. From there
`Mukai.im_expCharge_pos` puts the charge in the open upper half plane.

Rank zero is excluded here and handled by `mem_hnTors_of_rank_zero` instead — a rank-zero
object has phase one and no slope, so it belongs to every `T β` for arithmetic reasons rather
than by any comparison. -/
theorem slopeOfPhase_lt_of_mem_hnTors (hHN : D.toStabilityFunction.HasHNProperty) {E : A}
    (hE : 0 < D.rank E) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (h : E ∈ StabilityFunction.hnTors D.toStabilityFunction β) :
    slopeOfPhase β < D.slope E := by
  refine (D.lt_phase_iff_slopeOfPhase_lt hE hβ0 hβ1).mp ?_
  refine StabilityFunction.lt_phase_of_mem_hnTors hHN (fun hzero => ?_) h
  exact absurd (D.rank_zero E hzero) (Int.ne_of_gt hE)

/-- **The torsion-free class, dually.** -/
theorem slope_le_slopeOfPhase_of_mem_hnFree (hHN : D.toStabilityFunction.HasHNProperty) {E : A}
    (hE : 0 < D.rank E) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (h : E ∈ StabilityFunction.hnFree D.toStabilityFunction β) :
    D.slope E ≤ slopeOfPhase β := by
  refine (D.phase_le_iff_le_slopeOfPhase hE hβ0 hβ1).mp ?_
  refine StabilityFunction.phase_le_of_mem_hnFree hHN (fun hzero => ?_) h
  exact absurd (D.rank_zero E hzero) (Int.ne_of_gt hE)

end SlopeData

end CategoryTheory.Triangulated
