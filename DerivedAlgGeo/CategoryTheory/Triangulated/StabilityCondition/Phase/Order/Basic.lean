/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.CoreConsequences

/-!
# Order relations on slicings

This file introduces the strict and weak relations on slicings used by both
arXiv:2601.22994, Definition 2.1, and arXiv:2607.28411v1, Definition 3.12.
They compare the phase of an object in the first slicing with the upper HN
phase of the same object in the second slicing.

The source papers use different symbols for the same relations.  The named
predicates here keep that comparison independent of notation and of any
central charge or geometric realization.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The strict order on slicings: every object of phase `phi` for `s` has all
HN phases strictly below `phi` for `t`.

This is `P_s(phi) ⊆ P_t(< phi)` in arXiv:2601.22994, Definition 2.1, and
`P_s ≺ P_t` in arXiv:2607.28411v1, Definition 3.12. -/
def Slicing.Precedes (s t : Slicing C) : Prop :=
  ∀ phi : ℝ, s.P phi ≤ t.ltProp C phi

/-- The weak order on slicings: every object of phase `phi` for `s` has all
HN phases at most `phi` for `t`.

This is `P_s(phi) ⊆ P_t(≤ phi)` in both source papers. -/
def Slicing.PrecedesWeak (s t : Slicing C) : Prop :=
  ∀ phi : ℝ, s.P phi ≤ t.leProp C phi

/-- Li's strict order notation, retained as a source-facing alias of the
canonical strict slicing order. -/
abbrev Slicing.LiPrecedes (s t : Slicing C) : Prop := s.Precedes C t

/-- Li's weak order notation, retained as a source-facing alias of the
canonical weak slicing order. -/
abbrev Slicing.LiPrecedesWeak (s t : Slicing C) : Prop := s.PrecedesWeak C t

/-- The strict relation of arXiv:2601.22994, Definition 2.1, is exactly the
strict relation of arXiv:2607.28411v1, Definition 3.12. -/
theorem Slicing.liPrecedes_iff_precedes (s t : Slicing C) :
    s.LiPrecedes C t ↔ s.Precedes C t := Iff.rfl

/-- The weak relation of arXiv:2601.22994, Definition 2.1, is exactly the weak
relation of arXiv:2607.28411v1, Definition 3.12. -/
theorem Slicing.liPrecedesWeak_iff_precedesWeak (s t : Slicing C) :
    s.LiPrecedesWeak C t ↔ s.PrecedesWeak C t := Iff.rfl

/-- The strict slicing order is equivalent to its upper-phase formulation on
nonzero objects semistable for the left-hand slicing. -/
theorem Slicing.precedes_iff_phiPlus_lt (s t : Slicing C) :
    s.Precedes C t ↔
      ∀ {E : C} {phi : ℝ} (_hE : s.P phi E) (hE0 : ¬IsZero E),
        t.phiPlus C E hE0 < phi := by
  constructor
  · intro h E phi hE hE0
    exact t.phiPlus_lt_of_ltProp C hE0 (h phi E hE)
  · intro h phi E hE
    by_cases hE0 : IsZero E
    · exact Or.inl hE0
    · exact t.ltProp_of_phiPlus_lt C hE0 (h hE hE0)

/-- The weak slicing order is equivalent to its upper-phase formulation on
nonzero objects semistable for the left-hand slicing. -/
theorem Slicing.precedesWeak_iff_phiPlus_le (s t : Slicing C) :
    s.PrecedesWeak C t ↔
      ∀ {E : C} {phi : ℝ} (_hE : s.P phi E) (hE0 : ¬IsZero E),
        t.phiPlus C E hE0 ≤ phi := by
  constructor
  · intro h E phi hE hE0
    exact t.phiPlus_le_of_leProp C hE0 (h phi E hE)
  · intro h phi E hE
    by_cases hE0 : IsZero E
    · exact Or.inl hE0
    · exact t.leProp_of_phiPlus_le C hE0 (h hE hE0)

/-- A strict comparison is, in particular, a weak comparison. -/
theorem Slicing.Precedes.weak {s t : Slicing C} (h : s.Precedes C t) :
    s.PrecedesWeak C t := by
  intro phi E hE
  exact t.leProp_of_ltProp C E (h phi E hE)

/-- The weak slicing order is reflexive. -/
theorem Slicing.precedesWeak_refl (s : Slicing C) : s.PrecedesWeak C s := by
  intro phi E hE
  exact s.leProp_of_semistable C hE le_rfl

/-- Shifting all phases down by one strictly increases a slicing in the order:
`P ≺ P[1]`, where `P[1](phi) = P(phi + 1)`. -/
theorem Slicing.precedes_phaseShift_one (s : Slicing C) :
    s.Precedes C (s.phaseShift C 1) := by
  intro phi E hE
  apply (s.phaseShift_ltProp C 1 phi E).mpr
  refine Or.inr ⟨HNFiltration.single C E phi hE, one_pos, ?_⟩
  change phi < phi + 1
  linarith

/-- Shifting a slicing down by `t` subtracts `t` from the highest phase of a
nonzero object. -/
theorem Slicing.phaseShift_phiPlus (s : Slicing C) (t : ℝ) (E : C)
    (hE0 : ¬IsZero E) :
    (s.phaseShift C t).phiPlus C E hE0 = s.phiPlus C E hE0 - t := by
  obtain ⟨F, hn, hfirst, _⟩ := s.exists_hn_nonzero_boundaries C hE0
  rw [(s.phaseShift C t).phiPlus_eq C E hE0 (F.phaseShift (C := C) t) hn hfirst,
    s.phiPlus_eq C E hE0 F hn hfirst]
  rfl

/-- Shifting a slicing down by `t` subtracts `t` from the lowest phase of a
nonzero object. -/
theorem Slicing.phaseShift_phiMinus (s : Slicing C) (t : ℝ) (E : C)
    (hE0 : ¬IsZero E) :
    (s.phaseShift C t).phiMinus C E hE0 = s.phiMinus C E hE0 - t := by
  obtain ⟨F, hn, _, hlast⟩ := s.exists_hn_nonzero_boundaries C hE0
  rw [(s.phaseShift C t).phiMinus_eq C E hE0 (F.phaseShift (C := C) t) hn hlast,
    s.phiMinus_eq C E hE0 F hn hlast]
  rfl

end CategoryTheory.Triangulated
