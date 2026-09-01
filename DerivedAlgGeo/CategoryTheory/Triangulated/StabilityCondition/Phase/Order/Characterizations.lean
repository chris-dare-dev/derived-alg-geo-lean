/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Order.Basic

/-!
# Intrinsic-phase characterizations of the slicing orders

The strict and weak slicing orders admit three useful descriptions: by the
upper HN phase of objects semistable for the left slicing, by the lower HN
phase of objects semistable for the right slicing, and by both intrinsic HN
endpoints of every nonzero object.  These are the four formulations in
arXiv:2607.28411v1, Lemma 3.13.  The weak form is also arXiv:2601.22994,
Lemma 2.2; the strict form is obtained there by replacing every non-strict
inequality with a strict one.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The strict order is equivalent to the lower-phase formulation on nonzero
objects semistable for the right-hand slicing. -/
theorem Slicing.precedes_iff_lt_phiMinus (s t : Slicing C) :
    s.Precedes C t ↔
      ∀ {E : C} {phi : ℝ} (_hE : t.P phi E) (hE0 : ¬IsZero E),
        phi < s.phiMinus C E hE0 := by
  constructor
  · intro h E phi hE hE0
    obtain ⟨F, hn, _, hlast⟩ := s.exists_hn_nonzero_boundaries C hE0
    let j : Fin F.n := ⟨F.n - 1, by lia⟩
    have hlastPhase : s.phiMinus C E hE0 = F.phiMinus C hn :=
      s.phiMinus_eq C E hE0 F hn hlast
    rw [hlastPhase]
    by_contra hphi
    push Not at hphi
    have hLlt : t.ltProp C (F.phiMinus C hn) (F.triangle j).obj₃ := by
      exact h (F.phiMinus C hn) (F.triangle j).obj₃ (F.semistable j)
    have hEge : t.geProp C (F.phiMinus C hn) E := by
      refine Or.inr ⟨HNFiltration.single C E phi hE, one_pos, ?_⟩
      exact hphi
    have hzero : ∀ f : E ⟶ (F.triangle j).obj₃, f = 0 := fun f ↦
      t.zero_of_geProp_ltProp_general C (F.phiMinus C hn) hEge hLlt f
    exact hlast (F.isZero_factor_last_of_hom_eq_zero C s hn hzero)
  · intro h
    rw [s.precedes_iff_phiPlus_lt C t]
    intro E phi hE hE0
    obtain ⟨F, hn, hfirst, _⟩ := t.exists_hn_nonzero_boundaries C hE0
    let j : Fin F.n := ⟨0, hn⟩
    have hright : F.phiPlus C hn < s.phiMinus C (F.triangle j).obj₃ hfirst := by
      exact h (F.semistable j) hfirst
    have hle : s.phiMinus C (F.triangle j).obj₃ hfirst ≤ phi := by
      by_contra hphi
      push Not at hphi
      have hUgt : s.gtProp C phi (F.triangle j).obj₃ :=
        s.gtProp_of_phiMinus_gt C hfirst hphi
      have hEle : s.leProp C phi E :=
        s.leProp_of_semistable C hE le_rfl
      have hzero : ∀ f : (F.triangle j).obj₃ ⟶ E, f = 0 := fun f ↦
        s.zero_of_gtProp_leProp_general C phi hUgt hEle f
      exact hfirst (F.isZero_factor_zero_of_hom_eq_zero C t hn hzero)
    rw [t.phiPlus_eq C E hE0 F hn hfirst]
    exact hright.trans_le hle

/-- The weak order is equivalent to the lower-phase formulation on nonzero
objects semistable for the right-hand slicing. -/
theorem Slicing.precedesWeak_iff_le_phiMinus (s t : Slicing C) :
    s.PrecedesWeak C t ↔
      ∀ {E : C} {phi : ℝ} (_hE : t.P phi E) (hE0 : ¬IsZero E),
        phi ≤ s.phiMinus C E hE0 := by
  constructor
  · intro h E phi hE hE0
    obtain ⟨F, hn, _, hlast⟩ := s.exists_hn_nonzero_boundaries C hE0
    let j : Fin F.n := ⟨F.n - 1, by lia⟩
    have hlastPhase : s.phiMinus C E hE0 = F.phiMinus C hn :=
      s.phiMinus_eq C E hE0 F hn hlast
    rw [hlastPhase]
    by_contra hphi
    push Not at hphi
    have hLle : t.leProp C (F.phiMinus C hn) (F.triangle j).obj₃ := by
      exact h (F.phiMinus C hn) (F.triangle j).obj₃ (F.semistable j)
    have hEgt : t.gtProp C (F.phiMinus C hn) E := by
      refine Or.inr ⟨HNFiltration.single C E phi hE, one_pos, ?_⟩
      exact hphi
    have hzero : ∀ f : E ⟶ (F.triangle j).obj₃, f = 0 := fun f ↦
      t.zero_of_gtProp_leProp_general C (F.phiMinus C hn) hEgt hLle f
    exact hlast (F.isZero_factor_last_of_hom_eq_zero C s hn hzero)
  · intro h
    rw [s.precedesWeak_iff_phiPlus_le C t]
    intro E phi hE hE0
    obtain ⟨F, hn, hfirst, _⟩ := t.exists_hn_nonzero_boundaries C hE0
    let j : Fin F.n := ⟨0, hn⟩
    have hright : F.phiPlus C hn ≤ s.phiMinus C (F.triangle j).obj₃ hfirst := by
      exact h (F.semistable j) hfirst
    have hle : F.phiPlus C hn ≤ phi := by
      by_contra hphi
      push Not at hphi
      have hUgt : s.gtProp C phi (F.triangle j).obj₃ :=
        s.gtProp_of_phiMinus_gt C hfirst (hphi.trans_le hright)
      have hEle : s.leProp C phi E :=
        s.leProp_of_semistable C hE le_rfl
      have hzero : ∀ f : (F.triangle j).obj₃ ⟶ E, f = 0 := fun f ↦
        s.zero_of_gtProp_leProp_general C phi hUgt hEle f
      exact hfirst (F.isZero_factor_zero_of_hom_eq_zero C t hn hzero)
    rw [t.phiPlus_eq C E hE0 F hn hfirst]
    exact hle

/-- The strict order is equivalent to strict decrease of both intrinsic HN
endpoints on every nonzero object. -/
theorem Slicing.precedes_iff_extreme_phases_lt (s t : Slicing C) :
    s.Precedes C t ↔
      ∀ (E : C) (hE0 : ¬IsZero E),
        t.phiPlus C E hE0 < s.phiPlus C E hE0 ∧
          t.phiMinus C E hE0 < s.phiMinus C E hE0 := by
  constructor
  · intro h E hE0
    have hright : ∀ {E : C} {phi : ℝ}, t.P phi E →
        ∀ hE0 : ¬IsZero E, phi < s.phiMinus C E hE0 :=
      (s.precedes_iff_lt_phiMinus C t).mp h
    constructor
    · obtain ⟨F, hn, hfirst, _⟩ := t.exists_hn_nonzero_boundaries C hE0
      let j : Fin F.n := ⟨0, hn⟩
      have hU : F.phiPlus C hn < s.phiMinus C (F.triangle j).obj₃ hfirst :=
        hright (F.semistable j) hfirst
      rw [t.phiPlus_eq C E hE0 F hn hfirst]
      by_contra hplus
      push Not at hplus
      have hUgt : s.gtProp C (s.phiPlus C E hE0) (F.triangle j).obj₃ :=
        s.gtProp_of_phiMinus_gt C hfirst (hplus.trans_lt hU)
      have hEle : s.leProp C (s.phiPlus C E hE0) E :=
        s.leProp_of_phiPlus_le C hE0 le_rfl
      have hzero : ∀ f : (F.triangle j).obj₃ ⟶ E, f = 0 := fun f ↦
        s.zero_of_gtProp_leProp_general C (s.phiPlus C E hE0) hUgt hEle f
      exact hfirst (F.isZero_factor_zero_of_hom_eq_zero C t hn hzero)
    · obtain ⟨F, hn, _, hlast⟩ := s.exists_hn_nonzero_boundaries C hE0
      let j : Fin F.n := ⟨F.n - 1, by lia⟩
      have hLlt : t.ltProp C (F.phiMinus C hn) (F.triangle j).obj₃ :=
        h (F.phiMinus C hn) (F.triangle j).obj₃ (F.semistable j)
      rw [s.phiMinus_eq C E hE0 F hn hlast]
      by_contra hminus
      push Not at hminus
      have hEge : t.geProp C (F.phiMinus C hn) E :=
        t.geProp_of_phiMinus_ge C hE0 hminus
      have hzero : ∀ f : E ⟶ (F.triangle j).obj₃, f = 0 := fun f ↦
        t.zero_of_geProp_ltProp_general C (F.phiMinus C hn) hEge hLlt f
      exact hlast (F.isZero_factor_last_of_hom_eq_zero C s hn hzero)
  · intro h
    rw [s.precedes_iff_phiPlus_lt C t]
    intro E phi hE hE0
    exact (h E hE0).1.trans_eq
      (s.phiPlus_eq_phiMinus_of_semistable C hE hE0).1

/-- The weak order is equivalent to weak decrease of both intrinsic HN
endpoints on every nonzero object. -/
theorem Slicing.precedesWeak_iff_extreme_phases_le (s t : Slicing C) :
    s.PrecedesWeak C t ↔
      ∀ (E : C) (hE0 : ¬IsZero E),
        t.phiPlus C E hE0 ≤ s.phiPlus C E hE0 ∧
          t.phiMinus C E hE0 ≤ s.phiMinus C E hE0 := by
  constructor
  · intro h E hE0
    have hright : ∀ {E : C} {phi : ℝ}, t.P phi E →
        ∀ hE0 : ¬IsZero E, phi ≤ s.phiMinus C E hE0 :=
      (s.precedesWeak_iff_le_phiMinus C t).mp h
    constructor
    · obtain ⟨F, hn, hfirst, _⟩ := t.exists_hn_nonzero_boundaries C hE0
      let j : Fin F.n := ⟨0, hn⟩
      have hU : F.phiPlus C hn ≤ s.phiMinus C (F.triangle j).obj₃ hfirst :=
        hright (F.semistable j) hfirst
      rw [t.phiPlus_eq C E hE0 F hn hfirst]
      by_contra hplus
      push Not at hplus
      have hUgt : s.gtProp C (s.phiPlus C E hE0) (F.triangle j).obj₃ :=
        s.gtProp_of_phiMinus_gt C hfirst (hplus.trans_le hU)
      have hEle : s.leProp C (s.phiPlus C E hE0) E :=
        s.leProp_of_phiPlus_le C hE0 le_rfl
      have hzero : ∀ f : (F.triangle j).obj₃ ⟶ E, f = 0 := fun f ↦
        s.zero_of_gtProp_leProp_general C (s.phiPlus C E hE0) hUgt hEle f
      exact hfirst (F.isZero_factor_zero_of_hom_eq_zero C t hn hzero)
    · obtain ⟨F, hn, _, hlast⟩ := s.exists_hn_nonzero_boundaries C hE0
      let j : Fin F.n := ⟨F.n - 1, by lia⟩
      have hLle : t.leProp C (F.phiMinus C hn) (F.triangle j).obj₃ :=
        h (F.phiMinus C hn) (F.triangle j).obj₃ (F.semistable j)
      rw [s.phiMinus_eq C E hE0 F hn hlast]
      by_contra hminus
      push Not at hminus
      have hEgt : t.gtProp C (F.phiMinus C hn) E :=
        t.gtProp_of_phiMinus_gt C hE0 hminus
      have hzero : ∀ f : E ⟶ (F.triangle j).obj₃, f = 0 := fun f ↦
        t.zero_of_gtProp_leProp_general C (F.phiMinus C hn) hEgt hLle f
      exact hlast (F.isZero_factor_last_of_hom_eq_zero C s hn hzero)
  · intro h
    rw [s.precedesWeak_iff_phiPlus_le C t]
    intro E phi hE hE0
    exact (h E hE0).1.trans_eq
      (s.phiPlus_eq_phiMinus_of_semistable C hE hE0).1

/-- Transitivity of the strict slicing order. -/
theorem Slicing.Precedes.trans {s t u : Slicing C}
    (hst : s.Precedes C t) (htu : t.Precedes C u) : s.Precedes C u := by
  rw [s.precedes_iff_extreme_phases_lt C u]
  intro E hE0
  have hst' := (s.precedes_iff_extreme_phases_lt C t).mp hst E hE0
  have htu' := (t.precedes_iff_extreme_phases_lt C u).mp htu E hE0
  exact ⟨htu'.1.trans hst'.1, htu'.2.trans hst'.2⟩

/-- Transitivity of the weak slicing order. -/
theorem Slicing.PrecedesWeak.trans {s t u : Slicing C}
    (hst : s.PrecedesWeak C t) (htu : t.PrecedesWeak C u) :
    s.PrecedesWeak C u := by
  rw [s.precedesWeak_iff_extreme_phases_le C u]
  intro E hE0
  have hst' := (s.precedesWeak_iff_extreme_phases_le C t).mp hst E hE0
  have htu' := (t.precedesWeak_iff_extreme_phases_le C u).mp htu E hE0
  exact ⟨htu'.1.trans hst'.1, htu'.2.trans hst'.2⟩

/-- A strict comparison followed by a weak one remains strict. -/
theorem Slicing.Precedes.trans_weak {s t u : Slicing C}
    (hst : s.Precedes C t) (htu : t.PrecedesWeak C u) : s.Precedes C u := by
  rw [s.precedes_iff_extreme_phases_lt C u]
  intro E hE0
  have hst' := (s.precedes_iff_extreme_phases_lt C t).mp hst E hE0
  have htu' := (t.precedesWeak_iff_extreme_phases_le C u).mp htu E hE0
  exact ⟨htu'.1.trans_lt hst'.1, htu'.2.trans_lt hst'.2⟩

/-- A weak comparison followed by a strict one remains strict. -/
theorem Slicing.PrecedesWeak.trans_strict {s t u : Slicing C}
    (hst : s.PrecedesWeak C t) (htu : t.Precedes C u) : s.Precedes C u := by
  rw [s.precedes_iff_extreme_phases_lt C u]
  intro E hE0
  have hst' := (s.precedesWeak_iff_extreme_phases_le C t).mp hst E hE0
  have htu' := (t.precedes_iff_extreme_phases_lt C u).mp htu E hE0
  exact ⟨htu'.1.trans_le hst'.1, htu'.2.trans_le hst'.2⟩

end CategoryTheory.Triangulated
