/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.FiltrationOperations

/-!
# Real phase shifts of owner slicings

Real phase translation sends the slice at `ψ` to the old slice at `ψ + t`.
This module owns the construction and identifies all four phase-cut predicates
after translation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Translate the phases of an owner HN filtration by a real amount. -/
def HNFiltration.phaseShift {s : Slicing C} {E : C}
    (F : HNFiltration C s.P E) (t : ℝ) :
    HNFiltration C (fun ψ => s.P (ψ + t)) E where
  toPostnikovTower := F.toPostnikovTower
  φ := fun i => F.φ i - t
  hφ := fun i j hij => by linarith [F.hφ hij]
  semistable := by
    intro i
    simpa only [sub_add_cancel] using F.semistable i

/-- Phase-shifted owner slicing: `(s.phaseShift t).P ψ = s.P (ψ + t)`. -/
def Slicing.phaseShift (s : Slicing C) (t : ℝ) : Slicing C where
  P ψ := s.P (ψ + t)
  closedUnderIso ψ := s.closedUnderIso (ψ + t)
  zero_mem ψ := s.zero_mem (ψ + t)
  shift_iff ψ X := by
    show s.P (ψ + t) X ↔ s.P (ψ + 1 + t) (X⟦(1 : ℤ)⟧)
    rw [show ψ + 1 + t = (ψ + t) + 1 by ring]
    exact s.shift_iff (ψ + t) X
  hom_vanishing ψ₁ ψ₂ A B h hA hB :=
    s.hom_vanishing (ψ₁ + t) (ψ₂ + t) A B (by linarith) hA hB
  hn_exists E := ⟨(s.hn_exists E).some.phaseShift C t⟩

/-- The strict lower cut at zero of a shifted slicing is the old cut at the
translation parameter. -/
theorem Slicing.phaseShift_gtProp_zero (s : Slicing C) (t : ℝ) (E : C) :
    (s.phaseShift C t).gtProp C 0 E ↔ s.gtProp C t E := by
  constructor
  · rintro (hzero | ⟨F, hn, hgt⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨⟨F.toPostnikovTower, fun i => F.φ i + t,
        fun i j hij => by linarith [F.hφ hij], F.semistable⟩, hn, ?_⟩
      simp only [HNFiltration.phiMinus] at hgt ⊢
      linarith
  · rintro (hzero | ⟨F, hn, hgt⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨F.phaseShift C t, hn, ?_⟩
      simp only [HNFiltration.phiMinus, HNFiltration.phaseShift] at hgt ⊢
      linarith

/-- A strict lower cut of a shifted slicing is the old cut translated by the
same amount. -/
theorem Slicing.phaseShift_gtProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).gtProp C u E ↔ s.gtProp C (u + t) E := by
  constructor
  · rintro (hzero | ⟨F, hn, hgt⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨⟨F.toPostnikovTower, fun i => F.φ i + t,
        fun i j hij => by linarith [F.hφ hij], F.semistable⟩, hn, ?_⟩
      simp only [HNFiltration.phiMinus] at hgt ⊢
      linarith
  · rintro (hzero | ⟨F, hn, hgt⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨F.phaseShift C t, hn, ?_⟩
      simp only [HNFiltration.phiMinus, HNFiltration.phaseShift] at hgt ⊢
      linarith

/-- The weak upper cut at zero of a shifted slicing is the old cut at the
translation parameter. -/
theorem Slicing.phaseShift_leProp_zero (s : Slicing C) (t : ℝ) (E : C) :
    (s.phaseShift C t).leProp C 0 E ↔ s.leProp C t E := by
  constructor
  · rintro (hzero | ⟨F, hn, hle⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨⟨F.toPostnikovTower, fun i => F.φ i + t,
        fun i j hij => by linarith [F.hφ hij], F.semistable⟩, hn, ?_⟩
      simp only [HNFiltration.phiPlus] at hle ⊢
      linarith
  · rintro (hzero | ⟨F, hn, hle⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨F.phaseShift C t, hn, ?_⟩
      simp only [HNFiltration.phiPlus, HNFiltration.phaseShift] at hle ⊢
      linarith

/-- A weak upper cut of a shifted slicing is the old cut translated by the
same amount. -/
theorem Slicing.phaseShift_leProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).leProp C u E ↔ s.leProp C (u + t) E := by
  constructor
  · rintro (hzero | ⟨F, hn, hle⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨⟨F.toPostnikovTower, fun i => F.φ i + t,
        fun i j hij => by linarith [F.hφ hij], F.semistable⟩, hn, ?_⟩
      simp only [HNFiltration.phiPlus] at hle ⊢
      linarith
  · rintro (hzero | ⟨F, hn, hle⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨F.phaseShift C t, hn, ?_⟩
      simp only [HNFiltration.phiPlus, HNFiltration.phaseShift] at hle ⊢
      linarith

/-- The strict upper cut at zero of a shifted slicing is the old cut at the
translation parameter. -/
theorem Slicing.phaseShift_ltProp_zero (s : Slicing C) (t : ℝ) (E : C) :
    (s.phaseShift C t).ltProp C 0 E ↔ s.ltProp C t E := by
  constructor
  · rintro (hzero | ⟨F, hn, hlt⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨⟨F.toPostnikovTower, fun i => F.φ i + t,
        fun i j hij => by linarith [F.hφ hij], F.semistable⟩, hn, ?_⟩
      simp only [HNFiltration.phiPlus] at hlt ⊢
      linarith
  · rintro (hzero | ⟨F, hn, hlt⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨F.phaseShift C t, hn, ?_⟩
      simp only [HNFiltration.phiPlus, HNFiltration.phaseShift] at hlt ⊢
      linarith

/-- A strict upper cut of a shifted slicing is the old cut translated by the
same amount. -/
theorem Slicing.phaseShift_ltProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).ltProp C u E ↔ s.ltProp C (u + t) E := by
  constructor
  · rintro (hzero | ⟨F, hn, hlt⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨⟨F.toPostnikovTower, fun i => F.φ i + t,
        fun i j hij => by linarith [F.hφ hij], F.semistable⟩, hn, ?_⟩
      simp only [HNFiltration.phiPlus] at hlt ⊢
      linarith
  · rintro (hzero | ⟨F, hn, hlt⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨F.phaseShift C t, hn, ?_⟩
      simp only [HNFiltration.phiPlus, HNFiltration.phaseShift] at hlt ⊢
      linarith

/-- The weak lower cut at zero of a shifted slicing is the old cut at the
translation parameter. -/
theorem Slicing.phaseShift_geProp_zero (s : Slicing C) (t : ℝ) (E : C) :
    (s.phaseShift C t).geProp C 0 E ↔ s.geProp C t E := by
  constructor
  · rintro (hzero | ⟨F, hn, hge⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨⟨F.toPostnikovTower, fun i => F.φ i + t,
        fun i j hij => by linarith [F.hφ hij], F.semistable⟩, hn, ?_⟩
      simp only [HNFiltration.phiMinus] at hge ⊢
      linarith
  · rintro (hzero | ⟨F, hn, hge⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨F.phaseShift C t, hn, ?_⟩
      simp only [HNFiltration.phiMinus, HNFiltration.phaseShift] at hge ⊢
      linarith

/-- A weak lower cut of a shifted slicing is the old cut translated by the
same amount. -/
theorem Slicing.phaseShift_geProp (s : Slicing C) (t u : ℝ) (E : C) :
    (s.phaseShift C t).geProp C u E ↔ s.geProp C (u + t) E := by
  constructor
  · rintro (hzero | ⟨F, hn, hge⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨⟨F.toPostnikovTower, fun i => F.φ i + t,
        fun i j hij => by linarith [F.hφ hij], F.semistable⟩, hn, ?_⟩
      simp only [HNFiltration.phiMinus] at hge ⊢
      linarith
  · rintro (hzero | ⟨F, hn, hge⟩)
    · exact Or.inl hzero
    · refine Or.inr ⟨F.phaseShift C t, hn, ?_⟩
      simp only [HNFiltration.phiMinus, HNFiltration.phaseShift] at hge ⊢
      linarith

end CategoryTheory.Triangulated
