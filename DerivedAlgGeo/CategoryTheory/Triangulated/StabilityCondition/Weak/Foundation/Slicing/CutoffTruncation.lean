/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseCutClosure
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseShift
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseTruncation
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhaseBounds

/-!
# Owner phase truncation at an arbitrary real cutoff

Translate an owner HN filtration so a real cutoff becomes zero, apply the
owner zero-cut truncation, and translate the two phase-cut memberships back.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Every owner HN filtration admits a distinguished truncation triangle at
an arbitrary real phase cutoff. -/
theorem Slicing.exists_cutoff_truncation (s : Slicing C) {A : C}
    (F : HNFiltration C s.P A) (t : ℝ) :
    ∃ (X Y : C) (_ : s.gtProp C t X) (_ : s.leProp C t Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ :=
    (s.phaseShift C t).exists_phase_truncation C A (F.phaseShift C t)
  exact ⟨X, Y, (s.phaseShift_gtProp_zero C t X).mp hX,
    (s.phaseShift_leProp_zero C t Y).mp hY, f, g, h, hT⟩

/-- Truncating an object at a cutoff inside an old phase interval keeps both
pieces in that interval. -/
theorem Slicing.exists_cutoff_truncation_in_interval (s : Slicing C) {A : C}
    (F : HNFiltration C s.P A) {a b t : ℝ}
    (hA : s.intervalProp C a b A) (hat : a ≤ t) (htb : t < b) :
    ∃ (X Y : C) (_ : s.gtProp C t X) (_ : s.leProp C t Y)
      (_ : s.intervalProp C a b X) (_ : s.intervalProp C a b Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ :=
    s.exists_cutoff_truncation C F t
  let T := Triangle.mk f g h
  have hAlt : s.ltProp C b A := s.ltProp_of_intervalProp C hA
  have hAgt : s.gtProp C a A := s.gtProp_of_intervalProp C hA
  have hYlt : s.ltProp C b Y := by
    rcases hY with hzero | ⟨G, hn, hle⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨G, hn, hle.trans_lt htb⟩
  have hXgt : s.gtProp C a X := s.gtProp_anti C hat X hX
  have hXlt : s.ltProp C b X := by
    have hYshift : s.ltProp C (b + (-1 : ℤ)) (Y⟦(-1 : ℤ)⟧) :=
      s.ltProp_shift C b Y (-1) hYlt
    have hYshift' : s.ltProp C b (Y⟦(-1 : ℤ)⟧) :=
      s.ltProp_mono C (by norm_num) _ hYshift
    exact s.ltProp_of_triangle C b hYshift' hAlt
      (inv_rot_of_distTriang T hT)
  have hYgt : s.gtProp C a Y := by
    have hXshift : s.gtProp C (t + (1 : ℤ)) (X⟦(1 : ℤ)⟧) :=
      s.gtProp_shift C t X 1 hX
    have hXshift' : s.gtProp C a (X⟦(1 : ℤ)⟧) :=
      s.gtProp_anti C (by norm_num; linarith) _ hXshift
    exact s.gtProp_of_triangle C a hAgt hXshift'
      (rot_of_distTriang T hT)
  exact ⟨X, Y, hX, hY, s.intervalProp_of_gtProp_ltProp C hXgt hXlt,
    s.intervalProp_of_gtProp_ltProp C hYgt hYlt, f, g, h, hT⟩

end CategoryTheory.Triangulated
