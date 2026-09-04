/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhases
import DerivedAlgGeo.CategoryTheory.Triangulated.ExtensionClosure

/-!
# Extension closure of owner slicing phase cuts

The four HN phase cuts are closed under distinguished extensions.  The proof
uses nonzero boundary factors, owner phase-gap Hom-vanishing, and the Yoneda
exact sequences of a distinguished triangle.

Closure under a single extension propagates along any owner Postnikov tower
through `ExtensionClosure.le_of_closed`, so each cut is also closed under
towers whose factors satisfy it; this is how a condition stated on semistable
objects extends to every object with HN phases on one side of the cut once an
exact functor has been applied factorwise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The owner upper phase cut is closed under distinguished extensions. -/
theorem Slicing.leProp_of_triangle (s : Slicing C) {A E B : C} (t : ℝ)
    (hA : s.leProp C t A) (hB : s.leProp C t B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) : s.leProp C t E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  obtain ⟨F, hn, hfirst⟩ := s.exists_hn_nonzero_first C hE
  refine Or.inr ⟨F, hn, ?_⟩
  by_contra hle
  push Not at hle
  let S := HNFiltration.single C (F.factor ⟨0, hn⟩) (F.φ ⟨0, hn⟩)
    (F.semistable ⟨0, hn⟩)
  have vanish : ∀ {X : C}, s.leProp C t X →
      ∀ q : F.factor ⟨0, hn⟩ ⟶ X, q = 0 := by
    intro X hX q
    rcases hX with hZ | ⟨G, hG, hGle⟩
    · exact hZ.eq_of_tgt q 0
    · exact s.hom_eq_zero_of_phase_gap C S G (fun i j => by
        simp only [S, HNFiltration.single]
        exact ((G.phase_mem_range C hG j).2.trans hGle).trans_lt hle) q
  have hzero : ∀ q : F.factor ⟨0, hn⟩ ⟶ E, q = 0 := by
    intro q
    obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ _ hT q (vanish hB (q ≫ g))
    change F.factor ⟨0, hn⟩ ⟶ A at k
    change q = k ≫ f at hk
    calc q = k ≫ f := hk
      _ = 0 := by rw [vanish hA k, zero_comp]
  exact hfirst (F.firstFactor_isZero_of_hom_eq_zero C s hn hzero)

/-- The owner strict upper phase cut is closed under distinguished extensions. -/
theorem Slicing.ltProp_of_triangle (s : Slicing C) {A E B : C} (t : ℝ)
    (hA : s.ltProp C t A) (hB : s.ltProp C t B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) : s.ltProp C t E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  obtain ⟨F, hn, hfirst⟩ := s.exists_hn_nonzero_first C hE
  refine Or.inr ⟨F, hn, ?_⟩
  by_contra hlt
  push Not at hlt
  let S := HNFiltration.single C (F.factor ⟨0, hn⟩) (F.φ ⟨0, hn⟩)
    (F.semistable ⟨0, hn⟩)
  have vanish : ∀ {X : C}, s.ltProp C t X →
      ∀ q : F.factor ⟨0, hn⟩ ⟶ X, q = 0 := by
    intro X hX q
    rcases hX with hZ | ⟨G, hG, hGlt⟩
    · exact hZ.eq_of_tgt q 0
    · exact s.hom_eq_zero_of_phase_gap C S G (fun i j => by
        simp only [S, HNFiltration.single]
        exact ((G.phase_mem_range C hG j).2.trans_lt hGlt).trans_le hlt) q
  have hzero : ∀ q : F.factor ⟨0, hn⟩ ⟶ E, q = 0 := by
    intro q
    obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ _ hT q (vanish hB (q ≫ g))
    change F.factor ⟨0, hn⟩ ⟶ A at k
    change q = k ≫ f at hk
    calc q = k ≫ f := hk
      _ = 0 := by rw [vanish hA k, zero_comp]
  exact hfirst (F.firstFactor_isZero_of_hom_eq_zero C s hn hzero)

/-- The owner strict lower phase cut is closed under distinguished extensions. -/
theorem Slicing.gtProp_of_triangle (s : Slicing C) {A E B : C} (t : ℝ)
    (hA : s.gtProp C t A) (hB : s.gtProp C t B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) : s.gtProp C t E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  obtain ⟨F, hn, hlast⟩ := s.exists_hn_nonzero_last C hE
  refine Or.inr ⟨F, hn, ?_⟩
  by_contra hgt
  push Not at hgt
  let T := HNFiltration.single C (F.factor ⟨F.n - 1, by omega⟩)
    (F.φ ⟨F.n - 1, by omega⟩) (F.semistable ⟨F.n - 1, by omega⟩)
  have vanish : ∀ {X : C}, s.gtProp C t X →
      ∀ q : X ⟶ F.factor ⟨F.n - 1, by omega⟩, q = 0 := by
    intro X hX q
    rcases hX with hZ | ⟨G, hG, hGgt⟩
    · exact hZ.eq_of_src q 0
    · exact s.hom_eq_zero_of_phase_gap C G T (fun i j => by
        simp only [T, HNFiltration.single]
        exact hgt.trans_lt (hGgt.trans_le (G.phase_mem_range C hG i).1)) q
  have hzero : ∀ q : E ⟶ F.factor ⟨F.n - 1, by omega⟩, q = 0 := by
    intro q
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT q (vanish hA (f ≫ q))
    change B ⟶ F.factor ⟨F.n - 1, by omega⟩ at k
    change q = g ≫ k at hk
    calc q = g ≫ k := hk
      _ = 0 := by rw [vanish hB k, comp_zero]
  exact hlast (F.lastFactor_isZero_of_hom_eq_zero C s hn hzero)

/-- The owner weak lower phase cut is closed under distinguished extensions. -/
theorem Slicing.geProp_of_triangle (s : Slicing C) {A E B : C} (t : ℝ)
    (hA : s.geProp C t A) (hB : s.geProp C t B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) : s.geProp C t E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  obtain ⟨F, hn, hlast⟩ := s.exists_hn_nonzero_last C hE
  refine Or.inr ⟨F, hn, ?_⟩
  by_contra hge
  push Not at hge
  let T := HNFiltration.single C (F.factor ⟨F.n - 1, by omega⟩)
    (F.φ ⟨F.n - 1, by omega⟩) (F.semistable ⟨F.n - 1, by omega⟩)
  have vanish : ∀ {X : C}, s.geProp C t X →
      ∀ q : X ⟶ F.factor ⟨F.n - 1, by omega⟩, q = 0 := by
    intro X hX q
    rcases hX with hZ | ⟨G, hG, hGge⟩
    · exact hZ.eq_of_src q 0
    · exact s.hom_eq_zero_of_phase_gap C G T (fun i j => by
        simp only [T, HNFiltration.single]
        exact hge.trans_le (hGge.trans (G.phase_mem_range C hG i).1)) q
  have hzero : ∀ q : E ⟶ F.factor ⟨F.n - 1, by omega⟩, q = 0 := by
    intro q
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT q (vanish hA (f ≫ q))
    change B ⟶ F.factor ⟨F.n - 1, by omega⟩ at k
    change q = g ≫ k at hk
    calc q = g ≫ k := hk
      _ = 0 := by rw [vanish hB k, comp_zero]
  exact hlast (F.lastFactor_isZero_of_hom_eq_zero C s hn hzero)

/-- An owner Postnikov tower whose factors satisfy the upper phase cut has its
total object satisfying it. -/
theorem Slicing.leProp_of_postnikovTower (s : Slicing C) {E : C} {t : ℝ}
    (P : PostnikovTower C E) (hfactors : ∀ i, s.leProp C t (P.factor i)) :
    s.leProp C t E :=
  ExtensionClosure.le_of_closed (fun hz => s.leProp_of_isZero C hz t) le_rfl
    (fun hT hX hY => s.leProp_of_triangle C t hX hY hT) E
    (ExtensionClosure.ofPostnikovTower P hfactors)

/-- An owner Postnikov tower whose factors satisfy the strict upper phase cut
has its total object satisfying it. -/
theorem Slicing.ltProp_of_postnikovTower (s : Slicing C) {E : C} {t : ℝ}
    (P : PostnikovTower C E) (hfactors : ∀ i, s.ltProp C t (P.factor i)) :
    s.ltProp C t E :=
  ExtensionClosure.le_of_closed (fun hz => s.ltProp_of_isZero C hz t) le_rfl
    (fun hT hX hY => s.ltProp_of_triangle C t hX hY hT) E
    (ExtensionClosure.ofPostnikovTower P hfactors)

/-- An owner Postnikov tower whose factors satisfy the strict lower phase cut
has its total object satisfying it. -/
theorem Slicing.gtProp_of_postnikovTower (s : Slicing C) {E : C} {t : ℝ}
    (P : PostnikovTower C E) (hfactors : ∀ i, s.gtProp C t (P.factor i)) :
    s.gtProp C t E :=
  ExtensionClosure.le_of_closed (fun hz => s.gtProp_of_isZero C hz t) le_rfl
    (fun hT hX hY => s.gtProp_of_triangle C t hX hY hT) E
    (ExtensionClosure.ofPostnikovTower P hfactors)

/-- An owner Postnikov tower whose factors satisfy the lower phase cut has its
total object satisfying it. -/
theorem Slicing.geProp_of_postnikovTower (s : Slicing C) {E : C} {t : ℝ}
    (P : PostnikovTower C E) (hfactors : ∀ i, s.geProp C t (P.factor i)) :
    s.geProp C t E :=
  ExtensionClosure.le_of_closed (fun hz => s.geProp_of_isZero C hz t) le_rfl
    (fun hT hX hY => s.geProp_of_triangle C t hX hY hT) E
    (ExtensionClosure.ofPostnikovTower P hfactors)

end CategoryTheory.Triangulated
