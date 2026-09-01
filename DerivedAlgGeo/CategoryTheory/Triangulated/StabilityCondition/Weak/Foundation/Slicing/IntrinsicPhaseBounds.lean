/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseCutClosure

/-!
# Intrinsic phase bounds and interval membership

This module characterizes owner interval membership using intrinsic highest
and lowest phases.  It also supplies the interval-widening operations used by
the deformed-slicing construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Enlarging both endpoints preserves owner interval membership. -/
theorem Slicing.intervalProp_mono (s : Slicing C) {a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    s.intervalProp C a₁ b₁ ≤ s.intervalProp C a₂ b₂ := by
  intro E hE
  rcases hE with hE | ⟨F, hF⟩
  · exact Or.inl hE
  · exact Or.inr ⟨F, fun i => ⟨ha.trans_lt (hF i).1, (hF i).2.trans_le hb⟩⟩

/-- A radius increase widens a centered owner interval. -/
theorem Slicing.intervalProp_widen (s : Slicing C) {E : C} {φ ε δ : ℝ}
    (hE : s.intervalProp C (φ - ε) (φ + ε) E) (hεδ : ε ≤ δ) :
    s.intervalProp C (φ - δ) (φ + δ) E :=
  s.intervalProp_mono C (by linarith) (by linarith) E hE

/-- Interval membership bounds the intrinsic highest phase from above. -/
theorem Slicing.phiPlus_lt_of_intervalProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    s.phiPlus C E hE < b := by
  rcases hI with hzero | ⟨F, hF⟩
  · exact (hE hzero).elim
  · have hn : 0 < F.n := F.n_pos C hE
    obtain ⟨G, hG, hfirst⟩ := s.exists_hn_nonzero_first C hE
    calc
      s.phiPlus C E hE = G.phiPlus C hG := s.phiPlus_eq C E hE G hG hfirst
      _ ≤ F.phiPlus C hn := G.phiPlus_le_of_firstFactor_nonzero C s F hG hn hfirst
      _ < b := (hF ⟨0, hn⟩).2

/-- Interval membership bounds the intrinsic lowest phase from below. -/
theorem Slicing.phiMinus_gt_of_intervalProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    a < s.phiMinus C E hE := by
  rcases hI with hzero | ⟨F, hF⟩
  · exact (hE hzero).elim
  · have hn : 0 < F.n := F.n_pos C hE
    obtain ⟨G, hG, hlast⟩ := s.exists_hn_nonzero_last C hE
    calc
      a < F.phiMinus C hn := (hF ⟨F.n - 1, by omega⟩).1
      _ ≤ G.phiMinus C hG := F.phiMinus_le_of_lastFactor_nonzero C s G hn hG hlast
      _ = s.phiMinus C E hE := (s.phiMinus_eq C E hE G hG hlast).symm

/-- Interval membership bounds the intrinsic highest phase from below. -/
theorem Slicing.phiPlus_gt_of_intervalProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    a < s.phiPlus C E hE :=
  (s.phiMinus_gt_of_intervalProp C hE hI).trans_le
    (s.phiMinus_le_phiPlus C E hE)

/-- Interval membership bounds the intrinsic lowest phase from above. -/
theorem Slicing.phiMinus_lt_of_intervalProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    s.phiMinus C E hE < b :=
  (s.phiMinus_le_phiPlus C E hE).trans_lt
    (s.phiPlus_lt_of_intervalProp C hE hI)

/-- Intrinsic phase bounds imply owner interval membership. -/
theorem Slicing.intervalProp_of_intrinsic_phases (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ}
    (hminus : a < s.phiMinus C E hE) (hplus : s.phiPlus C E hE < b) :
    s.intervalProp C a b E := by
  obtain ⟨F, hn, hFplus, hFminus⟩ := s.exists_hn_intrinsic_width C hE
  refine Or.inr ⟨F, fun i => ⟨?_, ?_⟩⟩
  · calc
      a < s.phiMinus C E hE := hminus
      _ = F.phiMinus C hn := hFminus.symm
      _ ≤ F.φ i := (F.phase_mem_range C hn i).1
  · calc
      F.φ i ≤ F.phiPlus C hn := (F.phase_mem_range C hn i).2
      _ = s.phiPlus C E hE := hFplus
      _ < b := hplus

/-- Membership in two owner intervals implies membership in their
intersection. -/
theorem Slicing.intervalProp_intersection (s : Slicing C) {E : C}
    {a b c d : ℝ} (hab : s.intervalProp C a b E)
    (hcd : s.intervalProp C c d E) :
    s.intervalProp C (max a c) (min b d) E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  · apply s.intervalProp_of_intrinsic_phases C hE
    · exact max_lt
        (s.phiMinus_gt_of_intervalProp C hE hab)
        (s.phiMinus_gt_of_intervalProp C hE hcd)
    · exact lt_min
        (s.phiPlus_lt_of_intervalProp C hE hab)
        (s.phiPlus_lt_of_intervalProp C hE hcd)

/-- For a nonzero object, owner interval membership is equivalent to bounds
on both intrinsic phase extrema. -/
theorem Slicing.intervalProp_iff_intrinsic_phases (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} :
    s.intervalProp C a b E ↔
      a < s.phiMinus C E hE ∧ s.phiPlus C E hE < b := by
  constructor
  · intro hI
    exact ⟨s.phiMinus_gt_of_intervalProp C hE hI,
      s.phiPlus_lt_of_intervalProp C hE hI⟩
  · rintro ⟨hminus, hplus⟩
    exact s.intervalProp_of_intrinsic_phases C hE hminus hplus

/-- All four intrinsic extrema of a nonzero interval object lie between the
interval endpoints. -/
theorem Slicing.intrinsic_phases_mem_interval (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    a < s.phiPlus C E hE ∧ s.phiPlus C E hE < b ∧
      a < s.phiMinus C E hE ∧ s.phiMinus C E hE < b :=
  ⟨s.phiPlus_gt_of_intervalProp C hE hI,
    s.phiPlus_lt_of_intervalProp C hE hI,
    s.phiMinus_gt_of_intervalProp C hE hI,
    s.phiMinus_lt_of_intervalProp C hE hI⟩

/-- A strict bound on the intrinsic lowest phase yields the corresponding
strict lower phase cut. -/
theorem Slicing.gtProp_of_phiMinus_gt (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a : ℝ} (h : a < s.phiMinus C E hE) :
    s.gtProp C a E := by
  obtain ⟨F, hn, _, hminus⟩ := s.exists_hn_intrinsic_width C hE
  exact Or.inr ⟨F, hn, by rw [hminus]; exact h⟩

/-- A weak bound on the intrinsic lowest phase yields the corresponding weak
lower phase cut. -/
theorem Slicing.geProp_of_phiMinus_ge (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a : ℝ} (h : a ≤ s.phiMinus C E hE) :
    s.geProp C a E := by
  obtain ⟨F, hn, _, hminus⟩ := s.exists_hn_intrinsic_width C hE
  exact Or.inr ⟨F, hn, by rw [hminus]; exact h⟩

/-- A weak bound on the intrinsic highest phase yields the corresponding weak
upper phase cut. -/
theorem Slicing.leProp_of_phiPlus_le (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {b : ℝ} (h : s.phiPlus C E hE ≤ b) :
    s.leProp C b E := by
  obtain ⟨F, hn, hplus, _⟩ := s.exists_hn_intrinsic_width C hE
  exact Or.inr ⟨F, hn, by rw [hplus]; exact h⟩

/-- A strict bound on the intrinsic highest phase yields the corresponding
strict upper phase cut. -/
theorem Slicing.ltProp_of_phiPlus_lt (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {b : ℝ} (h : s.phiPlus C E hE < b) :
    s.ltProp C b E := by
  obtain ⟨F, hn, hplus, _⟩ := s.exists_hn_intrinsic_width C hE
  exact Or.inr ⟨F, hn, by rw [hplus]; exact h⟩

/-- Membership in a strict lower phase cut bounds the intrinsic lowest phase. -/
theorem Slicing.phiMinus_gt_of_gtProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a : ℝ} (h : s.gtProp C a E) :
    a < s.phiMinus C E hE := by
  rcases h with hzero | ⟨F, hn, hminus⟩
  · exact (hE hzero).elim
  · obtain ⟨G, hG, hlast⟩ := s.exists_hn_nonzero_last C hE
    calc
      a < F.phiMinus C hn := hminus
      _ ≤ G.phiMinus C hG :=
        F.phiMinus_le_of_lastFactor_nonzero C s G hn hG hlast
      _ = s.phiMinus C E hE := (s.phiMinus_eq C E hE G hG hlast).symm

/-- Membership in a weak lower phase cut bounds the intrinsic lowest phase. -/
theorem Slicing.phiMinus_ge_of_geProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a : ℝ} (h : s.geProp C a E) :
    a ≤ s.phiMinus C E hE := by
  rcases h with hzero | ⟨F, hn, hminus⟩
  · exact (hE hzero).elim
  · obtain ⟨G, hG, hlast⟩ := s.exists_hn_nonzero_last C hE
    calc
      a ≤ F.phiMinus C hn := hminus
      _ ≤ G.phiMinus C hG :=
        F.phiMinus_le_of_lastFactor_nonzero C s G hn hG hlast
      _ = s.phiMinus C E hE := (s.phiMinus_eq C E hE G hG hlast).symm

/-- Membership in a weak upper phase cut bounds the intrinsic highest phase. -/
theorem Slicing.phiPlus_le_of_leProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {b : ℝ} (h : s.leProp C b E) :
    s.phiPlus C E hE ≤ b := by
  rcases h with hzero | ⟨F, hn, hplus⟩
  · exact (hE hzero).elim
  · obtain ⟨G, hG, hfirst⟩ := s.exists_hn_nonzero_first C hE
    calc
      s.phiPlus C E hE = G.phiPlus C hG :=
        s.phiPlus_eq C E hE G hG hfirst
      _ ≤ F.phiPlus C hn :=
        G.phiPlus_le_of_firstFactor_nonzero C s F hG hn hfirst
      _ ≤ b := hplus

/-- Membership in a strict upper phase cut bounds the intrinsic highest phase. -/
theorem Slicing.phiPlus_lt_of_ltProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {b : ℝ} (h : s.ltProp C b E) :
    s.phiPlus C E hE < b := by
  rcases h with hzero | ⟨F, hn, hplus⟩
  · exact (hE hzero).elim
  · obtain ⟨G, hG, hfirst⟩ := s.exists_hn_nonzero_first C hE
    calc
      s.phiPlus C E hE = G.phiPlus C hG :=
        s.phiPlus_eq C E hE G hG hfirst
      _ ≤ F.phiPlus C hn :=
        G.phiPlus_le_of_firstFactor_nonzero C s F hG hn hfirst
      _ < b := hplus

/-- A weak upper phase bound becomes a strict upper phase bound after strictly
enlarging its endpoint. -/
theorem Slicing.ltProp_of_leProp_of_lt (s : Slicing C) {a b : ℝ}
    (hab : a < b) : s.leProp C a ≤ s.ltProp C b := by
  rintro E (hE | ⟨F, hF, hle⟩)
  · exact Or.inl hE
  · exact Or.inr ⟨F, hF, hle.trans_lt hab⟩

/-- In a distinguished triangle `A → E → B → A[1]` whose outer
terms lie in an interval of width at most one, the highest phase of the first
term is at most the highest phase of the middle term. -/
theorem Slicing.phiPlus_triangle_le (s : Slicing C) {A E B : C}
    (hA : ¬IsZero A) (hE : ¬IsZero E)
    {a b : ℝ} (hab : b ≤ a + 1)
    (hA_int : s.intervalProp C a b A)
    (hB_int : s.intervalProp C a b B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.phiPlus C A hA ≤ s.phiPlus C E hE := by
  obtain ⟨FA, hnA, hneA⟩ := s.exists_hn_nonzero_first C hA
  obtain ⟨FE, hnE, hneE⟩ := s.exists_hn_nonzero_first C hE
  rw [s.phiPlus_eq C A hA FA hnA hneA,
    s.phiPlus_eq C E hE FE hnE hneE]
  by_contra hlt
  push Not at hlt
  have hE_gap : ∀ j : Fin FE.n, FE.φ j < FA.φ ⟨0, hnA⟩ := fun j ↦
    lt_of_le_of_lt (FE.hφ.antitone
      (Fin.mk_le_mk.mpr (Nat.zero_le j.val))) hlt
  have hA_factor_zero :
      ∀ α : (FA.triangle ⟨0, hnA⟩).obj₃ ⟶ A, α = 0 := by
    intro α
    let SA := HNFiltration.single C (FA.factor ⟨0, hnA⟩)
      (FA.φ ⟨0, hnA⟩) (FA.semistable ⟨0, hnA⟩)
    have hαf : α ≫ f = 0 := by
      apply s.hom_eq_zero_of_phase_gap C SA FE
      intro i j
      simpa [SA, HNFiltration.single] using hE_gap j
    let T := Triangle.mk f g h
    obtain ⟨β, hβ⟩ := Triangle.coyoneda_exact₂ T.invRotate
      (inv_rot_of_distTriang _ hT) α hαf
    suffices hβ0 : β = 0 by rw [hβ, hβ0, zero_comp]; rfl
    by_cases hBZ : IsZero B
    · exact ((shiftFunctor C (-1 : ℤ)).map_isZero hBZ).eq_of_tgt β 0
    · rcases hB_int with hBZ' | ⟨GB, hGB⟩
      · exact absurd hBZ' hBZ
      · let GBs := GB.shift C s (-1 : ℤ)
        have hnB : 0 < GB.n := GB.n_pos C hBZ
        have hBs_gap : ∀ j : Fin GBs.n,
            GBs.φ j < FA.φ ⟨0, hnA⟩ := by
          intro j
          change GB.φ j + ((-1 : ℤ) : ℝ) < FA.φ ⟨0, hnA⟩
          have h₁ : GB.φ j < b := (hGB j).2
          have h₂ : a < FA.φ ⟨0, hnA⟩ := by
            simpa [HNFiltration.phiPlus] using
              (s.phiPlus_gt_of_intervalProp C hA hA_int).trans_eq
                (s.phiPlus_eq C A hA FA hnA hneA)
          norm_num at *
          linarith
        exact s.hom_eq_zero_of_phase_gap C SA GBs (fun i j ↦ by
          simpa [SA, HNFiltration.single] using hBs_gap j) β
  exact hneA (FA.firstFactor_isZero_of_hom_eq_zero C s hnA hA_factor_zero)

/-- In a distinguished triangle `A → E → B → A[1]` whose outer terms lie
in an interval of width at most one, the lowest phase of the middle term is
at most the lowest phase of the third term. -/
theorem Slicing.phiMinus_triangle_le (s : Slicing C) {A E B : C}
    (hB : ¬IsZero B) (hE : ¬IsZero E)
    {a b : ℝ} (hab : b ≤ a + 1)
    (hA_int : s.intervalProp C a b A)
    (hB_int : s.intervalProp C a b B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.phiMinus C E hE ≤ s.phiMinus C B hB := by
  obtain ⟨FB, hnB, hlastB⟩ := s.exists_hn_nonzero_last C hB
  obtain ⟨FE, hnE, hlastE⟩ := s.exists_hn_nonzero_last C hE
  rw [s.phiMinus_eq C E hE FE hnE hlastE,
    s.phiMinus_eq C B hB FB hnB hlastB]
  by_contra hle
  push Not at hle
  let jB : Fin FB.n := ⟨FB.n - 1, by omega⟩
  let L := HNFiltration.single C (FB.factor jB) (FB.φ jB)
    (FB.semistable jB)
  have hgapE : ∀ i : Fin FE.n, FB.φ jB < FE.φ i := by
    intro i
    exact hle.trans_le
      (FE.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
  have hzero : ∀ q : B ⟶ FB.factor jB, q = 0 := by
    intro q
    have hgq : g ≫ q = 0 := by
      apply s.hom_eq_zero_of_phase_gap C FE L
      intro i j
      simpa [L, HNFiltration.single] using hgapE i
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ (Triangle.mk f g h) hT q hgq
    suffices hkzero : k = 0 by
      calc
        q = (Triangle.mk f g h).mor₃ ≫ k := hk
        _ = 0 := by rw [hkzero, comp_zero]
    by_cases hAzero : IsZero A
    · exact ((shiftFunctor C (1 : ℤ)).map_isZero hAzero).eq_of_src k 0
    · obtain ⟨GA, hGA⟩ := hA_int.resolve_left hAzero
      let GAs := GA.shift C s (1 : ℤ)
      apply s.hom_eq_zero_of_phase_gap C GAs L
      intro i j
      change FB.φ jB < GA.φ i + ((1 : ℤ) : ℝ)
      have hlow : a < GA.φ i := (hGA i).1
      have hhigh : FB.φ jB < b := by
        calc
          FB.φ jB = FB.phiMinus C hnB := rfl
          _ = s.phiMinus C B hB :=
            (s.phiMinus_eq C B hB FB hnB hlastB).symm
          _ ≤ s.phiPlus C B hB := s.phiMinus_le_phiPlus C B hB
          _ < b := s.phiPlus_lt_of_intervalProp C hB hB_int
      norm_num
      linarith
  exact hlastB (FB.lastFactor_isZero_of_hom_eq_zero C s hnB hzero)

/-- In a distinguished triangle `K → E → Q → K[1]`, an upper phase bound
on `E` and a compatible weak upper bound on `Q` bound `K` from above. -/
theorem Slicing.phiPlus_lt_of_triangle_with_leProp (s : Slicing C)
    {K E Q : C} (hK : ¬IsZero K) {b : ℝ}
    (hE_lt : ∀ hE : ¬IsZero E, s.phiPlus C E hE < b)
    {c : ℝ} (hQ_le : s.leProp C c Q) (hcb : c < b + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.phiPlus C K hK < b := by
  let T := Triangle.mk f₁ f₂ f₃
  have hE_upper : s.ltProp C b E := by
    by_cases hE : IsZero E
    · exact Or.inl hE
    · exact s.ltProp_of_phiPlus_lt C hE (hE_lt hE)
  have hQ_shift : s.leProp C (c + ((-1 : ℤ) : ℝ)) (Q⟦(-1 : ℤ)⟧) :=
    s.leProp_shift C c Q (-1) hQ_le
  have hQ_upper : s.ltProp C b (Q⟦(-1 : ℤ)⟧) :=
    s.ltProp_of_leProp_of_lt C (by push_cast; linarith) _ hQ_shift
  have hK_upper : s.ltProp C b K := by
    simpa [T] using s.ltProp_of_triangle C b hQ_upper hE_upper
      (inv_rot_of_distTriang T hT)
  exact s.phiPlus_lt_of_ltProp C hK hK_upper

/-- In a distinguished triangle `K → E → Q → K[1]`, a lower phase bound
on `E` and a compatible strict lower bound on `K` bound `Q` from below. -/
theorem Slicing.phiMinus_gt_of_triangle_with_gtProp (s : Slicing C)
    {K E Q : C} (hQ : ¬IsZero Q) {a : ℝ}
    (hE_gt : ∀ hE : ¬IsZero E, a < s.phiMinus C E hE)
    {c : ℝ} (hK_gt : s.gtProp C c K) (hca : a < c + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    a < s.phiMinus C Q hQ := by
  let T := Triangle.mk f₁ f₂ f₃
  have hE_lower : s.gtProp C a E := by
    by_cases hE : IsZero E
    · exact Or.inl hE
    · exact s.gtProp_of_phiMinus_gt C hE (hE_gt hE)
  have hK_shift : s.gtProp C (c + ((1 : ℤ) : ℝ)) (K⟦(1 : ℤ)⟧) :=
    s.gtProp_shift C c K 1 hK_gt
  have hK_lower : s.gtProp C a (K⟦(1 : ℤ)⟧) :=
    s.gtProp_anti C (by push_cast; linarith) _ hK_shift
  have hQ_lower : s.gtProp C a Q := by
    simpa [T] using s.gtProp_of_triangle C a hE_lower hK_lower
      (rot_of_distTriang T hT)
  exact s.phiMinus_gt_of_gtProp C hQ hQ_lower

/-- The first vertex of a distinguished triangle stays in an open phase
interval when its middle vertex is in that interval and the first and third
vertices satisfy the one-sided bounds supplied by a common heart. -/
theorem Slicing.first_intervalProp_of_triangle (s : Slicing C)
    {a b : ℝ} (hab : a < b) {K E Q : C}
    (hE : s.intervalProp C a b E)
    (hQ_le : s.leProp C (a + 1) Q)
    (hK_gt : s.gtProp C a K)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.intervalProp C a b K := by
  by_cases hK : IsZero K
  · exact Or.inl hK
  · apply s.intervalProp_of_intrinsic_phases C hK
    · exact s.phiMinus_gt_of_gtProp C hK hK_gt
    · exact s.phiPlus_lt_of_triangle_with_leProp C hK
        (fun hEne => s.phiPlus_lt_of_intervalProp C hEne hE)
        hQ_le (by linarith) hT

/-- The intersection of strict lower and upper owner cuts is the corresponding
open owner phase interval. -/
theorem Slicing.intervalProp_of_gtProp_ltProp (s : Slicing C) {E : C}
    {a b : ℝ} (hgt : s.gtProp C a E) (hlt : s.ltProp C b E) :
    s.intervalProp C a b E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  · exact s.intervalProp_of_intrinsic_phases C hE
      (s.phiMinus_gt_of_gtProp C hE hgt)
      (s.phiPlus_lt_of_ltProp C hE hlt)

/-- Open owner phase intervals are extension-closed along distinguished
triangles. -/
theorem Slicing.intervalProp_of_triangle (s : Slicing C)
    {A E B : C} {a b : ℝ}
    (hA : s.intervalProp C a b A) (hB : s.intervalProp C a b B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a b E := by
  exact s.intervalProp_of_gtProp_ltProp C
    (s.gtProp_of_triangle C a (s.gtProp_of_intervalProp C hA)
      (s.gtProp_of_intervalProp C hB) hT)
    (s.ltProp_of_triangle C b (s.ltProp_of_intervalProp C hA)
      (s.ltProp_of_intervalProp C hB) hT)

/-- Every intermediate chain object belongs to an extension-closed slicing
interval when all factors of the Postnikov tower do. -/
theorem Slicing.intervalProp_chain_of_postnikovTower (s : Slicing C)
    {E : C} {a b : ℝ} (P : PostnikovTower C E)
    (hfactors : ∀ i, s.intervalProp C a b (P.factor i))
    (k : ℕ) (hk : k ≤ P.n) :
    s.intervalProp C a b (P.chain.obj' k (by omega)) := by
  induction k with
  | zero =>
      change s.intervalProp C a b P.chain.left
      exact Or.inl P.base_isZero
  | succ k ih =>
      let T := P.triangle ⟨k, by omega⟩
      let e₁ := Classical.choice (P.triangle_obj₁ ⟨k, by omega⟩)
      let e₂ := Classical.choice (P.triangle_obj₂ ⟨k, by omega⟩)
      have h₁ : s.intervalProp C a b T.obj₁ := by
        rcases ih (by omega) with hzero | ⟨F, hF⟩
        · exact Or.inl ((Iso.isZero_iff e₁.symm).mp hzero)
        · exact Or.inr ⟨F.ofIso C e₁.symm, hF⟩
      have h₃ : s.intervalProp C a b T.obj₃ := hfactors ⟨k, by omega⟩
      have h₂ : s.intervalProp C a b T.obj₂ :=
        s.intervalProp_of_triangle C h₁ h₃ (P.triangle_dist ⟨k, by omega⟩)
      rcases h₂ with hzero | ⟨F, hF⟩
      · exact Or.inl ((Iso.isZero_iff e₂).mp hzero)
      · exact Or.inr ⟨F.ofIso C e₂, hF⟩

/-- An owner Postnikov tower whose factors lie in a slicing interval has its
total object in that interval. -/
theorem Slicing.intervalProp_of_postnikovTower (s : Slicing C)
    {E : C} {a b : ℝ} (P : PostnikovTower C E)
    (hfactors : ∀ i, s.intervalProp C a b (P.factor i)) :
    s.intervalProp C a b E := by
  have h := s.intervalProp_chain_of_postnikovTower C P hfactors P.n le_rfl
  change s.intervalProp C a b P.chain.right at h
  rcases h with hzero | ⟨F, hF⟩
  · exact Or.inl ((Iso.isZero_iff (Classical.choice P.top_iso)).mp hzero)
  · exact Or.inr ⟨F.ofIso C (Classical.choice P.top_iso), hF⟩

/-- Semistable slices are extension-closed. -/
theorem Slicing.semistable_of_triangle (s : Slicing C) {A E B : C} (φ : ℝ)
    (hA : s.P φ A) (hB : s.P φ B)
    {f : A ⟶ E} {g : E ⟶ B} {h : B ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) : s.P φ E := by
  by_cases hE : IsZero E
  · exact s.zero_mem_of_isZero C φ E hE
  have hle : s.leProp C φ E :=
    s.leProp_of_triangle C φ
      (s.leProp_of_semistable C hA le_rfl)
      (s.leProp_of_semistable C hB le_rfl) hT
  have hge : s.geProp C φ E :=
    s.geProp_of_triangle C φ
      (s.geProp_of_semistable C hA)
      (s.geProp_of_semistable C hB) hT
  have hplus : s.phiPlus C E hE = φ := by
    apply le_antisymm (s.phiPlus_le_of_leProp C hE hle)
    exact (s.phiMinus_ge_of_geProp C hE hge).trans
      (s.phiMinus_le_phiPlus C E hE)
  have heq : s.phiPlus C E hE = s.phiMinus C E hE := by
    apply le_antisymm
    · rw [hplus]
      exact s.phiMinus_ge_of_geProp C hE hge
    · exact s.phiMinus_le_phiPlus C E hE
  obtain ⟨F, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hE
  have hplusF := (s.phiPlus_eq C E hE F hn hfirst).symm
  have hminusF := (s.phiMinus_eq C E hE F hn hlast).symm
  have hn_eq : F.n = 1 := by
    by_contra hne
    have hlast_lt : F.n - 1 < F.n := by omega
    have htop : F.φ ⟨0, hn⟩ = s.phiPlus C E hE := by
      simpa only [HNFiltration.phiPlus] using hplusF
    have hbot : F.φ ⟨F.n - 1, hlast_lt⟩ = s.phiMinus C E hE := by
      simpa only [HNFiltration.phiMinus] using hminusF
    have heq' : F.φ ⟨0, hn⟩ = F.φ ⟨F.n - 1, hlast_lt⟩ :=
      htop.trans (heq.trans hbot.symm)
    exact (F.hφ (Fin.mk_lt_mk.mpr (by omega))).ne heq'.symm
  have hP := F.semistable_of_length_one C (fun ψ ↦ s.closedUnderIso ψ) hn_eq
  have hphase : F.φ ⟨0, hn⟩ = φ := by
    simpa only [HNFiltration.phiPlus] using hplusF.trans hplus
  convert hP using 1
  simpa [hn_eq] using hphase.symm

/-- If every factor of an owner HN filtration has the same phase, then the
ambient object lies in that semistable slice. -/
theorem Slicing.semistable_of_HN_all_eq (s : Slicing C) {E : C} {φ : ℝ}
    (F : HNFiltration C s.P E) (hall : ∀ i : Fin F.n, F.φ i = φ) :
    s.P φ E := by
  have hchain : ∀ k (hk : k ≤ F.n), s.P φ (F.chain.obj' k (by omega)) := by
    intro k hk
    induction k with
    | zero => exact s.zero_mem_of_isZero C φ _ F.base_isZero
    | succ k ih =>
        have hkn : k < F.n := by omega
        let T := F.triangle ⟨k, hkn⟩
        have h₁ : s.P φ T.obj₁ :=
          (s.P φ).prop_of_iso
            (Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)).symm (ih (by omega))
        have h₃ : s.P φ T.obj₃ := by
          rw [← hall ⟨k, hkn⟩]
          exact F.semistable ⟨k, hkn⟩
        have h₂ : s.P φ T.obj₂ :=
          s.semistable_of_triangle C φ h₁ h₃ (F.triangle_dist ⟨k, hkn⟩)
        exact (s.P φ).prop_of_iso
          (Classical.choice (F.triangle_obj₂ ⟨k, hkn⟩)) h₂
  exact (s.P φ).prop_of_iso (Classical.choice F.top_iso) (hchain F.n le_rfl)

end CategoryTheory.Triangulated
