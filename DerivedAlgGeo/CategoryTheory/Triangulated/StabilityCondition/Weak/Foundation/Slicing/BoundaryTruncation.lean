/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.CutoffTruncation

/-!
# Half-open boundary truncations for owner slicings

This module supplies the dual half-open truncation convention and packages
both cutoff conventions as boundary triangles.  These triangles are the
geometric input for transporting skewed semistability between thin interval
presentations.
-/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Split an owner HN filtration into phases greater than or equal to zero
and phases strictly below zero.  This is the dual half-open convention to
`Slicing.exists_phase_truncation`. -/
theorem Slicing.exists_dual_phase_truncation (s : Slicing C) (A : C)
    (F : HNFiltration C s.P A) :
    ∃ (X Y : C) (_ : s.geProp C 0 X) (_ : s.ltProp C 0 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  suffices main : ∀ (m : ℕ) (A : C) (F : HNFiltration C s.P A), F.n ≤ m →
      ∃ (X Y : C) (_ : s.geProp C 0 X) (_ : s.ltProp C 0 Y)
        (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C by
    exact main F.n A F le_rfl
  intro m
  induction m with
  | zero =>
      intro A F hF
      have hn : F.n = 0 := by omega
      exact ⟨A, (0 : C), Or.inl (F.isZero_of_length_zero hn), Or.inl (isZero_zero C),
        𝟙 A, 0, 0, contractible_distinguished A⟩
  | succ m ih =>
      intro A F hF
      by_cases hn : F.n = 0
      · exact ⟨A, (0 : C), Or.inl (F.isZero_of_length_zero hn), Or.inl (isZero_zero C),
          𝟙 A, 0, 0, contractible_distinguished A⟩
      have hn₀ : 0 < F.n := Nat.pos_of_ne_zero hn
      by_cases hnonneg : ∀ i : Fin F.n, 0 ≤ F.φ i
      · exact ⟨A, (0 : C), s.geProp_of_hn C F 0 hnonneg hn₀,
          Or.inl (isZero_zero C), 𝟙 A, 0, 0, contractible_distinguished A⟩
      · push Not at hnonneg
        by_cases hneg : ∀ i : Fin F.n, F.φ i < 0
        · exact ⟨(0 : C), A, Or.inl (isZero_zero C),
            s.ltProp_of_hn C F 0 hneg hn₀, 0, 𝟙 A, 0,
            contractible_distinguished₁ A⟩
        · push Not at hneg
          have hn₂ : 2 ≤ F.n := by
            by_contra h
            obtain ⟨i, hi⟩ := hnonneg
            obtain ⟨j, hj⟩ := hneg
            have hij : i = j := Fin.ext (by omega)
            subst j
            linarith
          let G := F.prefix C (F.n - 1) (by omega)
          obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ :=
            ih (F.chain.obj' (F.n - 1) (by omega)) G
              (by change F.n - 1 ≤ m; omega)
          let T := F.triangle ⟨F.n - 1, by omega⟩
          let e₁ := Classical.choice (F.triangle_obj₁ ⟨F.n - 1, by omega⟩)
          let e₂ := Classical.choice (F.triangle_obj₂ ⟨F.n - 1, by omega⟩)
          let eA := Classical.choice F.top_iso
          have hchain : F.chain.obj' (F.n - 1 + 1) (by omega) =
              F.chain.obj (Fin.last F.n) :=
            congrArg F.chain.obj (Fin.ext (by simp [Fin.val_last]; omega))
          let e₂A : T.obj₂ ≅ A := e₂.trans ((eqToIso hchain).trans eA)
          let u : F.chain.obj' (F.n - 1) (by omega) ⟶ A :=
            e₁.inv ≫ T.mor₁ ≫ e₂A.hom
          have hTu : Triangle.mk u (e₂A.inv ≫ T.mor₂)
              (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') ∈ distTriang C := by
            apply isomorphic_distinguished _ (F.triangle_dist ⟨F.n - 1, by omega⟩)
            exact Triangle.isoMk _ T e₁.symm e₂A.symm (Iso.refl _)
              (by simp [u, e₂A]) (by simp [e₂A]) (by simp)
          obtain ⟨i, hi⟩ := hnonneg
          have hlast : F.φ ⟨F.n - 1, by omega⟩ < 0 :=
            lt_of_le_of_lt
              (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))) hi
          obtain ⟨Z, p, q, hXZ⟩ := distinguished_cocone_triangle (f ≫ u)
          let oct := CategoryTheory.Triangulated.someOctahedron rfl hT hTu hXZ
          have hfactor : s.ltProp C 0 T.obj₃ := by
            apply s.ltProp_of_hn C
              (HNFiltration.single C T.obj₃ (F.φ ⟨F.n - 1, by omega⟩)
                (F.semistable ⟨F.n - 1, by omega⟩)) 0
            · intro j
              simpa [HNFiltration.single] using hlast
            · change 0 < 1
              omega
          have hZ : s.ltProp C 0 Z := s.ltProp_of_triangle C 0 hY hfactor oct.mem
          exact ⟨X, Z, hX, hZ, f ≫ u, p, q, hXZ⟩

/-- Truncate an object at an upper endpoint, leaving the boundary phase in
the first term. -/
theorem Slicing.exists_upper_boundary_triangle (s : Slicing C)
    {a b₁ b₂ : ℝ} (hab₁ : a < b₁) {E : C}
    (hE : s.intervalProp C a b₂ E) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
        s.geProp C b₁ X ∧ s.intervalProp C a b₁ Y := by
  obtain ⟨F⟩ := s.hn_exists E
  obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ :=
    (s.phaseShift C b₁).exists_dual_phase_truncation C E (F.phaseShift C b₁)
  have hXge : s.geProp C b₁ X := (s.phaseShift_geProp_zero C b₁ X).mp hX
  have hYlt : s.ltProp C b₁ Y := (s.phaseShift_ltProp_zero C b₁ Y).mp hY
  by_cases hYne : IsZero Y
  · exact ⟨X, Y, f, g, h, hT, hXge, Or.inl hYne⟩
  have hXgt : s.gtProp C a X := by
    rcases hXge with hzero | ⟨G, hG, hge⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨G, hG, hab₁.trans_le hge⟩
  have hYlo : a < s.phiMinus C Y hYne :=
    s.phiMinus_gt_of_triangle_with_gtProp C hYne
      (fun hEne => s.phiMinus_gt_of_intervalProp C hEne hE)
      hXgt (by linarith) hT
  have hYhi : s.phiPlus C Y hYne < b₁ := s.phiPlus_lt_of_ltProp C hYne hYlt
  exact ⟨X, Y, f, g, h, hT, hXge,
    s.intervalProp_of_intrinsic_phases C hYne hYlo hYhi⟩

/-- Truncate an object at a lower endpoint, leaving the boundary phase in
the third term. -/
theorem Slicing.exists_lower_boundary_triangle (s : Slicing C)
    {a₁ a₂ b : ℝ} (ha₁ : a₁ < b) {E : C}
    (hE : s.intervalProp C a₂ b E) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
        s.intervalProp C a₁ b X ∧ s.leProp C a₁ Y := by
  obtain ⟨F⟩ := s.hn_exists E
  obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := s.exists_cutoff_truncation C F a₁
  by_cases hXne : IsZero X
  · exact ⟨X, Y, f, g, h, hT, Or.inl hXne, hY⟩
  have hXlo : a₁ < s.phiMinus C X hXne := s.phiMinus_gt_of_gtProp C hXne hX
  have hXhi : s.phiPlus C X hXne < b :=
    s.phiPlus_lt_of_triangle_with_leProp C hXne
      (fun hEne => s.phiPlus_lt_of_intervalProp C hEne hE)
      hY (by linarith) hT
  exact ⟨X, Y, f, g, h, hT,
    s.intervalProp_of_intrinsic_phases C hXne hXlo hXhi, hY⟩

omit [IsTriangulated C] in
/-- The first term of an upper-boundary triangle remains in the original
thin interval. -/
theorem Slicing.intervalProp_of_upper_boundary_triangle (s : Slicing C)
    {a b₁ b₂ : ℝ} (hab₁ : a < b₁) (hab₂ : a < b₂)
    (hb₁ : b₁ ≤ a + 1) {E X Y : C}
    (hE : s.intervalProp C a b₂ E) (hX : s.geProp C b₁ X)
    (hY : s.intervalProp C a b₁ Y)
    {f : X ⟶ E} {g : E ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a b₂ X := by
  have hYle : s.leProp C (a + 1) Y :=
    s.leProp_mono C hb₁ Y
      (s.leProp_of_ltProp C Y (s.ltProp_of_intervalProp C hY))
  have hXgt : s.gtProp C a X := by
    rcases hX with hzero | ⟨F, hF, hge⟩
    · exact Or.inl hzero
    · exact Or.inr ⟨F, hF, hab₁.trans_le hge⟩
  exact s.first_intervalProp_of_triangle C hab₂ hE hYle hXgt hT

omit [IsTriangulated C] in
/-- The third term of a lower-boundary triangle remains in the original
thin interval. -/
theorem Slicing.intervalProp_of_lower_boundary_triangle (s : Slicing C)
    {a₁ a₂ b : ℝ} (ha₁ : a₁ < b) (ha : a₂ ≤ a₁)
    {E X Y : C} (hE : s.intervalProp C a₂ b E)
    (hX : s.intervalProp C a₁ b X) (hY : s.leProp C a₁ Y)
    {f : X ⟶ E} {g : E ⟶ Y} {h : Y ⟶ X⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g h ∈ distTriang C) :
    s.intervalProp C a₂ b Y := by
  by_cases hYne : IsZero Y
  · exact Or.inl hYne
  have hYhi : s.phiPlus C Y hYne < b :=
    (s.phiPlus_le_of_leProp C hYne hY).trans_lt ha₁
  have hYlo : a₂ < s.phiMinus C Y hYne :=
    s.phiMinus_gt_of_triangle_with_gtProp C hYne
      (fun hEne => s.phiMinus_gt_of_intervalProp C hEne hE)
      (s.gtProp_of_intervalProp C hX) (by linarith) hT
  exact s.intervalProp_of_intrinsic_phases C hYne hYlo hYhi

end CategoryTheory.Triangulated
