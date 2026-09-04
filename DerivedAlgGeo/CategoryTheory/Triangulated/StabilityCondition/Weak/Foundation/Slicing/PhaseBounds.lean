/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.IntervalCategory

/-!
# Phase bounds attached to an owner slicing

This module defines the four phase-cut object properties used to construct the
t-structure associated to a slicing.  The definitions are intrinsic to the
repository-owned HN filtration API and have no retained-library dependency.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The highest phase in a nonempty HN filtration. -/
def HNFiltration.phiPlus {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) : ℝ :=
  F.φ ⟨0, h⟩

/-- The lowest phase in a nonempty HN filtration. -/
def HNFiltration.phiMinus {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) : ℝ :=
  F.φ ⟨F.n - 1, by lia⟩

/-- Every phase lies between the extremal phases. -/
theorem HNFiltration.phase_mem_range {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) (i : Fin F.n) :
    F.phiMinus C h ≤ F.φ i ∧ F.φ i ≤ F.phiPlus C h := by
  constructor
  · exact F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
  · exact F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))

/-- The lowest phase is no greater than the highest phase. -/
theorem HNFiltration.phiMinus_le_phiPlus {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (h : 0 < F.n) :
    F.phiMinus C h ≤ F.phiPlus C h :=
  (F.phase_mem_range C h ⟨0, h⟩).1

/-- Transport an owner HN filtration across an isomorphism of its target. -/
def HNFiltration.ofIso {P : ℝ → ObjectProperty C} {E E' : C}
    (F : HNFiltration C P E) (e : E ≅ E') : HNFiltration C P E' where
  toPostnikovTower :=
    { n := F.n
      chain := F.chain
      triangle := F.triangle
      triangle_dist := F.triangle_dist
      triangle_obj₁ := F.triangle_obj₁
      triangle_obj₂ := F.triangle_obj₂
      base_isZero := F.base_isZero
      top_iso := ⟨(Classical.choice F.top_iso).trans e⟩ }
  φ := F.φ
  hφ := F.hφ
  semistable := F.semistable

/-- Objects all of whose HN phases are at most `t`. -/
def Slicing.leProp (s : Slicing C) (t : ℝ) : ObjectProperty C :=
  fun E => IsZero E ∨ ∃ (F : HNFiltration C s.P E) (h : 0 < F.n),
    F.phiPlus C h ≤ t

/-- Objects all of whose HN phases are strictly greater than `t`. -/
def Slicing.gtProp (s : Slicing C) (t : ℝ) : ObjectProperty C :=
  fun E => IsZero E ∨ ∃ (F : HNFiltration C s.P E) (h : 0 < F.n),
    t < F.phiMinus C h

/-- Objects all of whose HN phases are strictly less than `t`. -/
def Slicing.ltProp (s : Slicing C) (t : ℝ) : ObjectProperty C :=
  fun E => IsZero E ∨ ∃ (F : HNFiltration C s.P E) (h : 0 < F.n),
    F.phiPlus C h < t

/-- Objects all of whose HN phases are at least `t`. -/
def Slicing.geProp (s : Slicing C) (t : ℝ) : ObjectProperty C :=
  fun E => IsZero E ∨ ∃ (F : HNFiltration C s.P E) (h : 0 < F.n),
    t ≤ F.phiMinus C h

instance Slicing.leProp_isClosedUnderIsomorphisms (s : Slicing C) (t : ℝ) :
    (s.leProp C t).IsClosedUnderIsomorphisms where
  of_iso e h := h.elim (fun hE => Or.inl (IsZero.of_iso hE e.symm))
    (fun ⟨F, hF, hle⟩ => Or.inr ⟨F.ofIso C e, hF, hle⟩)

instance Slicing.gtProp_isClosedUnderIsomorphisms (s : Slicing C) (t : ℝ) :
    (s.gtProp C t).IsClosedUnderIsomorphisms where
  of_iso e h := h.elim (fun hE => Or.inl (IsZero.of_iso hE e.symm))
    (fun ⟨F, hF, hgt⟩ => Or.inr ⟨F.ofIso C e, hF, hgt⟩)

instance Slicing.ltProp_isClosedUnderIsomorphisms (s : Slicing C) (t : ℝ) :
    (s.ltProp C t).IsClosedUnderIsomorphisms where
  of_iso e h := h.elim (fun hE => Or.inl (IsZero.of_iso hE e.symm))
    (fun ⟨F, hF, hlt⟩ => Or.inr ⟨F.ofIso C e, hF, hlt⟩)

instance Slicing.geProp_isClosedUnderIsomorphisms (s : Slicing C) (t : ℝ) :
    (s.geProp C t).IsClosedUnderIsomorphisms where
  of_iso e h := h.elim (fun hE => Or.inl (IsZero.of_iso hE e.symm))
    (fun ⟨F, hF, hge⟩ => Or.inr ⟨F.ofIso C e, hF, hge⟩)

theorem Slicing.leProp_of_isZero (s : Slicing C) {E : C} (hE : IsZero E) (t : ℝ) :
    s.leProp C t E := Or.inl hE

theorem Slicing.gtProp_of_isZero (s : Slicing C) {E : C} (hE : IsZero E) (t : ℝ) :
    s.gtProp C t E := Or.inl hE

theorem Slicing.ltProp_of_isZero (s : Slicing C) {E : C} (hE : IsZero E) (t : ℝ) :
    s.ltProp C t E := Or.inl hE

theorem Slicing.geProp_of_isZero (s : Slicing C) {E : C} (hE : IsZero E) (t : ℝ) :
    s.geProp C t E := Or.inl hE

/-- Upper phase cuts are monotone in their endpoint. -/
theorem Slicing.leProp_mono (s : Slicing C) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    s.leProp C t₁ ≤ s.leProp C t₂ := by
  rintro E (hE | ⟨F, hF, hle⟩)
  · exact Or.inl hE
  · exact Or.inr ⟨F, hF, hle.trans h⟩

/-- Strict lower phase cuts are antitone in their endpoint. -/
theorem Slicing.gtProp_anti (s : Slicing C) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    s.gtProp C t₂ ≤ s.gtProp C t₁ := by
  rintro E (hE | ⟨F, hF, hgt⟩)
  · exact Or.inl hE
  · exact Or.inr ⟨F, hF, h.trans_lt hgt⟩

/-- Strict upper phase cuts are monotone in their endpoint. -/
theorem Slicing.ltProp_mono (s : Slicing C) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    s.ltProp C t₁ ≤ s.ltProp C t₂ := by
  rintro E (hE | ⟨F, hF, hlt⟩)
  · exact Or.inl hE
  · exact Or.inr ⟨F, hF, hlt.trans_le h⟩

/-- Lower phase cuts are antitone in their endpoint. -/
theorem Slicing.geProp_anti (s : Slicing C) {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    s.geProp C t₂ ≤ s.geProp C t₁ := by
  rintro E (hE | ⟨F, hF, hge⟩)
  · exact Or.inl hE
  · exact Or.inr ⟨F, hF, h.trans hge⟩

theorem Slicing.leProp_of_ltProp (s : Slicing C) {t : ℝ} :
    s.ltProp C t ≤ s.leProp C t := by
  rintro E (hE | ⟨F, hF, hlt⟩)
  · exact Or.inl hE
  · exact Or.inr ⟨F, hF, hlt.le⟩

theorem Slicing.geProp_of_gtProp (s : Slicing C) {t : ℝ} :
    s.gtProp C t ≤ s.geProp C t := by
  rintro E (hE | ⟨F, hF, hgt⟩)
  · exact Or.inl hE
  · exact Or.inr ⟨F, hF, hgt.le⟩

/-- Membership in an open phase interval implies the corresponding strict
upper bound. -/
theorem Slicing.ltProp_of_intervalProp (s : Slicing C) {a b : ℝ} {E : C}
    (hE : s.intervalProp C a b E) : s.ltProp C b E := by
  rcases hE with hE | ⟨F, hF⟩
  · exact Or.inl hE
  · by_cases hn : 0 < F.n
    · exact Or.inr ⟨F, hn, (hF ⟨0, hn⟩).2⟩
    · exact Or.inl (F.isZero_of_length_zero (by lia))

/-- Membership in an open phase interval implies the corresponding strict
lower bound. -/
theorem Slicing.gtProp_of_intervalProp (s : Slicing C) {a b : ℝ} {E : C}
    (hE : s.intervalProp C a b E) : s.gtProp C a E := by
  rcases hE with hE | ⟨F, hF⟩
  · exact Or.inl hE
  · by_cases hn : 0 < F.n
    · exact Or.inr ⟨F, hn, (hF ⟨F.n - 1, by lia⟩).1⟩
    · exact Or.inl (F.isZero_of_length_zero (by lia))

/-! ### Hom-vanishing across phase cuts -/

private theorem chain_hom_eq_zero_of_gt (s : Slicing C) {A E : C} {ψ : ℝ}
    (hA : s.P ψ A) (F : HNFiltration C s.P E) (hlt : ∀ i, F.φ i < ψ) :
    ∀ (k : ℕ) (hk : k < F.n + 1) (f : A ⟶ F.chain.obj ⟨k, hk⟩), f = 0 := by
  intro k
  induction k with
  | zero =>
      intro _ f
      exact F.base_isZero.eq_of_tgt f 0
  | succ k ih =>
      intro hk f
      have hkn : k < F.n := by lia
      let T := F.triangle ⟨k, hkn⟩
      let e₁ := Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)
      let e₂ := Classical.choice (F.triangle_obj₂ ⟨k, hkn⟩)
      have hcomp : (f ≫ e₂.inv) ≫ T.mor₂ = 0 :=
        s.hom_vanishing ψ (F.φ ⟨k, hkn⟩) A T.obj₃
          (hlt ⟨k, hkn⟩) hA (F.semistable ⟨k, hkn⟩) _
      obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T
        (F.triangle_dist ⟨k, hkn⟩) (f ≫ e₂.inv) hcomp
      have hg0 : g ≫ e₁.hom = 0 := ih (by lia) (g ≫ e₁.hom)
      have hg_eq : g = 0 := by
        rw [← cancel_mono e₁.hom]
        simpa using hg0
      have hfe : f ≫ e₂.inv = 0 := by rw [hg, hg_eq, zero_comp]
      rw [← cancel_mono e₂.inv]
      simpa using hfe

private theorem hom_eq_zero_of_gt_phases (s : Slicing C) {A E : C} {ψ : ℝ}
    (hA : s.P ψ A) (F : HNFiltration C s.P E) (hlt : ∀ i, F.φ i < ψ)
    (f : A ⟶ E) : f = 0 := by
  let eE := Classical.choice F.top_iso
  have h : f ≫ eE.inv = 0 :=
    chain_hom_eq_zero_of_gt C s hA F hlt F.n (by lia) _
  rw [← cancel_mono eE.inv]
  simpa using h

private theorem chain_hom_eq_zero_gap (s : Slicing C) {X Y : C}
    (FX : HNFiltration C s.P X) (FY : HNFiltration C s.P Y)
    (hgap : ∀ i j, FY.φ j < FX.φ i) :
    ∀ (k : ℕ) (hk : k < FX.n + 1) (f : FX.chain.obj ⟨k, hk⟩ ⟶ Y), f = 0 := by
  intro k
  induction k with
  | zero =>
      intro _ f
      exact FX.base_isZero.eq_of_src f 0
  | succ k ih =>
      intro hk f
      have hkn : k < FX.n := by lia
      let T := FX.triangle ⟨k, hkn⟩
      let e₁ := Classical.choice (FX.triangle_obj₁ ⟨k, hkn⟩)
      let e₂ := Classical.choice (FX.triangle_obj₂ ⟨k, hkn⟩)
      have hmor₁ : T.mor₁ ≫ (e₂.hom ≫ f) = 0 := by
        have h : e₁.inv ≫ (T.mor₁ ≫ (e₂.hom ≫ f)) = 0 := by
          simp only [← Category.assoc]
          exact ih (by lia) _
        rw [← cancel_epi e₁.inv]
        simpa using h
      obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T
        (FX.triangle_dist ⟨k, hkn⟩) (e₂.hom ≫ f) hmor₁
      have hg_eq : g = 0 :=
        hom_eq_zero_of_gt_phases C s (FX.semistable ⟨k, hkn⟩) FY
          (fun j => hgap ⟨k, hkn⟩ j) g
      have hef : e₂.hom ≫ f = 0 := by rw [hg, hg_eq, comp_zero]
      rw [← cancel_epi e₂.hom]
      simpa using hef

/-- Morphisms between HN-filtered objects separated by a strict phase gap
vanish. -/
theorem Slicing.hom_eq_zero_of_phase_gap (s : Slicing C) {X Y : C}
    (FX : HNFiltration C s.P X) (FY : HNFiltration C s.P Y)
    (hgap : ∀ i j, FY.φ j < FX.φ i) (f : X ⟶ Y) : f = 0 := by
  let eX := Classical.choice FX.top_iso
  have h : eX.hom ≫ f = 0 :=
    chain_hom_eq_zero_gap C s FX FY hgap FX.n (by lia) _
  rw [← cancel_epi eX.hom]
  simpa using h

/-- Morphisms from an open interval strictly above another open interval
vanish. -/
theorem Slicing.intervalHom_eq_zero (s : Slicing C) {A B : C}
    {a₁ b₁ a₂ b₂ : ℝ} (hA : s.intervalProp C a₁ b₁ A)
    (hB : s.intervalProp C a₂ b₂ B) (hgap : b₂ ≤ a₁)
    (f : A ⟶ B) : f = 0 := by
  rcases hA with hAZ | ⟨FA, hFA⟩
  · exact hAZ.eq_of_src f 0
  rcases hB with hBZ | ⟨FB, hFB⟩
  · exact hBZ.eq_of_tgt f 0
  exact s.hom_eq_zero_of_phase_gap C FA FB
    (fun i j => ((hFB j).2.trans_le hgap).trans (hFA i).1) f

/-- The hom-vanishing statement for the `(> 0, ≤ 0)` phase cut. -/
theorem Slicing.zero_of_gtProp_leProp (s : Slicing C) {X Y : C}
    (hX : s.gtProp C 0 X) (hY : s.leProp C 0 Y) (f : X ⟶ Y) : f = 0 := by
  rcases hX with hX | ⟨FX, hFX, hFXgt⟩
  · exact hX.eq_of_src f 0
  rcases hY with hY | ⟨FY, hFY, hFYle⟩
  · exact hY.eq_of_tgt f 0
  exact s.hom_eq_zero_of_phase_gap C FX FY
    (fun i j => lt_of_le_of_lt
      ((FY.phase_mem_range C hFY j).2.trans hFYle)
      (hFXgt.trans_le (FX.phase_mem_range C hFX i).1)) f

/-- The hom-vanishing statement for the `(≥ 0, < 0)` phase cut. -/
theorem Slicing.zero_of_geProp_ltProp (s : Slicing C) {X Y : C}
    (hX : s.geProp C 0 X) (hY : s.ltProp C 0 Y) (f : X ⟶ Y) : f = 0 := by
  rcases hX with hX | ⟨FX, hFX, hFXge⟩
  · exact hX.eq_of_src f 0
  rcases hY with hY | ⟨FY, hFY, hFYlt⟩
  · exact hY.eq_of_tgt f 0
  exact s.hom_eq_zero_of_phase_gap C FX FY
    (fun i j => lt_of_le_of_lt
      (FY.phase_mem_range C hFY j).2
      (hFYlt.trans_le (hFXge.trans (FX.phase_mem_range C hFX i).1))) f

/-- The hom-vanishing statement for an arbitrary `(≥ t, < t)` phase cut. -/
theorem Slicing.zero_of_geProp_ltProp_at (s : Slicing C) (t : ℝ) {X Y : C}
    (hX : s.geProp C t X) (hY : s.ltProp C t Y) (f : X ⟶ Y) : f = 0 := by
  rcases hX with hX | ⟨FX, hFX, hFXge⟩
  · exact hX.eq_of_src f 0
  rcases hY with hY | ⟨FY, hFY, hFYlt⟩
  · exact hY.eq_of_tgt f 0
  exact s.hom_eq_zero_of_phase_gap C FX FY
    (fun i j => lt_of_le_of_lt
      (FY.phase_mem_range C hFY j).2
      (hFYlt.trans_le (hFXge.trans (FX.phase_mem_range C hFX i).1))) f

end CategoryTheory.Triangulated
