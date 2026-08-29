/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.FiltrationOperations

/-!
# Boundary factors of owner HN filtrations

This module removes zero factors at either end of a repository-owned
Harder--Narasimhan filtration.  Consequently every nonzero object admits an
HN filtration whose highest and lowest factors are nonzero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- An HN filtration of a nonzero object contains at least one factor. -/
theorem HNFiltration.n_pos {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hE : ¬IsZero E) : 0 < F.n := by
  by_contra hn
  push Not at hn
  exact hE (F.isZero_of_length_zero (by omega))

/-- Some factor of an HN filtration of a nonzero object is nonzero. -/
theorem HNFiltration.exists_nonzero_factor {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hE : ¬IsZero E) :
    ∃ i : Fin F.n, ¬IsZero (F.factor i) := by
  by_contra h
  push Not at h
  suffices hchain : ∀ k (hk : k < F.n + 1), IsZero (F.chain.obj ⟨k, hk⟩) by
    exact hE (IsZero.of_iso (hchain F.n (by omega)) (Classical.choice F.top_iso).symm)
  intro k hk
  induction k with
  | zero => exact F.base_isZero
  | succ k ih =>
      have hkn : k < F.n := by omega
      let T := F.triangle ⟨k, hkn⟩
      let e₁ := Classical.choice (F.triangle_obj₁ ⟨k, hkn⟩)
      let e₂ := Classical.choice (F.triangle_obj₂ ⟨k, hkn⟩)
      have hT₃ : IsZero T.obj₃ := h ⟨k, hkn⟩
      have hmor : IsIso T.mor₁ :=
        (Triangle.isZero₃_iff_isIso₁ T (F.triangle_dist ⟨k, hkn⟩)).mp hT₃
      have hT₁ : IsZero T.obj₁ := (ih (by omega)).of_iso e₁
      have hT₂ : IsZero T.obj₂ := hT₁.of_iso (asIso T.mor₁).symm
      exact hT₂.of_iso e₂.symm

/-- Remove a zero first factor from an HN filtration. -/
def HNFiltration.dropFirst {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hn : 1 < F.n)
    (hzero : IsZero (F.factor ⟨0, by omega⟩)) : HNFiltration C P E := by
  let T := F.triangle ⟨0, by omega⟩
  have hmor : IsIso T.mor₁ :=
    (Triangle.isZero₃_iff_isIso₁ T (F.triangle_dist ⟨0, by omega⟩)).mp hzero
  have hchain₁ : IsZero (F.chain.obj ⟨1, by omega⟩) :=
    (F.base_isZero.of_iso (Classical.choice (F.triangle_obj₁ ⟨0, by omega⟩))).of_iso
      (asIso T.mor₁).symm |>.of_iso
        (Classical.choice (F.triangle_obj₂ ⟨0, by omega⟩)).symm
  exact
    { n := F.n - 1
      chain := ComposableArrows.mkOfObjOfMapSucc
        (fun i : Fin (F.n - 1 + 1) => F.chain.obj ⟨i.val + 1, by omega⟩)
        (fun i : Fin (F.n - 1) =>
          F.chain.map' (i.val + 1) (i.val + 2) (by omega) (by omega))
      triangle := fun i => F.triangle ⟨i.val + 1, by omega⟩
      triangle_dist := fun i => F.triangle_dist ⟨i.val + 1, by omega⟩
      triangle_obj₁ := fun i => by
        refine ⟨(Classical.choice (F.triangle_obj₁ ⟨i.val + 1, by omega⟩)).trans
          (eqToIso ?_)⟩
        simp [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj]
      triangle_obj₂ := fun i => by
        refine ⟨(Classical.choice (F.triangle_obj₂ ⟨i.val + 1, by omega⟩)).trans
          (eqToIso ?_)⟩
        simp [ComposableArrows.obj', ComposableArrows.mkOfObjOfMapSucc_obj]
      base_isZero := by
        change IsZero ((ComposableArrows.mkOfObjOfMapSucc _ _).obj ⟨0, _⟩)
        simpa [ComposableArrows.mkOfObjOfMapSucc_obj] using hchain₁
      top_iso := ⟨by
        change (ComposableArrows.mkOfObjOfMapSucc _ _).obj ⟨F.n - 1, _⟩ ≅ E
        simp only [ComposableArrows.mkOfObjOfMapSucc_obj]
        exact (eqToIso (by
          apply congrArg F.chain.obj
          ext
          simp only
          omega)).trans (Classical.choice F.top_iso)⟩
      φ := fun i => F.φ ⟨i.val + 1, by omega⟩
      hφ := by
        intro i j hij
        apply F.hφ
        exact Fin.mk_lt_mk.mpr (by omega)
      semistable := fun i => F.semistable ⟨i.val + 1, by omega⟩ }

/-- A nonzero object admits an HN filtration with nonzero highest factor. -/
theorem Slicing.exists_hn_nonzero_first (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.factor ⟨0, hn⟩) := by
  obtain ⟨F⟩ := s.hn_exists E
  suffices hmain : ∀ m (G : HNFiltration C s.P E), G.n ≤ m →
      ∃ (H : HNFiltration C s.P E) (hn : 0 < H.n),
        ¬IsZero (H.factor ⟨0, hn⟩) from hmain F.n F le_rfl
  intro m
  induction m with
  | zero =>
      intro G hG
      exact absurd (G.isZero_of_length_zero (by omega)) hE
  | succ m ih =>
      intro G hG
      have hn : 0 < G.n := G.n_pos C hE
      by_cases hfirst : IsZero (G.factor ⟨0, hn⟩)
      · have htwo : 1 < G.n := by
          by_contra h
          push Not at h
          obtain ⟨i, hi⟩ := G.exists_nonzero_factor C hE
          have : i = ⟨0, hn⟩ := Fin.ext (by omega)
          subst i
          exact hi hfirst
        apply ih (G.dropFirst C htwo hfirst)
        change G.n - 1 ≤ m
        omega
      · exact ⟨G, hn, hfirst⟩

/-- Remove a zero last factor from an HN filtration. -/
def HNFiltration.dropLast {P : ℝ → ObjectProperty C} {E : C}
    (F : HNFiltration C P E) (hn : 1 < F.n)
    (hzero : IsZero (F.factor ⟨F.n - 1, by omega⟩)) : HNFiltration C P E := by
  let T := F.triangle ⟨F.n - 1, by omega⟩
  have hmor : IsIso T.mor₁ :=
    (Triangle.isZero₃_iff_isIso₁ T (F.triangle_dist ⟨F.n - 1, by omega⟩)).mp hzero
  let e₁ := Classical.choice (F.triangle_obj₁ ⟨F.n - 1, by omega⟩)
  let e₂ := Classical.choice (F.triangle_obj₂ ⟨F.n - 1, by omega⟩)
  let G := F.prefix C (F.n - 1) (by omega)
  exact
    { n := F.n - 1
      chain := G.chain
      triangle := G.triangle
      triangle_dist := G.triangle_dist
      triangle_obj₁ := G.triangle_obj₁
      triangle_obj₂ := G.triangle_obj₂
      base_isZero := G.base_isZero
      top_iso := ⟨(Classical.choice G.top_iso).trans
        (e₁.symm.trans ((asIso T.mor₁).trans
          (e₂.trans ((eqToIso (by
            simp only [ComposableArrows.obj']
            apply congrArg F.chain.obj
            ext
            simp only
            omega)).trans (Classical.choice F.top_iso)))))⟩
      φ := G.φ
      hφ := G.hφ
      semistable := G.semistable }

/-- A nonzero object admits an HN filtration with nonzero lowest factor. -/
theorem Slicing.exists_hn_nonzero_last (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.factor ⟨F.n - 1, by omega⟩) := by
  obtain ⟨F⟩ := s.hn_exists E
  suffices hmain : ∀ m (G : HNFiltration C s.P E), G.n ≤ m →
      ∃ (H : HNFiltration C s.P E) (hn : 0 < H.n),
        ¬IsZero (H.factor ⟨H.n - 1, by omega⟩) from hmain F.n F le_rfl
  intro m
  induction m with
  | zero =>
      intro G hG
      exact absurd (G.isZero_of_length_zero (by omega)) hE
  | succ m ih =>
      intro G hG
      have hn : 0 < G.n := G.n_pos C hE
      by_cases hlast : IsZero (G.factor ⟨G.n - 1, by omega⟩)
      · have htwo : 1 < G.n := by
          by_contra h
          push Not at h
          obtain ⟨i, hi⟩ := G.exists_nonzero_factor C hE
          have : i = ⟨G.n - 1, by omega⟩ := Fin.ext (by omega)
          subst i
          exact hi hlast
        apply ih (G.dropLast C htwo hlast)
        change G.n - 1 ≤ m
        omega
      · exact ⟨G, hn, hlast⟩

/-- A nonzero object admits one HN filtration with both boundary factors nonzero. -/
theorem Slicing.exists_hn_nonzero_boundaries (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      ¬IsZero (F.factor ⟨0, hn⟩) ∧
        ¬IsZero (F.factor ⟨F.n - 1, by omega⟩) := by
  obtain ⟨F, hF, hfirst⟩ := s.exists_hn_nonzero_first C hE
  suffices hmain : ∀ m (G : HNFiltration C s.P E), G.n ≤ m →
      ∀ (hn : 0 < G.n), ¬IsZero (G.factor ⟨0, hn⟩) →
        ∃ (H : HNFiltration C s.P E) (hH : 0 < H.n),
          ¬IsZero (H.factor ⟨0, hH⟩) ∧
            ¬IsZero (H.factor ⟨H.n - 1, by omega⟩) from
    hmain F.n F le_rfl hF hfirst
  intro m
  induction m with
  | zero =>
      intro G hG hn
      omega
  | succ m ih =>
      intro G hG hn hGfirst
      by_cases hlast : IsZero (G.factor ⟨G.n - 1, by omega⟩)
      · have htwo : 1 < G.n := by
          by_contra h
          push Not at h
          have hi : (⟨0, hn⟩ : Fin G.n) = ⟨G.n - 1, by omega⟩ := Fin.ext (by omega)
          rw [hi] at hGfirst
          exact hGfirst hlast
        apply ih (G.dropLast C htwo hlast) (by change G.n - 1 ≤ m; omega)
          (by change 0 < G.n - 1; omega)
        exact hGfirst
      · exact ⟨G, hn, hGfirst, hlast⟩

end CategoryTheory.Triangulated
