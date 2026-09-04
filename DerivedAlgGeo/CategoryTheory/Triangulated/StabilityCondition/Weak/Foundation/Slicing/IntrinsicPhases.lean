/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.BoundaryFactors

/-!
# Intrinsic phases of owner slicings

The extremal phases of a nonzero object are independent of the HN filtration
used to compute them.  This module establishes that uniqueness and defines the
repository-owned intrinsic highest and lowest phases.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If every map from the first factor to the filtered object vanishes, then
every map from that factor to every stage of the filtration vanishes. -/
theorem HNFiltration.firstFactor_hom_chain_eq_zero (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n)
    (hzero : ∀ f : F.factor ⟨0, hn⟩ ⟶ E, f = 0) :
    ∀ k (hk : k < F.n + 1) (f : F.factor ⟨0, hn⟩ ⟶ F.chain.obj ⟨k, hk⟩),
      f = 0 := by
  suffices hmain : ∀ m, m ≤ F.n → ∀ k (hk : k < F.n + 1), F.n - m ≤ k →
      ∀ f : F.factor ⟨0, hn⟩ ⟶ F.chain.obj ⟨k, hk⟩, f = 0 by
    intro k hk f
    exact hmain F.n le_rfl k hk (by omega) f
  intro m
  induction m with
  | zero =>
      intro hm k hk hkn f
      have hk_eq : k = F.n := by omega
      subst k
      let e := Classical.choice F.top_iso
      have hfe : f ≫ e.hom = 0 := hzero _
      calc
        f = (f ≫ e.hom) ≫ e.inv := by simp
        _ = 0 := by rw [hfe, zero_comp]
  | succ m ih =>
      intro hm k hk hkn f
      by_cases hk_eq : k = F.n - (m + 1)
      · have hkF : k < F.n := by omega
        let T := F.triangle ⟨k, hkF⟩
        let e₁ := Classical.choice (F.triangle_obj₁ ⟨k, hkF⟩)
        let e₂ := Classical.choice (F.triangle_obj₂ ⟨k, hkF⟩)
        have hstep : (f ≫ e₁.inv) ≫ T.mor₁ = 0 := by
          have hnext : (f ≫ e₁.inv ≫ T.mor₁) ≫ e₂.hom = 0 := by
            rw [Category.assoc, Category.assoc]
            exact ih (by omega) (k + 1) (by omega) (by omega) _
          rw [Category.assoc]
          simpa only [Preadditive.IsIso.comp_right_eq_zero] using hnext
        obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T.invRotate
          (inv_rot_of_distTriang _ (F.triangle_dist ⟨k, hkF⟩)) (f ≫ e₁.inv) hstep
        have hg_zero : g = 0 := by
          have hsource : s.P (F.φ ⟨0, hn⟩) (F.factor ⟨0, hn⟩) :=
            F.semistable ⟨0, hn⟩
          have htarget : s.P (F.φ ⟨k, hkF⟩ - 1) T.invRotate.obj₁ := by
            have hk_semistable := F.semistable ⟨k, hkF⟩
            change s.P (F.φ ⟨k, hkF⟩) T.obj₃ at hk_semistable
            rw [show F.φ ⟨k, hkF⟩ - 1 =
              F.φ ⟨k, hkF⟩ + ((-1 : ℤ) : ℝ) by push_cast; ring]
            exact (s.shift_int C (F.φ ⟨k, hkF⟩) T.obj₃ (-1)).mp hk_semistable
          exact s.hom_vanishing (F.φ ⟨0, hn⟩) (F.φ ⟨k, hkF⟩ - 1)
            (F.factor ⟨0, hn⟩) T.invRotate.obj₁ (by
              have hphase := F.hφ.antitone
                (show (⟨0, hn⟩ : Fin F.n) ≤ ⟨k, hkF⟩ from Fin.mk_le_mk.mpr (by omega))
              linarith) hsource htarget g
        have hcomp : f ≫ e₁.inv = 0 := by
          calc
            f ≫ e₁.inv = g ≫ T.invRotate.mor₁ := hg
            _ = 0 := by rw [hg_zero, zero_comp]
        calc
          f = (f ≫ e₁.inv) ≫ e₁.hom := by simp
          _ = 0 := by rw [hcomp, zero_comp]
      · exact ih (by omega) k hk (by omega) f

/-- A first factor is zero when all of its maps to the filtered object vanish. -/
theorem HNFiltration.firstFactor_isZero_of_hom_eq_zero (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n)
    (hzero : ∀ f : F.factor ⟨0, hn⟩ ⟶ E, f = 0) : IsZero (F.factor ⟨0, hn⟩) := by
  rw [IsZero.iff_id_eq_zero]
  let T := F.triangle ⟨0, hn⟩
  let e₂ := Classical.choice (F.triangle_obj₂ ⟨0, hn⟩)
  have hmor₂ : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist ⟨0, hn⟩)).mp
      (F.base_isZero.of_iso (Classical.choice (F.triangle_obj₁ ⟨0, hn⟩)))
  have hmap : inv T.mor₂ ≫ e₂.hom = 0 :=
    F.firstFactor_hom_chain_eq_zero C s hn hzero 1 (by omega) _
  have hinv : inv T.mor₂ = 0 := by
    calc
      inv T.mor₂ = (inv T.mor₂ ≫ e₂.hom) ≫ e₂.inv := by simp
      _ = 0 := by rw [hmap, zero_comp]
  calc
    𝟙 _ = inv T.mor₂ ≫ T.mor₂ := by rw [IsIso.inv_hom_id]
    _ = 0 := by rw [hinv, zero_comp]

/-- The nonzero first factor of one HN filtration cannot have higher phase
than the first factor of another filtration of the same object. -/
theorem HNFiltration.phiPlus_le_of_firstFactor_nonzero (s : Slicing C) {E : C}
    (F G : HNFiltration C s.P E) (hF : 0 < F.n) (hG : 0 < G.n)
    (hne : ¬IsZero (F.factor ⟨0, hF⟩)) : F.phiPlus C hF ≤ G.phiPlus C hG := by
  by_contra h
  push Not at h
  have hgap : ∀ j : Fin G.n, G.φ j < F.φ ⟨0, hF⟩ := fun j =>
    lt_of_le_of_lt (G.hφ.antitone
      (show (⟨0, hG⟩ : Fin G.n) ≤ j from Fin.mk_le_mk.mpr (Nat.zero_le j.val))) (by
      change G.phiPlus C hG < F.phiPlus C hF
      exact h)
  let source := HNFiltration.single C (F.factor ⟨0, hF⟩) (F.φ ⟨0, hF⟩)
    (F.semistable ⟨0, hF⟩)
  have hzero : ∀ f : F.factor ⟨0, hF⟩ ⟶ E, f = 0 := fun f =>
    s.hom_eq_zero_of_phase_gap C source G
      (fun _ j => by simpa [source, HNFiltration.single] using hgap j) f
  exact hne (F.firstFactor_isZero_of_hom_eq_zero C s hF hzero)

/-- Nonzero first factors of two HN filtrations have the same phase. -/
theorem HNFiltration.phiPlus_eq_of_firstFactors_nonzero (s : Slicing C) {E : C}
    (F G : HNFiltration C s.P E) (hF : 0 < F.n) (hG : 0 < G.n)
    (hneF : ¬IsZero (F.factor ⟨0, hF⟩)) (hneG : ¬IsZero (G.factor ⟨0, hG⟩)) :
    F.phiPlus C hF = G.phiPlus C hG :=
  le_antisymm (F.phiPlus_le_of_firstFactor_nonzero C s G hF hG hneF)
    (G.phiPlus_le_of_firstFactor_nonzero C s F hG hF hneG)

/-- A last factor is zero when every map from the filtered object to it vanishes. -/
theorem HNFiltration.lastFactor_isZero_of_hom_eq_zero (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n)
    (hzero : ∀ f : E ⟶ F.factor ⟨F.n - 1, by omega⟩, f = 0) :
    IsZero (F.factor ⟨F.n - 1, by omega⟩) := by
  rw [IsZero.iff_id_eq_zero]
  let i : Fin F.n := ⟨F.n - 1, by omega⟩
  let T := F.triangle i
  let e₂ := Classical.choice (F.triangle_obj₂ i)
  let eE := Classical.choice F.top_iso
  have hright : F.chain.obj' (F.n - 1 + 1) (by omega) = F.chain.right := by
    simp only [ComposableArrows.obj']
    apply congrArg F.chain.obj
    ext
    simp only
    omega
  let e : T.obj₂ ≅ E := e₂.trans ((eqToIso hright).trans eE)
  have hmor₂ : T.mor₂ = 0 := by
    have he : e.inv ≫ T.mor₂ = 0 := hzero _
    calc
      T.mor₂ = (e.hom ≫ e.inv) ≫ T.mor₂ := by simp
      _ = e.hom ≫ (e.inv ≫ T.mor₂) := by simp only [Category.assoc]
      _ = 0 := by rw [he, comp_zero]
  have hcomp : T.mor₂ ≫ 𝟙 T.obj₃ = 0 := by simp [hmor₂]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ T (F.triangle_dist i) (𝟙 T.obj₃) hcomp
  suffices hg_zero : g = 0 by
    change 𝟙 T.obj₃ = 0
    rw [hg, hg_zero, comp_zero]
  let e₁ := Classical.choice (F.triangle_obj₁ i)
  by_cases hone : F.n = 1
  · have hleft : F.chain.obj' (F.n - 1) (by omega) = F.chain.left := by
      simp only [ComposableArrows.obj']
      apply congrArg F.chain.obj
      ext
      simp only
      omega
    have hT₁ : IsZero T.obj₁ := F.base_isZero.of_iso (e₁.trans (eqToIso hleft))
    exact ((shiftFunctor C (1 : ℤ)).map_isZero hT₁).eq_of_src g 0
  · let pfx := F.prefix C (F.n - 1) (by omega)
    let shifted := pfx.shift C s (1 : ℤ)
    let e₁shift := (shiftFunctor C (1 : ℤ)).mapIso e₁
    let source := shifted.ofIso C e₁shift.symm
    let target := HNFiltration.single C T.obj₃ (F.φ i) (F.semistable i)
    apply s.hom_eq_zero_of_phase_gap C source target
    intro j k
    have hsource_n : source.n = F.n - 1 := rfl
    have hj : j.val < F.n - 1 := by
      rw [← hsource_n]
      exact j.isLt
    change F.φ i < F.φ ⟨j.val, by omega⟩ + (1 : ℤ)
    have hphase : F.φ i ≤ F.φ ⟨j.val, by omega⟩ :=
      F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
    norm_num
    linarith

/-- The last factor of any HN filtration is bounded above by a nonzero last
factor of another filtration of the same object. -/
theorem HNFiltration.phiMinus_le_of_lastFactor_nonzero (s : Slicing C) {E : C}
    (F G : HNFiltration C s.P E) (hF : 0 < F.n) (hG : 0 < G.n)
    (hneG : ¬IsZero (G.factor ⟨G.n - 1, by omega⟩)) :
    F.phiMinus C hF ≤ G.phiMinus C hG := by
  by_contra h
  push Not at h
  have hgap : ∀ j : Fin F.n, G.φ ⟨G.n - 1, by omega⟩ < F.φ j := fun j =>
    lt_of_lt_of_le (by
      change G.phiMinus C hG < F.phiMinus C hF
      exact h) (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega)))
  let target := HNFiltration.single C (G.factor ⟨G.n - 1, by omega⟩)
    (G.φ ⟨G.n - 1, by omega⟩) (G.semistable ⟨G.n - 1, by omega⟩)
  have hzero : ∀ f : E ⟶ G.factor ⟨G.n - 1, by omega⟩, f = 0 := fun f =>
    s.hom_eq_zero_of_phase_gap C F target
      (fun i _ => by simpa [target, HNFiltration.single] using hgap i) f
  exact hneG (G.lastFactor_isZero_of_hom_eq_zero C s hG hzero)

/-- Nonzero last factors of two HN filtrations have the same phase. -/
theorem HNFiltration.phiMinus_eq_of_lastFactors_nonzero (s : Slicing C) {E : C}
    (F G : HNFiltration C s.P E) (hF : 0 < F.n) (hG : 0 < G.n)
    (hneF : ¬IsZero (F.factor ⟨F.n - 1, by omega⟩))
    (hneG : ¬IsZero (G.factor ⟨G.n - 1, by omega⟩)) :
    F.phiMinus C hF = G.phiMinus C hG :=
  le_antisymm (F.phiMinus_le_of_lastFactor_nonzero C s G hF hG hneG)
    (G.phiMinus_le_of_lastFactor_nonzero C s F hG hF hneF)

/-- The intrinsic highest phase of a nonzero object. -/
noncomputable def Slicing.phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (s.exists_hn_nonzero_first C hE).choose
  let hn := (s.exists_hn_nonzero_first C hE).choose_spec.choose
  F.phiPlus C hn

/-- The intrinsic lowest phase of a nonzero object. -/
noncomputable def Slicing.phiMinus (s : Slicing C) (E : C) (hE : ¬IsZero E) : ℝ :=
  let F := (s.exists_hn_nonzero_last C hE).choose
  let hn := (s.exists_hn_nonzero_last C hE).choose_spec.choose
  F.phiMinus C hn

/-- Any HN filtration with nonzero first factor computes the intrinsic highest phase. -/
theorem Slicing.phiPlus_eq (s : Slicing C) (E : C) (hE : ¬IsZero E)
    (F : HNFiltration C s.P E) (hn : 0 < F.n) (hne : ¬IsZero (F.factor ⟨0, hn⟩)) :
    s.phiPlus C E hE = F.phiPlus C hn := by
  unfold Slicing.phiPlus
  let G := (s.exists_hn_nonzero_first C hE).choose
  let hG := (s.exists_hn_nonzero_first C hE).choose_spec.choose
  let hneG := (s.exists_hn_nonzero_first C hE).choose_spec.choose_spec
  exact G.phiPlus_eq_of_firstFactors_nonzero C s F hG hn hneG hne

/-- The intrinsic highest phase is invariant under isomorphism. -/
theorem Slicing.phiPlus_iso (s : Slicing C) {E E' : C} (e : E ≅ E')
    (hE : ¬IsZero E) (hE' : ¬IsZero E') :
    s.phiPlus C E hE = s.phiPlus C E' hE' := by
  obtain ⟨F, hn, hfirst⟩ := s.exists_hn_nonzero_first C hE
  calc
    s.phiPlus C E hE = F.phiPlus C hn :=
      s.phiPlus_eq C E hE F hn hfirst
    _ = s.phiPlus C E' hE' :=
      (s.phiPlus_eq C E' hE' (F.ofIso C e) hn hfirst).symm

/-- Any HN filtration with nonzero last factor computes the intrinsic lowest phase. -/
theorem Slicing.phiMinus_eq (s : Slicing C) (E : C) (hE : ¬IsZero E)
    (F : HNFiltration C s.P E) (hn : 0 < F.n)
    (hne : ¬IsZero (F.factor ⟨F.n - 1, by omega⟩)) :
    s.phiMinus C E hE = F.phiMinus C hn := by
  unfold Slicing.phiMinus
  let G := (s.exists_hn_nonzero_last C hE).choose
  let hG := (s.exists_hn_nonzero_last C hE).choose_spec.choose
  let hneG := (s.exists_hn_nonzero_last C hE).choose_spec.choose_spec
  exact G.phiMinus_eq_of_lastFactors_nonzero C s F hG hn hneG hne

/-- The intrinsic lowest phase is invariant under isomorphism. -/
theorem Slicing.phiMinus_iso (s : Slicing C) {E E' : C} (e : E ≅ E')
    (hE : ¬IsZero E) (hE' : ¬IsZero E') :
    s.phiMinus C E hE = s.phiMinus C E' hE' := by
  obtain ⟨F, hn, hlast⟩ := s.exists_hn_nonzero_last C hE
  calc
    s.phiMinus C E hE = F.phiMinus C hn :=
      s.phiMinus_eq C E hE F hn hlast
    _ = s.phiMinus C E' hE' :=
      (s.phiMinus_eq C E' hE' (F.ofIso C e) hn hlast).symm

/-- The intrinsic lowest phase is no greater than the intrinsic highest phase. -/
theorem Slicing.phiMinus_le_phiPlus (s : Slicing C) (E : C) (hE : ¬IsZero E) :
    s.phiMinus C E hE ≤ s.phiPlus C E hE := by
  by_contra h
  push Not at h
  let F := (s.exists_hn_nonzero_first C hE).choose
  let hF := (s.exists_hn_nonzero_first C hE).choose_spec.choose
  let G := (s.exists_hn_nonzero_last C hE).choose
  let hG := (s.exists_hn_nonzero_last C hE).choose_spec.choose
  have hgap : ∀ i j, F.φ j < G.φ i := fun i j =>
    calc
      F.φ j ≤ F.phiPlus C hF := (F.phase_mem_range C hF j).2
      _ = s.phiPlus C E hE := by unfold Slicing.phiPlus; rfl
      _ < s.phiMinus C E hE := h
      _ = G.phiMinus C hG := by unfold Slicing.phiMinus; rfl
      _ ≤ G.φ i := (G.phase_mem_range C hG i).1
  have hid : (𝟙 E : E ⟶ E) = 0 := s.hom_eq_zero_of_phase_gap C G F hgap (𝟙 E)
  exact hE ((IsZero.iff_id_eq_zero E).mpr hid)

/-- A nonzero semistable object's intrinsic highest phase is its semistable phase. -/
theorem Slicing.phiPlus_eq_of_semistable (s : Slicing C) (E : C) (hE : ¬IsZero E)
    (φ : ℝ) (hP : s.P φ E) : s.phiPlus C E hE = φ := by
  let F := HNFiltration.single C E φ hP
  have hn : 0 < F.n := by simp [F, HNFiltration.single]
  have hfactor : F.factor ⟨0, hn⟩ = E := rfl
  have hne : ¬IsZero (F.factor ⟨0, hn⟩) := by simpa [hfactor] using hE
  simpa [F, HNFiltration.phiPlus, HNFiltration.single] using s.phiPlus_eq C E hE F hn hne

/-- A nonzero semistable object's intrinsic lowest phase is its semistable phase. -/
theorem Slicing.phiMinus_eq_of_semistable (s : Slicing C) (E : C) (hE : ¬IsZero E)
    (φ : ℝ) (hP : s.P φ E) : s.phiMinus C E hE = φ := by
  let F := HNFiltration.single C E φ hP
  have hn : 0 < F.n := by simp [F, HNFiltration.single]
  have hfactor : F.factor ⟨F.n - 1, by omega⟩ = E := rfl
  have hne : ¬IsZero (F.factor ⟨F.n - 1, by omega⟩) := by simpa [hfactor] using hE
  simpa [F, HNFiltration.phiMinus, HNFiltration.single] using s.phiMinus_eq C E hE F hn hne

/-- Some HN filtration realizes both intrinsic phase extrema. -/
theorem Slicing.exists_hn_intrinsic_width (s : Slicing C) {E : C} (hE : ¬IsZero E) :
    ∃ (F : HNFiltration C s.P E) (hn : 0 < F.n),
      F.phiPlus C hn = s.phiPlus C E hE ∧
        F.phiMinus C hn = s.phiMinus C E hE := by
  obtain ⟨F, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hE
  exact ⟨F, hn, (s.phiPlus_eq C E hE F hn hfirst).symm,
    (s.phiMinus_eq C E hE F hn hlast).symm⟩

end CategoryTheory.Triangulated
