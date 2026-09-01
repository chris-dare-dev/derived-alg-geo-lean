/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.PhiPlusHN
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.LocalFiniteness

/-!
# Owner deformed HN existence

This file upgrades the strict MDQ recursion to the enveloped HN existence
statements used to assemble the deformed slicing.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

omit [IsTriangulated C] in
/-- The first factor of a Postnikov filtration whose factors lie in a common
thin old interval cannot have old highest phase above that of the total
object. -/
theorem HNFiltration.firstFactor_phiPlus_le_target
    (s : Slicing C) {P : ℝ → ObjectProperty C} {E : C}
    (G : HNFiltration C P E) (hn : 0 < G.n)
    (hE : ¬IsZero E) (hfirst : ¬IsZero (G.factor ⟨0, hn⟩))
    {a b : ℝ} (hab : b ≤ a + 1)
    (hfactors : ∀ i, s.intervalProp C a b (G.factor i)) :
    s.phiPlus C (G.factor ⟨0, hn⟩) hfirst ≤ s.phiPlus C E hE := by
  let T := G.toPostnikovTower
  have hnT : 0 < T.n := by simpa [T] using hn
  have hchain : ∀ k (hk : k ≤ T.n),
      s.intervalProp C a b (T.chain.obj' k (by omega)) :=
    fun k hk => s.intervalProp_chain_of_postnikovTower C T hfactors k hk
  have hchain1 : ¬IsZero (T.chain.obj' 1 (by omega)) := by
    intro hzero
    let T0 := T.triangle ⟨0, hn⟩
    have hobj₂ : IsZero T0.obj₂ :=
      (Iso.isZero_iff (Classical.choice (T.triangle_obj₂ ⟨0, hn⟩))).mpr hzero
    haveI : IsIso T0.mor₂ :=
      (Triangle.isZero₁_iff_isIso₂ T0 (T.triangle_dist ⟨0, hn⟩)).mp
        ((Iso.isZero_iff (Classical.choice (T.triangle_obj₁ ⟨0, hn⟩))).mpr
          T.base_isZero)
    exact hfirst ((Iso.isZero_iff (asIso T0.mor₂)).mp hobj₂)
  suffices main : ∀ d k (hk : k ≤ T.n), k + d = T.n → 0 < k →
      (hne : ¬IsZero (T.chain.obj' k (by omega))) →
      s.phiPlus C (T.chain.obj' k (by omega)) hne ≤
        s.phiPlus C E hE by
    have hle := main (T.n - 1) 1 (by omega) (by omega) (by omega) hchain1
    let T0 := T.triangle ⟨0, hn⟩
    haveI : IsIso T0.mor₂ :=
      (Triangle.isZero₁_iff_isIso₂ T0 (T.triangle_dist ⟨0, hn⟩)).mp
        ((Iso.isZero_iff (Classical.choice (T.triangle_obj₁ ⟨0, hn⟩))).mpr
          T.base_isZero)
    let e : T.factor ⟨0, hn⟩ ≅ T.chain.obj' 1 (by omega) :=
      ((Classical.choice (T.triangle_obj₂ ⟨0, hn⟩)).symm.trans
        (asIso T0.mor₂)).symm
    exact (s.phiPlus_iso C e hfirst hchain1).le.trans hle
  intro d
  induction d with
  | zero =>
      intro k hk hkn _ hne
      have hkTop : k = T.n := by omega
      subst k
      exact (s.phiPlus_iso C (Classical.choice T.top_iso) hne hE).le
  | succ d ih =>
      intro k hk hkn hkpos hne
      have hklt : k < T.n := by omega
      let Tk := T.triangle ⟨k, hklt⟩
      let e₁ := Classical.choice (T.triangle_obj₁ ⟨k, hklt⟩)
      let e₂ := Classical.choice (T.triangle_obj₂ ⟨k, hklt⟩)
      have hTk₁ : ¬IsZero Tk.obj₁ := fun hzero =>
        hne ((Iso.isZero_iff e₁).mp hzero)
      by_cases hnext : IsZero (T.chain.obj' (k + 1) (by omega))
      · exfalso
        have hTk₂ : IsZero Tk.obj₂ := (Iso.isZero_iff e₂).mpr hnext
        haveI : IsIso Tk.mor₃ :=
          (Triangle.isZero₂_iff_isIso₃ Tk (T.triangle_dist ⟨k, hklt⟩)).mp hTk₂
        have hfactor : ¬IsZero (T.factor ⟨k, hklt⟩) := by
          intro hzero
          exact hTk₁ ((Triangle.isZero₁_iff Tk
            (T.triangle_dist ⟨k, hklt⟩)).mpr
              ⟨hTk₂.eq_of_tgt _ _, hzero.eq_of_src _ _⟩)
        have hshift : s.intervalProp C (a + 1) (b + 1)
            (T.factor ⟨k, hklt⟩) := by
          rcases hchain k (by omega) with hzero | ⟨F, hF⟩
          · exact (hne hzero).elim
          · exact Or.inr
              ⟨((F.ofIso C e₁.symm).shift C s 1).ofIso C (asIso Tk.mor₃).symm,
                fun i => by
                  simp only [HNFiltration.ofIso, HNFiltration.shift,
                    Int.cast_one]
                  constructor <;> linarith [(hF i).1, (hF i).2]⟩
        have hid := s.intervalHom_eq_zero C hshift
          (hfactors ⟨k, hklt⟩) hab (𝟙 (T.factor ⟨k, hklt⟩))
        exact hfactor (by rw [IsZero.iff_id_eq_zero]; exact hid)
      · have hTk₂ : ¬IsZero Tk.obj₂ := fun hzero =>
          hnext ((Iso.isZero_iff e₂).mp hzero)
        have hTk₁I : s.intervalProp C a b Tk.obj₁ := by
          rcases hchain k (by omega) with hzero | ⟨F, hF⟩
          · exact Or.inl ((Iso.isZero_iff e₁.symm).mp hzero)
          · exact Or.inr ⟨F.ofIso C e₁.symm, hF⟩
        have hstep := s.phiPlus_triangle_le C hTk₁ hTk₂ hab hTk₁I
          (hfactors ⟨k, hklt⟩) (T.triangle_dist ⟨k, hklt⟩)
        have htail := ih (k + 1) (by omega) (by omega) (by omega) hnext
        have h₁ := s.phiPlus_iso C e₁ hTk₁ hne
        have h₂ := s.phiPlus_iso C e₂ hTk₂ hnext
        linarith

omit [IsTriangulated C] in
/-- The last factor of a Postnikov filtration whose factors lie in a common
thin old interval cannot have old lowest phase below that of the total
object. -/
theorem HNFiltration.target_phiMinus_le_lastFactor
    (s : Slicing C) {P : ℝ → ObjectProperty C} {E : C}
    (G : HNFiltration C P E) (hn : 0 < G.n)
    (hE : ¬IsZero E)
    (hlast : ¬IsZero (G.factor ⟨G.n - 1, by omega⟩))
    {a b : ℝ} (hab : b ≤ a + 1)
    (hfactors : ∀ i, s.intervalProp C a b (G.factor i)) :
    s.phiMinus C E hE ≤
      s.phiMinus C (G.factor ⟨G.n - 1, by omega⟩) hlast := by
  let T := G.toPostnikovTower
  let j : Fin T.n := ⟨T.n - 1, by simpa [T] using hn⟩
  let Tj := T.triangle j
  let e₁ := Classical.choice (T.triangle_obj₁ j)
  let e₂ := Classical.choice (T.triangle_obj₂ j)
  let eTop := Classical.choice T.top_iso
  have hchainTop : T.chain.obj' (j.val + 1) (by omega) =
      T.chain.obj (Fin.last T.n) := by
    apply congrArg T.chain.obj
    apply Fin.ext
    change T.n - 1 + 1 = T.n
    have : 0 < T.n := by simpa [T] using hn
    omega
  let e₂E : Tj.obj₂ ≅ E := e₂.trans ((eqToIso hchainTop).trans eTop)
  have hprefix : s.intervalProp C a b
      (T.chain.obj' (T.n - 1) (by omega)) :=
    s.intervalProp_chain_of_postnikovTower C T hfactors (T.n - 1) (by omega)
  have hA : s.intervalProp C a b Tj.obj₁ :=
    (s.intervalProp C a b).prop_of_iso e₁.symm hprefix
  have hTj₂ : ¬IsZero Tj.obj₂ := fun hzero =>
    hE ((Iso.isZero_iff e₂E).mp hzero)
  have hle := s.phiMinus_triangle_le C hlast hTj₂ hab hA
    (hfactors j) (T.triangle_dist j)
  calc
    s.phiMinus C E hE = s.phiMinus C Tj.obj₂ hTj₂ :=
      (s.phiMinus_iso C e₂E hTj₂ hE).symm
    _ ≤ s.phiMinus C (G.factor ⟨G.n - 1, by omega⟩) hlast := hle

namespace StabilityCondition.WithClassMap

/-- Every nonzero object in the interior of a thin finite-length interval
has an HN filtration by skewed-semistable factors whose phases are enveloped
by the ambient interval. -/
theorem interior_has_enveloped_HN_skewed
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFinite : ThinStrictFiniteLength C σ a b)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hE : ¬IsZero E)
    (hInner : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) E) :
    let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
    ∃ G : HNFiltration C (fun ψ X => F.IsSemistable X ψ) E,
      ∀ j, a + ε < G.φ j ∧ G.φ j < b - ε := by
  let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
  have hEab : σ.slicing.intervalProp C a b E :=
    σ.slicing.intervalProp_mono C (by linarith) (by linarith) E hInner
  let XI : σ.slicing.IntervalCat C a b := ⟨E, hEab⟩
  have hXI : ¬IsZero XI := fun hzero =>
    hE ((σ.slicing.intervalProp C a b).ι.map_isZero hzero)
  have hWindow : ∀ Y : σ.slicing.IntervalCat C a b, ¬IsZero Y.obj →
      a - ε < F.phase Y.obj ∧ F.phase Y.obj < b + ε := by
    intro Y hY
    exact σ.skewedPhase_mem_expanded_interval C W hr0 hr1 hW hab
      hε hε2 hthin hsin Y.property hY
  have hWidth : (b + ε) - (a - ε) < 1 := by linarith
  have hwide : 6 * ε ≤ b - a := by
    linarith [σ.slicing.phiMinus_gt_of_intervalProp C hE hInner,
      σ.slicing.phiPlus_lt_of_intervalProp C hE hInner,
      σ.slicing.phiMinus_le_phiPlus C E hE]
  have hquot : ∀ A : Subobject XI, A ≠ ⊤ → IsStrictMono A.arrow →
      a + ε < F.phase (cokernel A.arrow).obj := by
    intro A hAtop hAstrict
    have hQ : ¬IsZero (cokernel A.arrow).obj := fun hzero =>
      (Slicing.IntervalCat.cokernel_not_isZero_of_ne_top C hAtop hAstrict)
        (ObjectProperty.FullSubcategory.isZero_of_obj_isZero hzero)
    exact σ.skewedPhase_gt_of_strictQuotient_inner C W hr0 hr1 hW hab
      hε hε2 hthin hsin hInner (cokernel.π A.arrow)
      (isStrictEpi_cokernel A.arrow) hQ
  obtain ⟨G, hG⟩ := σ.hn_exists_with_phiPlus_reduction C W hr0 hr1 hW
    hab hFinite hWindow hWidth hε hε2 hε8 hthin hsin
    (by linarith) hwide (a + ε) le_rfl XI hXI hquot
    (fun h => σ.slicing.phiPlus_lt_of_intervalProp C h hInner)
  have hn : 0 < G.n := by
    by_contra h
    push Not at h
    exact hE (G.isZero_of_length_zero (by omega))
  have hfirstSS := G.semistable ⟨0, hn⟩
  have hfirstLe : σ.slicing.phiPlus C (G.factor ⟨0, hn⟩)
      hfirstSS.nonzero ≤ σ.slicing.phiPlus C E hE :=
    G.firstFactor_phiPlus_le_target C σ.slicing hn hE hfirstSS.nonzero
      (by linarith [Fact.out (p := b - a ≤ 1)])
      (fun i => (G.semistable i).interval)
  have hminus := σ.skewed_phiMinus_ge C W hr0 hr1 hW hab
    hε hε2 hthin hsin hfirstSS
  have hfirstUpper : G.φ ⟨0, hn⟩ < b - ε := by
    have hEupper := σ.slicing.phiPlus_lt_of_intervalProp C hE hInner
    have hminmax := σ.slicing.phiMinus_le_phiPlus C
      (G.factor ⟨0, hn⟩) hfirstSS.nonzero
    linarith
  refine ⟨G, fun j => ⟨(hG j).1, ?_⟩⟩
  exact (G.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le j.val))).trans_lt
    hfirstUpper

/-- Interior HN existence in the repository-owned deformed slice
predicate. -/
theorem interior_has_enveloped_HN
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b ε : ℝ} (hab : a < b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (hFinite : ThinStrictFiniteLength C σ a b)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hE : ¬IsZero E)
    (hInner : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) E) :
    ∃ G : HNFiltration C (σ.deformedPred C W hr0 hr1 hW ε) E,
      (∀ j, a + ε < G.φ j ∧ G.φ j < b - ε) ∧
        ∀ j, ¬IsZero (G.factor j) := by
  obtain ⟨G, hG⟩ := σ.interior_has_enveloped_HN_skewed C W hr0 hr1 hW
    hab hFinite hε hε2 hε8 hthin hsin hE hInner
  let G' : HNFiltration C (σ.deformedPred C W hr0 hr1 hW ε) E :=
    { toPostnikovTower := G.toPostnikovTower
      φ := G.φ
      hφ := G.hφ
      semistable := fun j => Or.inr
        ⟨a, b, hab, hthin, (hG j).1.le, (hG j).2.le, G.semistable j⟩ }
  exact ⟨G', hG, fun j => (G.semistable j).nonzero⟩

/-- Every nonzero old semistable object admits an owner deformed HN
filtration.  The wide local-finiteness sector is used directly, avoiding any
change-of-interval chain-condition assumption. -/
theorem semistable_has_deformedHN
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ : ℝ} (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    ∃ G : HNFiltration C (σ.deformedPred C W hr0 hr1 hW ε) E,
      (∀ j, φ - 4 * ε₀ + ε < G.φ j ∧
        G.φ j < φ + 4 * ε₀ - ε) ∧
      ∀ j, ¬IsZero (G.factor j) := by
  let a := φ - 4 * ε₀
  let b := φ + 4 * ε₀
  have hab : a < b := by dsimp [a, b]; linarith
  letI : Fact (a < b) := ⟨hab⟩
  letI : Fact (b - a ≤ 1) := ⟨by dsimp [a, b]; linarith⟩
  have hthin : b - a + 2 * ε < 1 := by
    dsimp [a, b]
    linarith
  have hFinite : ThinStrictFiniteLength C σ a b := by
    intro Y
    have hY := hWide φ Y
    exact Slicing.IntervalCat.isStrictFiniteLength_of_isFiniteLength C hY
  have hInner : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) E := by
    have hminus := σ.slicing.phiMinus_eq_of_semistable C E hE φ hP
    have hplus := σ.slicing.phiPlus_eq_of_semistable C E hE φ hP
    apply σ.slicing.intervalProp_of_intrinsic_phases C hE
    · rw [hminus]
      dsimp [a]
      linarith
    · rw [hplus]
      dsimp [b]
      linarith
  simpa [a, b] using σ.interior_has_enveloped_HN C W hr0 hr1 hW hab
    hFinite hε hε2 hε8 hthin hsin hE hInner

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
