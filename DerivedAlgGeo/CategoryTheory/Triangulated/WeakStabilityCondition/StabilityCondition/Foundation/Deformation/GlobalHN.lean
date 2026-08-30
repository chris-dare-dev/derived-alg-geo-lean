/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.GlobalTruncation

/-!
# Global HN filtrations for the owner deformed slices

The global cut triangles are iterated across a finite phase interval.  This
file first records the exact orthogonality of the provisional cuts and a
normalization lemma which discards the parts of a local filtration lying
outside a prescribed cut window.
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

namespace StabilityCondition.WithClassMap

/-- The two provisional cuts at the same phase are orthogonal. -/
theorem hom_eq_zero_of_deformedGtLe
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {E F : C}
    (hE : σ.deformedGtPred C W hr0 hr1 hW ε t E)
    (hF : σ.deformedLePred C W hr0 hr1 hW ε t F)
    (f : E ⟶ F) : f = 0 := by
  apply ExtensionClosure.hom_eq_zero (hE := hE) (hF := hF)
  intro X Y hX hY g
  obtain ⟨ψX, hψX, hPX⟩ := hX
  obtain ⟨ψY, hψY, hPY⟩ := hY
  exact σ.hom_eq_zero_of_deformedPred C W hr0 hr1 hW
    hε hε2 hε8 hsin hPX hPY (hψY.trans_lt hψX) g

/-- An object lying in both provisional cuts at the same phase is zero. -/
theorem isZero_of_deformedGtLe
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {t : ℝ} {E : C}
    (hGt : σ.deformedGtPred C W hr0 hr1 hW ε t E)
    (hLe : σ.deformedLePred C W hr0 hr1 hW ε t E) : IsZero E := by
  rw [IsZero.iff_id_eq_zero]
  exact σ.hom_eq_zero_of_deformedGtLe C W hr0 hr1 hW
    hε hε2 hε8 hsin hGt hLe (𝟙 E)

/-- Restrict a deformed HN filtration to the open-closed phase window forced
by cut membership of its target. -/
theorem deformedHN_of_cut_window
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {a b : ℝ} {E : C}
    (G : HNFiltration C (σ.deformedPred C W hr0 hr1 hW ε) E)
    (hGt : σ.deformedGtPred C W hr0 hr1 hW ε a E)
    (hLe : σ.deformedLePred C W hr0 hr1 hW ε b E) :
    ∃ G' : HNFiltration C (σ.deformedPred C W hr0 hr1 hW ε) E,
      (∀ j, a < G'.φ j) ∧ ∀ j, G'.φ j ≤ b := by
  obtain ⟨Xhi, Xlo, Ghi, Glo, fhi, glo, δlo, hTlo,
      hGhi, hGlo, -, -⟩ := G.exists_split_at_cutoff C a
  have hXhiGt : σ.deformedGtPred C W hr0 hr1 hW ε a Xhi :=
    ExtensionClosure.ofPostnikovTower Ghi.toPostnikovTower
      (fun j => ⟨Ghi.φ j, hGhi j, Ghi.semistable j⟩)
  have hXloLe : σ.deformedLePred C W hr0 hr1 hW ε a Xlo :=
    ExtensionClosure.ofPostnikovTower Glo.toPostnikovTower
      (fun j => ⟨Glo.φ j, hGlo j, Glo.semistable j⟩)
  have hXloGt : σ.deformedGtPred C W hr0 hr1 hW ε a Xlo :=
    σ.deformedGtPred_of_triangle_obj₃ C W hr0 hr1 hW hTlo hXhiGt hGt
  have hXloZero := σ.isZero_of_deformedGtLe C W hr0 hr1 hW
    hε hε2 hε8 hsin hXloGt hXloLe
  haveI : IsIso fhi :=
    (Triangle.isZero₃_iff_isIso₁ _ hTlo).mp hXloZero
  let ehi : Xhi ≅ E := asIso fhi
  have hXhiLe : σ.deformedLePred C W hr0 hr1 hW ε b Xhi :=
    ExtensionClosure.ofIso ehi.symm hLe
  by_cases hnhi : 0 < Ghi.n
  · obtain ⟨Xabove, Xmid, Gabove, Gmid, fabove, gmid, δmid, hTmid,
        hGabove, hGmid, hGmidLower, -⟩ := Ghi.exists_split_at_cutoff C b
    have hXaboveGt : σ.deformedGtPred C W hr0 hr1 hW ε b Xabove :=
      ExtensionClosure.ofPostnikovTower Gabove.toPostnikovTower
        (fun j => ⟨Gabove.φ j, hGabove j, Gabove.semistable j⟩)
    have hXmidLe : σ.deformedLePred C W hr0 hr1 hW ε b Xmid :=
      ExtensionClosure.ofPostnikovTower Gmid.toPostnikovTower
        (fun j => ⟨Gmid.φ j, hGmid j, Gmid.semistable j⟩)
    have hXaboveLe : σ.deformedLePred C W hr0 hr1 hW ε b Xabove :=
      σ.deformedLePred_of_triangle_obj₁ C W hr0 hr1 hW hTmid hXhiLe hXmidLe
    have hXaboveZero := σ.isZero_of_deformedGtLe C W hr0 hr1 hW
      hε hε2 hε8 hsin hXaboveGt hXaboveLe
    haveI : IsIso gmid :=
      (Triangle.isZero₁_iff_isIso₂ _ hTmid).mp hXaboveZero
    let emid : Xmid ≅ E := (asIso gmid).symm.trans ehi
    exact ⟨Gmid.ofIso C emid,
      fun j => (hGhi ⟨Ghi.n - 1, by omega⟩).trans_le
        (hGmidLower hnhi j), hGmid⟩
  · have hnhi0 : Ghi.n = 0 := by omega
    exact ⟨Ghi.ofIso C ehi,
      fun j => False.elim (by simpa [HNFiltration.ofIso, hnhi0] using j.isLt),
      fun j => False.elim (by simpa [HNFiltration.ofIso, hnhi0] using j.isLt)⟩

/-- A single strip between consecutive global cuts has a deformed HN
filtration whose phases lie in exactly that strip. -/
theorem deformedHN_exists_in_cut_strip
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (t : ℝ)
    (hGt : σ.deformedGtPred C W hr0 hr1 hW ε (t - ε₀) E)
    (hLe : σ.deformedLePred C W hr0 hr1 hW ε t E) :
    ∃ G : HNFiltration C (σ.deformedPred C W hr0 hr1 hW ε) E,
      (∀ j, t - ε₀ < G.φ j) ∧ ∀ j, G.φ j ≤ t := by
  by_cases hE : IsZero E
  · exact ⟨HNFiltration.zero C E hE, fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  · let a := t - 4 * ε₀
    let b := t + 4 * ε₀
    have hab : a < b := by dsimp [a, b]; linarith
    letI : Fact (a < b) := ⟨hab⟩
    letI : Fact (b - a ≤ 1) := ⟨by dsimp [a, b]; linarith⟩
    have hthin : b - a + 2 * ε < 1 := by
      dsimp [a, b]
      linarith
    have hFinite : ThinStrictFiniteLength C σ a b := by
      intro Y
      have hY := hWide t Y
      exact Slicing.IntervalCat.isStrictFiniteLength_of_isFiniteLength C hY
    have hOldGt : σ.slicing.gtProp C (t - ε₀ - ε) E :=
      σ.deformedGtPred_gtProp C W hr0 hr1 hW hε hε2 hsin E hGt
    have hOldLe : σ.slicing.leProp C (t + ε) E :=
      σ.deformedLePred_leProp C W hr0 hr1 hW hε hε2 hsin E hLe
    have hLower : a + 2 * ε ≤ t - ε₀ - ε := by
      dsimp [a]
      linarith
    have hUpper : t + ε < b - 4 * ε := by
      dsimp [b]
      linarith
    have hInner : σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) E := by
      apply σ.slicing.intervalProp_of_gtProp_ltProp C
      · exact σ.slicing.gtProp_anti C hLower E hOldGt
      · exact σ.slicing.ltProp_of_leProp_of_lt C hUpper E hOldLe
    obtain ⟨G, -, -⟩ := σ.interior_has_enveloped_HN C W hr0 hr1 hW
      hab hFinite hε hε2 hε8 hthin hsin hE hInner
    exact σ.deformedHN_of_cut_window C W hr0 hr1 hW
      hε hε2 hε8 hsin G hGt hLe

/-- Iterating consecutive cut strips produces an HN filtration on every
object already bounded by two provisional cuts. -/
theorem deformedHN_exists_of_bounded_cuts
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (n : ℕ) (t : ℝ) (E : C)
    (hGt : σ.deformedGtPred C W hr0 hr1 hW ε (t - (n : ℝ) * ε₀) E)
    (hLe : σ.deformedLePred C W hr0 hr1 hW ε t E) :
    ∃ G : HNFiltration C (σ.deformedPred C W hr0 hr1 hW ε) E,
      (∀ j, t - (n : ℝ) * ε₀ < G.φ j) ∧
        ∀ j, G.φ j ≤ t := by
  induction n generalizing t E with
  | zero =>
      have hGt' : σ.deformedGtPred C W hr0 hr1 hW ε t E := by
        simpa using hGt
      have hE := σ.isZero_of_deformedGtLe C W hr0 hr1 hW
        hε hε2 hε8 hsin hGt' hLe
      exact ⟨HNFiltration.zero C E hE,
        fun j => Fin.elim0 j, fun j => Fin.elim0 j⟩
  | succ n ih =>
      let cut := t - ε₀
      have hLower : t - ((n + 1 : ℕ) : ℝ) * ε₀ =
          cut - (n : ℝ) * ε₀ := by
        dsimp [cut]
        push_cast
        ring
      obtain ⟨X, Y, f, g, δ, hT, hXgt, hYle⟩ :=
        σ.exists_global_deformedCut_triangle C W hr0 hr1 hW
          hε₀16 hWide hε hεhalf hε2 hε8 hsin E cut
      have hYleTop : σ.deformedLePred C W hr0 hr1 hW ε t Y :=
        σ.deformedLePred_mono C W hr0 hr1 hW (by dsimp [cut]; linarith) Y hYle
      have hXleTop : σ.deformedLePred C W hr0 hr1 hW ε t X :=
        σ.deformedLePred_of_triangle_obj₁ C W hr0 hr1 hW hT hLe hYleTop
      have hLowerCut : t - ((n + 1 : ℕ) : ℝ) * ε₀ ≤ cut := by
        dsimp [cut]
        push_cast
        nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
      have hXgtLower : σ.deformedGtPred C W hr0 hr1 hW ε
          (t - ((n + 1 : ℕ) : ℝ) * ε₀) X :=
        σ.deformedGtPred_anti C W hr0 hr1 hW hLowerCut X hXgt
      have hYgtLower : σ.deformedGtPred C W hr0 hr1 hW ε
          (t - ((n + 1 : ℕ) : ℝ) * ε₀) Y :=
        σ.deformedGtPred_of_triangle_obj₃ C W hr0 hr1 hW hT hXgtLower hGt
      obtain ⟨GX, hGXlo, hGXhi⟩ :=
        σ.deformedHN_exists_in_cut_strip C W hr0 hr1 hW
          hε₀16 hWide hε hεhalf hε2 hε8 hsin t hXgt hXleTop
      obtain ⟨GY, hGYlo, hGYhi⟩ := ih cut Y (hLower ▸ hYgtLower) hYle
      obtain ⟨G, hGlo, hGhi⟩ :=
        HNFiltration.exists_of_distinguished_triangle_phase_bounds C
          (fun ψ => σ.deformedPred_isClosedUnderIsomorphisms C W hr0 hr1 hW ε ψ)
          GX GY f g δ hT (t - ((n + 1 : ℕ) : ℝ) * ε₀) t
          (fun j => hLowerCut.trans_lt (hGXlo j))
          (fun j => hLower ▸ hGYlo j)
          (fun i j => (hGYhi i).trans_lt (hGXlo j))
          hGXhi (fun i => (hGYhi i).trans (by dsimp [cut]; linarith))
      exact ⟨G, hGlo, hGhi⟩

/-- Every object has an HN filtration for the repository-owned deformed
phase predicate. -/
theorem deformedHN_exists
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (E : C) :
    Nonempty (HNFiltration C (σ.deformedPred C W hr0 hr1 hW ε) E) := by
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  by_cases hn : 0 < F.n
  · let first : Fin F.n := ⟨0, hn⟩
    let last : Fin F.n := ⟨F.n - 1, by omega⟩
    let top : ℝ := F.φ first + 2 * ε
    let bottom : ℝ := F.φ last - 2 * ε
    have hε₀10 : ε₀ < 1 / 10 := by linarith
    have hεε₀ : ε < ε₀ := by linarith
    have collapseGt : ExtensionClosure
        (σ.deformedGtPred C W hr0 hr1 hW ε bottom) ≤
        σ.deformedGtPred C W hr0 hr1 hW ε bottom :=
      ExtensionClosure.le_of_closed
        (fun hzero => .zero hzero) (fun _ h => h)
        (fun hT hX hY => .ext hT hX hY)
    have collapseLe : ExtensionClosure
        (σ.deformedLePred C W hr0 hr1 hW ε top) ≤
        σ.deformedLePred C W hr0 hr1 hW ε top :=
      ExtensionClosure.le_of_closed
        (fun hzero => .zero hzero) (fun _ h => h)
        (fun hT hX hY => .ext hT hX hY)
    have hGt : σ.deformedGtPred C W hr0 hr1 hW ε bottom E := by
      apply collapseGt
      exact ExtensionClosure.ofPostnikovTower F.toPostnikovTower (fun j => by
        by_cases hj : IsZero (F.factor j)
        · exact .zero hj
        · exact σ.semistable_mem_deformedGt C W hr0 hr1 hW
            hε₀10 hWide hε hεε₀ hε2 hε8 hsin
            (by
              have hphase : F.φ last ≤ F.φ j :=
                F.hφ.antitone (Fin.mk_le_mk.mpr (by change j.val ≤ F.n - 1; omega))
              dsimp [bottom]
              linarith)
            (F.semistable j) hj)
    have hLe : σ.deformedLePred C W hr0 hr1 hW ε top E := by
      apply collapseLe
      exact ExtensionClosure.ofPostnikovTower F.toPostnikovTower (fun j => by
        by_cases hj : IsZero (F.factor j)
        · exact .zero hj
        · exact σ.deformedLePred_of_deformedLtPred C W hr0 hr1 hW _
            (σ.semistable_mem_deformedLt C W hr0 hr1 hW
              hε₀10 hWide hε hεε₀ hε2 hε8 hsin
              (by
                have hphase : F.φ j ≤ F.φ first :=
                  F.hφ.antitone
                    (Fin.mk_le_mk.mpr (by change 0 ≤ j.val; exact Nat.zero_le j.val))
                dsimp [top]
                linarith)
              (F.semistable j) hj))
    obtain ⟨n, hnLarge⟩ := exists_nat_gt ((top - bottom) / ε₀)
    have hBound : top - (n : ℝ) * ε₀ ≤ bottom := by
      have hnReal : (top - bottom) / ε₀ < (n : ℝ) := by
        exact_mod_cast hnLarge
      have hmul : top - bottom < (n : ℝ) * ε₀ :=
        (div_lt_iff₀ hε₀).mp hnReal
      linarith
    have hGt' := σ.deformedGtPred_anti C W hr0 hr1 hW hBound E hGt
    obtain ⟨G, -, -⟩ := σ.deformedHN_exists_of_bounded_cuts
      C W hr0 hr1 hW hε₀ hε₀16 hWide hε hεhalf hε2 hε8 hsin
      n top E hGt' hLe
    exact ⟨G⟩
  · exact ⟨HNFiltration.zero C E (F.isZero_of_length_zero (by omega))⟩

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
