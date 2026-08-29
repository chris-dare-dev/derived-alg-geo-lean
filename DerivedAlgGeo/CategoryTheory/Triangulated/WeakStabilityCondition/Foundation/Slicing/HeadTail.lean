/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.FiltrationOperations

/-!
# Head/tail decompositions of HN filtrations

This file splits the highest-phase factor from an owner HN filtration. The
tail has one fewer factor, and its phase indexing is identified with the
remaining phase indexing of the original filtration.

The construction is purely triangulated. In particular, it does not depend
on a central charge or mass; those structures consume this decomposition but
are not prerequisites for it.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Split an HN filtration into its highest-phase factor and an HN-filtered
tail. The tail has one fewer factor, and factor `j` of the tail has the phase
of factor `j + 1` of the original filtration. -/
theorem HNFiltration.exists_headTailFiltration
    {s : Slicing C} {E : C} (F : HNFiltration C s.P E) (hn : 0 < F.n) :
    ∃ (Y : C) (G : HNFiltration C s.P Y)
      (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
      (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      G.n = F.n - 1 ∧
      ∀ j : Fin G.n, ∃ i : Fin F.n,
        i.val = j.val + 1 ∧ G.φ j = F.φ i := by
  suffices hmain : ∀ (m : ℕ) {E : C} (F : HNFiltration C s.P E),
      F.n ≤ m → ∀ hn : 0 < F.n,
      ∃ (Y : C) (G : HNFiltration C s.P Y)
        (f : F.factor ⟨0, hn⟩ ⟶ E) (g : E ⟶ Y)
        (h : Y ⟶ (F.factor ⟨0, hn⟩)⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧
        G.n = F.n - 1 ∧
        ∀ j : Fin G.n, ∃ i : Fin F.n,
          i.val = j.val + 1 ∧ G.φ j = F.φ i by
    exact hmain F.n F le_rfl hn
  intro m
  induction m with
  | zero =>
      intro E F hFm hn
      omega
  | succ m ih =>
      intro E F hFm hn
      by_cases hn1 : F.n = 1
      · let i0 : Fin F.n := ⟨0, hn⟩
        let T := F.triangle i0
        let e₁ := Classical.choice (F.triangle_obj₁ i0)
        let e₂ := Classical.choice (F.triangle_obj₂ i0)
        have hT₁ : IsZero T.obj₁ := F.base_isZero.of_iso e₁
        haveI : IsIso T.mor₂ :=
          (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist i0)).mp hT₁
        have hchain1 : F.chain.obj' 1 (by omega) = F.chain.right := by
          congr 1
          omega
        let e₂E : T.obj₂ ≅ E :=
          e₂.trans ((eqToIso hchain1).trans (Classical.choice F.top_iso))
        let e : F.factor i0 ≅ E := (asIso T.mor₂).symm.trans e₂E
        let G := HNFiltration.zero (P := s.P) C (0 : C) (isZero_zero C)
        refine ⟨0, G, e.hom, 0, 0, ?_, ?_, ?_⟩
        · apply isomorphic_distinguished _ (contractible_distinguished (F.factor i0))
          exact Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _)
            (by simp [contractibleTriangle]) (by simp) (by simp)
        · change 0 = F.n - 1
          omega
        · intro j
          exact Fin.elim0 j
      · have hn2 : 2 ≤ F.n := by omega
        let A := F.chain.obj' (F.n - 1) (by omega)
        let P := F.prefix C (F.n - 1) (by omega)
        have hPn : 0 < P.n := by
          change 0 < F.n - 1
          omega
        obtain ⟨Y', G', f', g', h', hT', hnG', hφ'⟩ :=
          ih P (by change F.n - 1 ≤ m; omega) hPn
        let ilast : Fin F.n := ⟨F.n - 1, by omega⟩
        let T := F.triangle ilast
        let e₁ := Classical.choice (F.triangle_obj₁ ilast)
        let e₂ := Classical.choice (F.triangle_obj₂ ilast)
        let eE := Classical.choice F.top_iso
        have hchainN : F.chain.obj' (F.n - 1 + 1) (by omega) = F.chain.right := by
          congr 1
          omega
        let e₂E : T.obj₂ ≅ E := e₂.trans ((eqToIso hchainN).trans eE)
        let u : A ⟶ E := e₁.inv ≫ T.mor₁ ≫ e₂E.hom
        let TAE : Triangle C := Triangle.mk u (e₂E.inv ≫ T.mor₂)
          (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧')
        have hTAE : TAE ∈ distTriang C := by
          apply isomorphic_distinguished _ (F.triangle_dist ilast)
          exact Triangle.isoMk TAE T e₁.symm e₂E.symm (Iso.refl _)
            (by simp [TAE, u, e₂E]) (by simp [TAE, e₂E]) (by simp [TAE])
        obtain ⟨X₃, v₁₃, w₁₃, h₁₃⟩ := distinguished_cocone_triangle (f' ≫ u)
        let oct := Triangulated.someOctahedron rfl hT' hTAE h₁₃
        have hlast_lt : ∀ j : Fin G'.n, F.φ ilast < G'.φ j := by
          intro j
          obtain ⟨i, hi, hphase⟩ := hφ' j
          rw [hphase]
          exact F.hφ (Fin.mk_lt_mk.mpr (by
            change (ilast : Fin F.n).val > i.val
            simp only [ilast]
            have hiP := i.isLt
            change i.val < F.n - 1 at hiP
            omega))
        let GZ := G'.appendFactor C oct.triangle oct.mem (Iso.refl _)
          (Iso.refl _) (F.φ ilast) (F.semistable ilast) hlast_lt
        have hGZn : GZ.n = F.n - 1 := by
          change G'.n + 1 = F.n - 1
          rw [hnG']
          change (F.n - 1 - 1) + 1 = F.n - 1
          omega
        refine ⟨X₃, GZ, f' ≫ u, v₁₃, w₁₃, h₁₃, hGZn, ?_⟩
        intro j
        change ∃ i : Fin F.n, i.val = j.val + 1 ∧
          (if h : j.val < G'.n then G'.φ ⟨j.val, h⟩ else F.φ ilast) = F.φ i
        split_ifs with hj
        · obtain ⟨i, hi, hphase⟩ := hφ' ⟨j.val, hj⟩
          let iF : Fin F.n := ⟨i.val, by
            have hiP := i.isLt
            change i.val < F.n - 1 at hiP
            omega⟩
          refine ⟨iF, ?_, ?_⟩
          · simpa [iF] using hi
          · calc
              G'.φ ⟨j.val, hj⟩ = P.φ i := hphase
              _ = F.φ iF := by rfl
        · have hjlast : j.val = G'.n := by
            have hjbound := j.isLt
            change j.val < G'.n + 1 at hjbound
            omega
          refine ⟨ilast, ?_, rfl⟩
          simp only [ilast]
          rw [hjlast]
          have hG'n : G'.n = F.n - 2 := by
            rw [hnG']
            rfl
          rw [hG'n]
          omega

end CategoryTheory.Triangulated
