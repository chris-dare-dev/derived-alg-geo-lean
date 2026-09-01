/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.HeadTail
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.InducedTStructures

/-!
# HN filtrations from phase-indexed induced t-structures

This file formalizes the finite phase-truncation argument in Corollary A.23 of
arXiv:2607.28411v1. A target HN filtration is split into its highest-phase
factor and tail. The t-structure supplied by formula (A.8) at that phase gives
the corresponding source triangle. Uniqueness of t-structure truncation
triangles identifies its image with the target head/tail triangle, and
induction on the target filtration length terminates the construction.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]

namespace Slicing.InducedTStructures

omit [IsTriangulated C] [IsTriangulated D] in
/-- Formula (A.8) reflects zero objects. This is the zero-length base case of
the phase-truncation induction. -/
theorem isZero_of_map_isZero {s : Slicing D} {F : C ⥤ D}
    (h : s.InducedTStructures F) {E : C} (hE : IsZero (F.obj E)) : IsZero E := by
  let t := h.tStructure 0
  have hLE : t.IsLE E 0 := (h.le_zero_iff 0 E).2 (Or.inl hE)
  have hGE : t.IsGE E 1 := (h.ge_one_iff 0 E).2 (Or.inl hE)
  exact t.isZero E 0 1 (by omega)

/-- A target HN filtration lifts to a source HN filtration. When the target
filtration is nonempty, the output phases remain in a strict finite window
around its lowest and highest phases. The window is the induction invariant
used to keep the head phase strictly above every tail phase. -/
private theorem exists_hn_of_target {s : Slicing D} {F : C ⥤ D}
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (h : s.InducedTStructures F) {E : C}
    (G : HNFiltration D s.P (F.obj E)) :
    ∃ H : HNFiltration C (s.preimagePhase F) E,
      (G.n = 0 → H.n = 0) ∧
      ∀ hn : 0 < G.n,
        (∀ j : Fin H.n, G.φ ⟨G.n - 1, by omega⟩ - 1 < H.φ j) ∧
        (∀ j : Fin H.n, H.φ j ≤ G.φ ⟨0, hn⟩) := by
  suffices hmain : ∀ (m : ℕ) {E : C}
      (G : HNFiltration D s.P (F.obj E)), G.n ≤ m →
      ∃ H : HNFiltration C (s.preimagePhase F) E,
        (G.n = 0 → H.n = 0) ∧
        ∀ hn : 0 < G.n,
          (∀ j : Fin H.n, G.φ ⟨G.n - 1, by omega⟩ - 1 < H.φ j) ∧
          (∀ j : Fin H.n, H.φ j ≤ G.φ ⟨0, hn⟩) by
    exact hmain G.n G le_rfl
  intro m
  induction m with
  | zero =>
      intro E G hG
      have hGn : G.n = 0 := by omega
      have hFE : IsZero (F.obj E) := G.isZero_of_length_zero hGn
      let H := HNFiltration.zero (P := s.preimagePhase F) C E (h.isZero_of_map_isZero hFE)
      exact ⟨H, fun _ => rfl, fun hn => absurd hn (by omega)⟩
  | succ m ih =>
      intro E G hG
      by_cases hGn : G.n = 0
      · have hFE : IsZero (F.obj E) := G.isZero_of_length_zero hGn
        let H := HNFiltration.zero (P := s.preimagePhase F) C E
          (h.isZero_of_map_isZero hFE)
        exact ⟨H, fun _ => rfl, fun hn => absurd hn (by omega)⟩
      · have hn : 0 < G.n := Nat.pos_of_ne_zero hGn
        let phi := G.φ ⟨0, hn⟩
        obtain ⟨Y, GY, fY, gY, kY, hTY, hGY_n, hGY_phase⟩ :=
          G.exists_headTailFiltration D hn
        let tC := h.tStructure phi
        let TC := (tC.triangleLTGE 1).obj E
        have hTC : TC ∈ distTriang C := tC.triangleLTGE_distinguished 1 E
        have hFTC : F.mapTriangle.obj TC ∈ distTriang D := F.map_distinguished TC hTC
        let TID := s.inducedTStructuresId
        let tD := TID.tStructure phi
        have hFTC₁ : tD.IsLE (F.obj TC.obj₁) 0 := by
          apply (TID.le_zero_iff phi (F.obj TC.obj₁)).2
          apply (h.le_zero_iff phi TC.obj₁).1
          simpa [TC] using tC.isLE_truncLT_obj E 1 0
        have hFTC₃ : tD.IsGE (F.obj TC.obj₃) 1 := by
          apply (TID.ge_one_iff phi (F.obj TC.obj₃)).2
          apply (h.ge_one_iff phi TC.obj₃).1
          simpa [TC] using tC.isGE_truncGE_obj E 1 1
        have hTY₁ : tD.IsLE (G.factor ⟨0, hn⟩) 0 := by
          apply (TID.le_zero_iff phi (G.factor ⟨0, hn⟩)).2
          exact s.geProp_of_semistable D (G.semistable ⟨0, hn⟩)
        have hTY₃ : tD.IsGE Y 1 := by
          apply (TID.ge_one_iff phi Y).2
          by_cases hGYzero : GY.n = 0
          · exact Or.inl (GY.isZero_of_length_zero hGYzero)
          · have hGYpos : 0 < GY.n := Nat.pos_of_ne_zero hGYzero
            apply s.ltProp_of_hn D GY phi _ hGYpos
            intro j
            obtain ⟨i, hi, hphase⟩ := hGY_phase j
            rw [hphase]
            exact G.hφ (Fin.mk_lt_mk.mpr (by omega))
        obtain ⟨eT, heT⟩ := tD.triangle_iso_exists hFTC hTY (Iso.refl _)
          0 1 hFTC₁ hFTC₃ hTY₁ hTY₃ (by omega)
        let eHead : F.obj TC.obj₁ ≅ G.factor ⟨0, hn⟩ := Triangle.π₁.mapIso eT
        let eTail : F.obj TC.obj₃ ≅ Y := Triangle.π₃.mapIso eT
        have hHead : s.preimagePhase F phi TC.obj₁ :=
          (s.P phi).prop_of_iso eHead.symm (G.semistable ⟨0, hn⟩)
        let GH := HNFiltration.single C TC.obj₁ phi hHead
        let GYF := GY.ofIso D eTail.symm
        obtain ⟨GT, hGTzero, hGTwindow⟩ :=
          ih GYF (by change GY.n ≤ m; omega)
        have hTail_gt : ∀ j : Fin GT.n,
            G.φ ⟨G.n - 1, by omega⟩ - 1 < GT.φ j := by
          by_cases hGYzero : GY.n = 0
          · have hGYFzero : GYF.n = 0 := by
              change GY.n = 0
              exact hGYzero
            have hGTn : GT.n = 0 := hGTzero hGYFzero
            intro j
            exact absurd j.isLt (by omega)
          · have hGYpos : 0 < GY.n := Nat.pos_of_ne_zero hGYzero
            have hGYFpos : 0 < GYF.n := by
              change 0 < GY.n
              exact hGYpos
            have hwindow := hGTwindow hGYFpos
            dsimp [GYF, HNFiltration.ofIso] at hwindow
            intro j
            have hlast := hGY_phase ⟨GY.n - 1, by omega⟩
            obtain ⟨i, hi, hphase⟩ := hlast
            have hiVal : i.val = G.n - 1 := by
              calc
                i.val = (GY.n - 1) + 1 := hi
                _ = GY.n := by omega
                _ = G.n - 1 := hGY_n
            have hiLast : i = ⟨G.n - 1, by omega⟩ := Fin.ext hiVal
            rw [hphase, hiLast] at hwindow
            exact hwindow.1 j
        have hTail_lt : ∀ j : Fin GT.n, GT.φ j < phi := by
          by_cases hGYzero : GY.n = 0
          · have hGYFzero : GYF.n = 0 := by
              change GY.n = 0
              exact hGYzero
            have hGTn : GT.n = 0 := hGTzero hGYFzero
            intro j
            exact absurd j.isLt (by omega)
          · have hGYpos : 0 < GY.n := Nat.pos_of_ne_zero hGYzero
            have hGYFpos : 0 < GYF.n := by
              change 0 < GY.n
              exact hGYpos
            have hwindow := hGTwindow hGYFpos
            dsimp [GYF, HNFiltration.ofIso] at hwindow
            intro j
            obtain ⟨i, hi, hphase⟩ := hGY_phase ⟨0, hGYpos⟩
            have hiPos : 0 < i.val := by omega
            calc
              GT.φ j ≤ GY.φ ⟨0, hGYpos⟩ := by simpa [GYF] using hwindow.2 j
              _ = G.φ i := hphase
              _ < phi := G.hφ (Fin.mk_lt_mk.mpr hiPos)
        have hTail_le : ∀ j : Fin GT.n, GT.φ j ≤ phi := fun j => (hTail_lt j).le
        have hsep : ∀ i : Fin GT.n, ∀ j : Fin GH.n, GT.φ i < GH.φ j := by
          intro i j
          simpa [GH, HNFiltration.single] using hTail_lt i
        let lower := G.φ ⟨G.n - 1, by omega⟩ - 1
        obtain ⟨H, hHgt, hHle⟩ :=
          HNFiltration.exists_of_distinguished_triangle_phase_bounds C
            (fun psi => ⟨by
              intro X X' e hX
              exact (s.P psi).prop_of_iso (F.mapIso e) hX⟩)
            GH GT TC.mor₁ TC.mor₂ TC.mor₃ hTC lower phi
            (fun j => by
              change lower < phi
              dsimp [lower, phi]
              have hlastle :
                  G.φ ⟨G.n - 1, by omega⟩ ≤ G.φ ⟨0, hn⟩ :=
                G.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
              linarith)
            hTail_gt hsep
            (fun j => by simp [GH, HNFiltration.single]) hTail_le
        refine ⟨H, fun hzero => absurd hn (by omega), ?_⟩
        intro _
        exact ⟨hHgt, hHle⟩

/-- The finite phase-truncation argument supplies the remaining HN field of
`Slicing.PreimageData`. -/
theorem hn_exists {s : Slicing D} {F : C ⥤ D}
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (h : s.InducedTStructures F) :
    ∀ E : C, Nonempty (HNFiltration C (s.preimagePhase F) E) := by
  intro E
  obtain ⟨G⟩ := s.hn_exists (F.obj E)
  obtain ⟨H, _, _⟩ := h.exists_hn_of_target G
  exact ⟨H⟩

/-- Formula (A.8), exactness of the detecting functor, and the target slicing
construct the genuine preimage slicing data. -/
theorem preimageData {s : Slicing D} {F : C ⥤ D}
    [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (h : s.InducedTStructures F) : s.PreimageData F :=
  h.toPreimageData h.hn_exists

end Slicing.InducedTStructures

end CategoryTheory.Triangulated
