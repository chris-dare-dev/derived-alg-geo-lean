/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.FiltrationOperations
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
# Phase truncations and the t-structure interface

This file isolates the final input needed to construct a t-structure from an
owner slicing: a distinguished triangle separating positive from nonpositive
HN phases.  The structure construction itself is proved here from that input;
the canonical decomposition supplied by an HN filtration is developed next.
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

variable [IsTriangulated C]

/-- Split an HN filtration at phase zero.  The proof removes the final factor,
recursively truncates the prefix, and uses an octahedron to attach a
nonpositive last factor to the lower-phase side. -/
theorem Slicing.exists_phase_truncation (s : Slicing C) (A : C)
    (F : HNFiltration C s.P A) :
    ∃ (X Y : C) (_ : s.gtProp C 0 X) (_ : s.leProp C 0 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  suffices main : ∀ (m : ℕ) (A : C) (F : HNFiltration C s.P A), F.n ≤ m →
      ∃ (X Y : C) (_ : s.gtProp C 0 X) (_ : s.leProp C 0 Y)
        (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C ∧
        (IsZero Y ∨ ∃ (G : HNFiltration C s.P Y) (hG : 0 < G.n),
          G.phiPlus C hG ≤ 0 ∧
          ∀ (_ : 0 < F.n) (j : Fin G.n), F.φ ⟨F.n - 1, by omega⟩ ≤ G.φ j) by
    obtain ⟨X, Y, hX, hY, f, g, h, hT, _⟩ := main F.n A F le_rfl
    exact ⟨X, Y, hX, hY, f, g, h, hT⟩
  intro m
  induction m with
  | zero =>
      intro A F hF
      have hn : F.n = 0 := by omega
      exact ⟨A, (0 : C), Or.inl (F.isZero_of_length_zero hn), Or.inl (isZero_zero C),
        𝟙 A, 0, 0, contractible_distinguished A, Or.inl (isZero_zero C)⟩
  | succ m ih =>
      intro A F hF
      by_cases hn : F.n = 0
      · exact ⟨A, (0 : C), Or.inl (F.isZero_of_length_zero hn), Or.inl (isZero_zero C),
          𝟙 A, 0, 0, contractible_distinguished A, Or.inl (isZero_zero C)⟩
      have hn₀ : 0 < F.n := Nat.pos_of_ne_zero hn
      by_cases hpos : ∀ i : Fin F.n, 0 < F.φ i
      · exact ⟨A, (0 : C), s.gtProp_of_hn C F 0 hpos hn₀,
          Or.inl (isZero_zero C), 𝟙 A, 0, 0, contractible_distinguished A,
          Or.inl (isZero_zero C)⟩
      · push Not at hpos
        by_cases hnonpos : ∀ i : Fin F.n, F.φ i ≤ 0
        · refine ⟨(0 : C), A, Or.inl (isZero_zero C), s.leProp_of_hn C F 0 hnonpos hn₀,
            0, 𝟙 A, 0, contractible_distinguished₁ A, Or.inr ⟨F, hn₀, ?_, ?_⟩⟩
          · exact hnonpos ⟨0, hn₀⟩
          · intro _ j
            exact F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))
        · push Not at hnonpos
          have hn₂ : 2 ≤ F.n := by
            by_contra h
            obtain ⟨i, hi⟩ := hpos
            obtain ⟨j, hj⟩ := hnonpos
            have hij : i = j := Fin.ext (by omega)
            subst j
            linarith
          let G := F.prefix C (F.n - 1) (by omega)
          have hGn : G.n = F.n - 1 := rfl
          obtain ⟨X, Y, hX, hY, f, g, h, hT, hYdata⟩ :=
            ih (F.chain.obj' (F.n - 1) (by omega)) G (by rw [hGn]; omega)
          let T := F.triangle ⟨F.n - 1, by omega⟩
          let e₁ := Classical.choice (F.triangle_obj₁ ⟨F.n - 1, by omega⟩)
          let e₂ := Classical.choice (F.triangle_obj₂ ⟨F.n - 1, by omega⟩)
          let eA := Classical.choice F.top_iso
          have chainTop : F.chain.obj' (F.n - 1 + 1) (by omega) =
              F.chain.obj (Fin.last F.n) :=
            congrArg F.chain.obj (Fin.ext (by simp [Fin.val_last]; omega))
          let e₂A : T.obj₂ ≅ A := e₂.trans ((eqToIso chainTop).trans eA)
          let u : F.chain.obj' (F.n - 1) (by omega) ⟶ A :=
            e₁.inv ≫ T.mor₁ ≫ e₂A.hom
          let Tu := Triangle.mk u (e₂A.inv ≫ T.mor₂)
            (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧')
          let TuIso := Triangle.isoMk Tu T e₁.symm e₂A.symm (Iso.refl _)
            (by simp [Tu, u, e₂A]) (by simp [Tu, e₂A]) (by simp [Tu])
          have hTu : Triangle.mk u (e₂A.inv ≫ T.mor₂)
              (T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧') ∈ distTriang C := by
            exact isomorphic_distinguished _ (F.triangle_dist ⟨F.n - 1, by omega⟩) _ TuIso
          obtain ⟨i, hi⟩ := hpos
          have hlast : F.φ ⟨F.n - 1, by omega⟩ ≤ 0 :=
            (F.hφ.antitone (Fin.mk_le_mk.mpr (by omega))).trans hi
          rcases hYdata with hYZ | ⟨GY, hGY, hGYle, hGYbound⟩
          · have hf : IsIso f := (Triangle.isZero₃_iff_isIso₁ _ hT).mp hYZ
            let eX : X ≅ F.chain.obj' (F.n - 1) (by omega) := asIso f
            let H := HNFiltration.single C T.obj₃ (F.φ ⟨F.n - 1, by omega⟩)
              (F.semistable ⟨F.n - 1, by omega⟩)
            refine ⟨X, T.obj₃, hX,
              s.leProp_of_hn C H 0 (fun _ => by simpa [H, HNFiltration.single] using hlast)
                (by change 0 < 1; omega),
              eX.hom ≫ u, e₂A.inv ≫ T.mor₂,
              T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' ≫ eX.inv⟦(1 : ℤ)⟧', ?_,
              Or.inr ⟨H, by change 0 < 1; omega, ?_, ?_⟩⟩
            · apply isomorphic_distinguished _ (F.triangle_dist ⟨F.n - 1, by omega⟩)
              exact Triangle.isoMk _ T (eX.trans e₁.symm) e₂A.symm (Iso.refl _)
                (by simp [u, eX, e₂A]) (by simp [e₂A]) (by simp [eX])
            · simpa [H, HNFiltration.phiPlus, HNFiltration.single] using hlast
            · intro _ j
              simp [H, HNFiltration.single]
          · have hGpos : 0 < G.n := by rw [hGn]; omega
            have hlast_lt : ∀ j : Fin GY.n,
                F.φ ⟨F.n - 1, by omega⟩ < GY.φ j := by
              intro j
              calc
                F.φ ⟨F.n - 1, by omega⟩ < F.φ ⟨F.n - 2, by omega⟩ :=
                  F.hφ (Fin.mk_lt_mk.mpr (by omega))
                _ = G.φ ⟨G.n - 1, by omega⟩ := by
                  simp only [G, HNFiltration.prefix_φ]
                  congr 1
                _ ≤ GY.φ j := hGYbound hGpos j
            obtain ⟨Z, v, w, hXZ⟩ := distinguished_cocone_triangle (f ≫ u)
            let oct := CategoryTheory.Triangulated.someOctahedron rfl hT hTu hXZ
            let GZ := GY.appendFactor C oct.triangle oct.mem (Iso.refl _) (Iso.refl _)
              (F.φ ⟨F.n - 1, by omega⟩) (F.semistable ⟨F.n - 1, by omega⟩) hlast_lt
            have hGZn : GZ.n = GY.n + 1 := rfl
            have hGZpos : 0 < GZ.n := by rw [hGZn]; omega
            refine ⟨X, Z, hX, Or.inr ⟨GZ, hGZpos, ?_⟩,
              f ≫ u, v, w, hXZ, Or.inr ⟨GZ, hGZpos, ?_, ?_⟩⟩
            · change GZ.φ ⟨0, hGZpos⟩ ≤ 0
              simp only [GZ, HNFiltration.appendFactor, dif_pos hGY]
              exact hGYle
            · change GZ.φ ⟨0, hGZpos⟩ ≤ 0
              simp only [GZ, HNFiltration.appendFactor, dif_pos hGY]
              exact hGYle
            · intro _ j
              change F.φ ⟨F.n - 1, by omega⟩ ≤ GZ.φ j
              simp only [GZ, HNFiltration.appendFactor]
              split_ifs with hj
              · exact (hlast_lt ⟨j, hj⟩).le
              · exact le_rfl

/-- Distinguished phase truncations at the boundary `0`.  This is the precise
decomposition datum required by the half-open t-structure convention, and it is
available for every owner slicing from its Harder--Narasimhan filtrations. -/
theorem Slicing.exists_phase_truncation_zero (s : Slicing C) (A : C) :
    ∃ (X Y : C) (_ : s.gtProp C 0 X) (_ : s.leProp C 0 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨F⟩ := s.hn_exists A
  exact s.exists_phase_truncation C A F

/-- An owner slicing determines a t-structure.  Its heart uses the half-open
convention `P((0, 1])`. -/
def Slicing.toTStructure (s : Slicing C) :
    CategoryTheory.Triangulated.TStructure C where
  le n := s.gtProp C (-n)
  ge n := s.leProp C (1 - n)
  le_isClosedUnderIsomorphisms _ := inferInstance
  ge_isClosedUnderIsomorphisms _ := inferInstance
  le_shift n a n' h X hX := by
    have ha : (a : ℝ) + n' = n := by exact_mod_cast h
    have phase : (-n' : ℝ) = -n + a := by linarith
    rw [phase]
    exact s.gtProp_shift C _ X a hX
  ge_shift n a n' h X hX := by
    have ha : (a : ℝ) + n' = n := by exact_mod_cast h
    have phase : (1 - n' : ℝ) = (1 - n) + a := by linarith
    rw [phase]
    exact s.leProp_shift C _ X a hX
  zero' {X Y} f hX hY := by
    exact s.zero_of_gtProp_leProp C (by simpa using hX) (by simpa using hY) f
  le_zero_le := by
    simpa using s.gtProp_anti C (show (-1 : ℝ) ≤ 0 by norm_num)
  ge_one_le := by
    simpa using s.leProp_mono C (show (0 : ℝ) ≤ 1 by norm_num)
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ := s.exists_phase_truncation_zero C A
    exact ⟨X, Y, by simpa using hX, by simpa using hY, f, g, h, hT⟩

@[simp]
theorem Slicing.toTStructure_heart_iff (s : Slicing C) (E : C) : (s.toTStructure C).heart E ↔ s.gtProp C 0 E ∧ s.leProp C 1 E := by
  change (s.toTStructure C).le 0 E ∧ (s.toTStructure C).ge 0 E ↔ _
  simp only [Slicing.toTStructure, Int.cast_zero, neg_zero, sub_zero]

/-- The t-structure determined by a slicing is bounded. -/
theorem Slicing.toTStructure_bounded (s : Slicing C) :
    ∀ E : C, (s.toTStructure C).bounded E := by
  intro E
  obtain ⟨F⟩ := s.hn_exists E
  by_cases hE : IsZero E
  · refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
    · exact ⟨Or.inl hE⟩
    · exact ⟨Or.inl hE⟩
  · have hn : 0 < F.n := by
      by_contra h
      exact hE (F.isZero_of_length_zero (by omega))
    let upper : ℤ := Int.floor (1 - F.phiPlus C hn)
    let lower : ℤ := Int.ceil (-(F.phiMinus C hn)) + 1
    refine ⟨⟨upper, ?_⟩, ⟨lower, ?_⟩⟩
    · refine ⟨Or.inr ⟨F, hn, ?_⟩⟩
      dsimp [upper]
      linarith [Int.floor_le (1 - F.phiPlus C hn)]
    · refine ⟨Or.inr ⟨F, hn, ?_⟩⟩
      dsimp [lower]
      have hceil := Int.le_ceil (-(F.phiMinus C hn))
      push_cast
      linarith

end CategoryTheory.Triangulated
