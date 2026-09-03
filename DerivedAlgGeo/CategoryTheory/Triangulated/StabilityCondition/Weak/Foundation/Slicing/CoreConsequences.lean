/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.IntrinsicPhaseBounds
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseShift

/-!
# Core consequences of the owner slicing API

This file collects phase-cut vanishing and intrinsic-extrema consequences
used throughout the stability-condition development.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace CategoryTheory.Triangulated

namespace HNFiltration

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- If every map from the first HN factor to the filtered object is zero, that factor is zero. -/
theorem isZero_factor_zero_of_hom_eq_zero (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n)
    (hzero : ∀ f : F.factor ⟨0, hn⟩ ⟶ E, f = 0) :
    IsZero (F.factor ⟨0, hn⟩) :=
  F.firstFactor_isZero_of_hom_eq_zero C s hn hzero

/-- If every map from the filtered object to its last HN factor is zero, that factor is zero. -/
theorem isZero_factor_last_of_hom_eq_zero (s : Slicing C) {E : C}
    (F : HNFiltration C s.P E) (hn : 0 < F.n)
    (hzero : ∀ f : E ⟶ F.factor ⟨F.n - 1, by omega⟩, f = 0) :
    IsZero (F.factor ⟨F.n - 1, by omega⟩) :=
  F.lastFactor_isZero_of_hom_eq_zero C s hn hzero

end HNFiltration

namespace Slicing

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A morphism from phases strictly above a cut to phases at or below it vanishes. -/
theorem zero_of_gtProp_leProp_general (s : Slicing C) (t : ℝ) {X Y : C}
    (hX : s.gtProp C t X) (hY : s.leProp C t Y) (f : X ⟶ Y) : f = 0 := by
  exact (s.phaseShift C t).zero_of_gtProp_leProp C
    ((s.phaseShift_gtProp_zero C t X).mpr hX)
    ((s.phaseShift_leProp_zero C t Y).mpr hY) f

/-- A morphism from phases at or above a cut to phases strictly below it vanishes. -/
theorem zero_of_geProp_ltProp_general (s : Slicing C) (t : ℝ) {X Y : C}
    (hX : s.geProp C t X) (hY : s.ltProp C t Y) (f : X ⟶ Y) : f = 0 := by
  exact (s.phaseShift C t).zero_of_geProp_ltProp C
    ((s.phaseShift_geProp_zero C t X).mpr hX)
    ((s.phaseShift_ltProp_zero C t Y).mpr hY) f

/-- **Orthogonality characterizes the lower phase cut.**  An object with no
nonzero morphism to any object of phases below `t` has all its HN phases at
least `t`.  Take a filtration with nonzero boundary factors; if the lowest
phase were below `t`, the last factor would itself lie in `𝒫(< t)`, so the
hypothesis kills every map onto it and
`HNFiltration.lastFactor_isZero_of_hom_eq_zero` makes it zero, contradicting
the choice of filtration.  This is the converse of
`Slicing.zero_of_geProp_ltProp_general`, and it is the step that turns a
Hom-vanishing computation into membership in `𝒫(≥ t)`. -/
theorem geProp_of_forall_hom_eq_zero (s : Slicing C) (t : ℝ) {E : C}
    (hE : ∀ G : C, s.ltProp C t G → ∀ g : E ⟶ G, g = 0) : s.geProp C t E := by
  by_cases hz : IsZero E
  · exact s.geProp_of_isZero C hz t
  obtain ⟨F, hn, -, hlast⟩ := s.exists_hn_nonzero_boundaries C hz
  refine Or.inr ⟨F, hn, ?_⟩
  by_contra hlt
  push Not at hlt
  apply hlast
  apply F.lastFactor_isZero_of_hom_eq_zero C s hn
  intro g
  refine hE _ ?_ g
  exact s.ltProp_of_hn C (HNFiltration.single C (F.factor ⟨F.n - 1, by omega⟩)
      (F.φ ⟨F.n - 1, by omega⟩) (F.semistable ⟨F.n - 1, by omega⟩)) t
    (fun _ => by simpa [HNFiltration.single, HNFiltration.phiMinus] using hlt)
    (by change 0 < 1; omega)

/-- A nonzero semistable object's two intrinsic phase extrema equal its phase. -/
theorem phiPlus_eq_phiMinus_of_semistable (s : Slicing C) {E : C} {φ : ℝ}
    (hP : s.P φ E) (hE : ¬IsZero E) :
    s.phiPlus C E hE = φ ∧ s.phiMinus C E hE = φ :=
  ⟨s.phiPlus_eq_of_semistable C E hE φ hP,
    s.phiMinus_eq_of_semistable C E hE φ hP⟩

/-- Equal intrinsic endpoints force a nonzero object to be semistable. -/
theorem semistable_of_phiPlus_eq_phiMinus (s : Slicing C) {E : C}
    (hE : ¬IsZero E) (heq : s.phiPlus C E hE = s.phiMinus C E hE) :
    s.P (s.phiPlus C E hE) E := by
  obtain ⟨F, hn, hfirst, hlast⟩ := s.exists_hn_nonzero_boundaries C hE
  have hplus := (s.phiPlus_eq C E hE F hn hfirst).symm
  have hminus := (s.phiMinus_eq C E hE F hn hlast).symm
  have hn_eq : F.n = 1 := by
    by_contra hne
    have hn_two : 2 ≤ F.n := by omega
    have hlast_lt : F.n - 1 < F.n := by omega
    have hplus' : F.φ ⟨0, hn⟩ = s.phiPlus C E hE := by
      simpa only [HNFiltration.phiPlus] using hplus
    have hminus' : F.φ ⟨F.n - 1, hlast_lt⟩ = s.phiMinus C E hE := by
      simpa only [HNFiltration.phiMinus] using hminus
    have hphase_eq : F.φ ⟨0, hn⟩ = F.φ ⟨F.n - 1, hlast_lt⟩ := by
      exact hplus'.trans (heq.trans hminus'.symm)
    have hphase_lt : F.φ ⟨F.n - 1, hlast_lt⟩ < F.φ ⟨0, hn⟩ :=
      F.hφ (Fin.mk_lt_mk.mpr (by omega))
    exact hphase_lt.ne hphase_eq.symm
  let T := F.triangle ⟨0, hn⟩
  have hzero : IsZero T.obj₁ :=
    IsZero.of_iso F.base_isZero (Classical.choice (F.triangle_obj₁ ⟨0, hn⟩))
  letI : IsIso T.mor₂ :=
    (Triangle.isZero₁_iff_isIso₂ T (F.triangle_dist ⟨0, hn⟩)).mp hzero
  have hobj₂ : F.chain.obj' (0 + 1) (by omega) = F.chain.obj (Fin.last F.n) :=
    congrArg F.chain.obj (Fin.ext (by simp [Fin.last]; omega))
  let e : T.obj₂ ≅ E :=
    (Classical.choice (F.triangle_obj₂ ⟨0, hn⟩)).trans
      ((eqToIso hobj₂).trans (Classical.choice F.top_iso))
  exact (s.P _).prop_of_iso (e.symm.trans (asIso T.mor₂)).symm (by
    rw [← hplus]
    exact F.semistable ⟨0, hn⟩)

/-- The zero object lies strictly above every phase cut by the zero disjunct. -/
theorem gtProp_zero (s : Slicing C) (t : ℝ) : s.gtProp C t (0 : C) :=
  Or.inl (isZero_zero C)

/-- The zero object lies weakly below every phase cut by the zero disjunct. -/
theorem leProp_zero (s : Slicing C) (t : ℝ) : s.leProp C t (0 : C) :=
  Or.inl (isZero_zero C)

/-- Split an HN filtration at a cutoff while retaining an upper bound on the first piece. -/
theorem exists_split_at_cutoff_with_upper_bound [IsTriangulated C]
    (s : Slicing C) {E : C} (F : HNFiltration C s.P E)
    {a b t : ℝ} (hI : ∀ i : Fin F.n, a < F.φ i ∧ F.φ i < b)
    (_hn : 0 < F.n) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C ∧
      s.gtProp C t X ∧ s.leProp C t Y ∧
      (∀ hX : ¬IsZero X, s.phiPlus C X hX < b) := by
  obtain ⟨X, Y, GX, GY, f, g, h, hT, hGX, hGY, -, hsource⟩ :=
    F.exists_split_at_cutoff C t
  have hXgt : s.gtProp C t X := by
    by_cases hX : IsZero X
    · exact Or.inl hX
    · exact s.gtProp_of_hn C GX t hGX (GX.n_pos C hX)
  have hYle : s.leProp C t Y := by
    by_cases hY : IsZero Y
    · exact Or.inl hY
    · exact s.leProp_of_hn C GY t hGY (GY.n_pos C hY)
  refine ⟨X, Y, f, g, h, hT, hXgt, hYle, fun hX => ?_⟩
  apply s.phiPlus_lt_of_intervalProp C hX
  exact Or.inr ⟨GX, fun j => by
    obtain ⟨i, hi⟩ := hsource j
    rw [hi]
    exact hI i⟩

/-- Semistability of phase `φ`, cut into the two one-sided conditions the Ind-extensions read
off a t-structure.  The upper cut is `∀ ψ > φ, ltProp ψ` rather than the single `leProp φ`
because `Slicing.IndExtensions.isGE_one_iff_ltProp` delivers `ltProp`; the two agree here only
after the fact, since `φ ≤ φ⁻ ≤ φ⁺ ≤ φ` squeezes both intrinsic phases onto `φ`.  Only `←` is
new: `→` is `geProp_of_semistable` together with `ltProp_of_leProp_of_lt` applied to
`leProp_of_semistable`. -/
theorem semistable_iff_geProp_ltProp (s : Slicing C) (φ : ℝ) (Z : C) :
    s.P φ Z ↔ (s.geProp C φ Z ∧ ∀ ψ, φ < ψ → s.ltProp C ψ Z) := by
  constructor
  · intro hZ
    exact ⟨s.geProp_of_semistable C hZ,
      fun ψ hψ => s.ltProp_of_leProp_of_lt C hψ Z (s.leProp_of_semistable C hZ le_rfl)⟩
  · rintro ⟨hge, hlt⟩
    by_cases hZ : IsZero Z
    · exact s.zero_mem_of_isZero C φ Z hZ
    · have h1 : φ ≤ s.phiMinus C Z hZ := s.phiMinus_ge_of_geProp C hZ hge
      have h2 : s.phiPlus C Z hZ ≤ φ := by
        by_contra hcon
        push Not at hcon
        exact lt_irrefl _ (s.phiPlus_lt_of_ltProp C hZ (hlt _ hcon))
      have h3 := s.phiMinus_le_phiPlus C Z hZ
      have heq : s.phiPlus C Z hZ = s.phiMinus C Z hZ := le_antisymm (h2.trans h1) h3
      have hsemi := Slicing.semistable_of_phiPlus_eq_phiMinus C s hZ heq
      rwa [show s.phiPlus C Z hZ = φ from le_antisymm h2 (h1.trans h3)] at hsemi

end Slicing

end CategoryTheory.Triangulated
