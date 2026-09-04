/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.Deformation.PhaseArithmetic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.Slicing.PhaseBounds
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.StabilityCondition

/-!
# Skewed stability data on an owner interval

A perturbed charge need not itself define a stability condition yet.  On a
thin interval it supplies a skewed phase whenever it is nonzero on the old
semistable factors.  This module owns that intermediate object and its
triangle-additive phase comparisons.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- A perturbed central charge on the owner interval `P((a,b))`, with a branch
centre and nonvanishing on the original semistable factors in that interval. -/
structure SkewedStabilityFunction (s : Slicing C) (a b : ℝ) where
  /-- The perturbed central charge. -/
  W : Λ →+ ℂ
  /-- The centre of the chosen phase branch. -/
  α : ℝ
  /-- The branch centre lies in the interval. -/
  centre_mem : a < α ∧ α < b
  /-- The perturbed charge does not vanish on old nonzero semistable factors. -/
  nonzero : ∀ (E : C) (φ : ℝ), a < φ → φ < b →
    s.P φ E → ¬IsZero E → W (classOf C v E) ≠ 0

namespace SkewedStabilityFunction

variable {C v} {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}
variable {s : Slicing C} {a b : ℝ}

/-- The perturbed charge of an ambient object. -/
abbrev charge (F : SkewedStabilityFunction C κ s a b) (E : C) : ℂ :=
  F.W (classOf C κ E)

/-- The perturbed phase on the branch selected by the skewed data. -/
abbrev phase (F : SkewedStabilityFunction C κ s a b) (E : C) : ℝ :=
  relativePhase (F.charge E) F.α

/-- Nonvanishing of an object's perturbed charge. -/
abbrev ChargeNe (F : SkewedStabilityFunction C κ s a b) (E : C) : Prop :=
  F.charge E ≠ 0

/-- Equal perturbed charges have equal phases. -/
theorem phase_congr (F : SkewedStabilityFunction C κ s a b) {E E' : C}
    (h : F.charge E = F.charge E') : F.phase E = F.phase E' := by
  simp only [phase, h]

/-- Isomorphic objects have equal perturbed phases. -/
theorem phase_iso (F : SkewedStabilityFunction C κ s a b) {E E' : C}
    (e : E ≅ E') : F.phase E = F.phase E' :=
  F.phase_congr (congrArg F.W (classOf_iso C κ e))

/-- Perturbed charges are additive along distinguished triangles. -/
theorem charge_triangle (F : SkewedStabilityFunction C κ s a b)
    (T : Triangle C) (hT : T ∈ distTriang C) :
    F.charge T.obj₂ = F.charge T.obj₁ + F.charge T.obj₃ := by
  simp only [charge, classOf_triangle C κ T hT, map_add]

/-- The charge-level phase see-saw for ambient objects. -/
theorem phase_seesaw (F : SkewedStabilityFunction C κ s a b)
    {E E₁ E₂ : C} {ψ : ℝ}
    (hsum : F.charge E₁ + F.charge E₂ = F.charge E)
    (hψ : F.phase E = ψ)
    (hE₁_range : F.phase E₁ ∈ Set.Ioc (ψ - 1) ψ)
    (hE₂_ne : F.ChargeNe E₂)
    (hE₂_range : F.phase E₂ ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ ≤ F.phase E₂ :=
  relativePhase_seesaw hsum hψ hE₁_range hE₂_ne hE₂_range

/-- Strict charge-level phase see-saw for ambient objects. -/
theorem phase_seesaw_strict (F : SkewedStabilityFunction C κ s a b)
    {E E₁ E₂ : C} {ψ : ℝ}
    (hsum : F.charge E₁ + F.charge E₂ = F.charge E)
    (hψ : F.phase E = ψ)
    (hE₂_lt : F.phase E₂ < ψ)
    (hE₂_ne : F.ChargeNe E₂)
    (hE₂_range : F.phase E₂ ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hE₁_range : F.phase E₁ ∈ Set.Ioo (ψ - 1) (ψ + 1)) :
    ψ < F.phase E₁ :=
  relativePhase_seesaw_strict hsum hψ hE₂_lt hE₂_ne
    hE₂_range hE₁_range

/-- An interval object is semistable for the perturbed charge when every
admissible nonzero subobject triangle has phase at most its phase. -/
structure IsSemistable (F : SkewedStabilityFunction C κ s a b)
    (E : C) (ψ : ℝ) : Prop where
  /-- The object lies in the old thin interval. -/
  interval : s.intervalProp C a b E
  /-- The object is nonzero. -/
  nonzero : ¬IsZero E
  /-- Its perturbed charge is nonzero. -/
  charge_ne : F.ChargeNe E
  /-- Its chosen perturbed phase is `ψ`. -/
  phase_eq : F.phase E = ψ
  /-- Every nonzero subobject represented by an interval triangle has phase at
  most `ψ`. -/
  phase_le_of_triangle : ∀ ⦃K Q : C⦄ ⦃i : K ⟶ E⦄ ⦃q : E ⟶ Q⦄
    ⦃δ : Q ⟶ K⟦(1 : ℤ)⟧⦄,
    Triangle.mk i q δ ∈ distTriang C →
    s.intervalProp C a b K → s.intervalProp C a b Q →
    ¬IsZero K → F.phase K ≤ ψ

/-- A nonzero quotient in an admissible interval triangle has phase at least
that of a skewed-semistable object, provided all three selected phases lie on
the same branch. -/
theorem IsSemistable.phase_le_of_quotient_triangle
    {F : SkewedStabilityFunction C κ s a b} {E : C} {ψ : ℝ}
    (h : F.IsSemistable E ψ) {K Q : C}
    {i : K ⟶ E} {q : E ⟶ Q} {δ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk i q δ ∈ distTriang C)
    (hQcharge : F.ChargeNe Q)
    (hQrange : F.phase Q ∈ Set.Ioo (ψ - 1) (ψ + 1))
    (hKrange : ∀ _ : ¬IsZero K, F.phase K ∈ Set.Ioc (ψ - 1) ψ) :
    ψ ≤ F.phase Q := by
  have hsum : F.charge K + F.charge Q = F.charge E :=
    (F.charge_triangle (Triangle.mk i q δ) hT).symm
  by_cases hKne : IsZero K
  · have hKcharge : F.charge K = 0 := by
      simp only [charge, classOf_isZero C κ hKne, map_zero]
    have hQE : F.charge Q = F.charge E := by
      simpa [hKcharge] using hsum
    exact le_of_eq ((F.phase_congr hQE).trans h.phase_eq).symm
  · exact F.phase_seesaw hsum h.phase_eq (hKrange hKne) hQcharge hQrange

/-- A perturbed-semistable object's phase lies on its chosen branch. -/
theorem IsSemistable.phase_mem_Ioc {F : SkewedStabilityFunction C κ s a b}
    {E : C} {ψ : ℝ} (h : F.IsSemistable E ψ) :
    ψ ∈ Set.Ioc (F.α - 1) (F.α + 1) := by
  rw [← h.phase_eq]
  exact relativePhase_mem_Ioc _ _

/-- Polar form of the charge of a perturbed-semistable object. -/
theorem IsSemistable.charge_polar {F : SkewedStabilityFunction C κ s a b}
    {E : C} {ψ : ℝ} (h : F.IsSemistable E ψ) :
    F.charge E = (‖F.charge E‖ : ℂ) *
      Complex.exp (↑(Real.pi * ψ) * Complex.I) := by
  rw [← h.phase_eq]
  exact relativePhase_polar _ _

/-- Transport perturbed semistability across an isomorphism of ambient
objects. -/
theorem IsSemistable.ofIso {F : SkewedStabilityFunction C κ s a b}
    {E E' : C} {ψ : ℝ} (h : F.IsSemistable E ψ) (e : E ≅ E') :
    F.IsSemistable E' ψ where
  interval := by
    rcases h.interval with hzero | ⟨G, hG⟩
    · exact Or.inl ((Iso.isZero_iff e).mp hzero)
    · exact Or.inr ⟨G.ofIso C e, fun i => by
        simpa [HNFiltration.ofIso] using hG i⟩
  nonzero hE' := h.nonzero ((Iso.isZero_iff e).mpr hE')
  charge_ne := by
    change F.W (classOf C κ E') ≠ 0
    rw [← classOf_iso C κ e]
    exact h.charge_ne
  phase_eq := by
    rw [← F.phase_iso e]
    exact h.phase_eq
  phase_le_of_triangle := by
    intro K Q i q δ hT hK hQ hKne
    have hT' : Triangle.mk (i ≫ e.inv) (e.hom ≫ q) δ ∈ distTriang C := by
      unfold Triangle.mk at hT ⊢
      exact isomorphic_distinguished _ hT _
        (Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _)
          (by simp) (by simp) (by simp))
    exact h.phase_le_of_triangle hT' hK hQ hKne

/-- Transport skewed semistability to a second interval presentation once
the admissible triangles widen to the old interval and the selected phases
agree on the ambient object and every nonzero candidate subobject. -/
theorem IsSemistable.ofCompatibleInterval
    {c d : ℝ} {F : SkewedStabilityFunction C κ s a b}
    {G : SkewedStabilityFunction C κ s c d}
    {E : C} {ψ : ℝ} (h : F.IsSemistable E ψ)
    (hI : s.intervalProp C c d E)
    (hmono : s.intervalProp C c d ≤ s.intervalProp C a b)
    (hcharge : G.charge E = F.charge E)
    (hphaseE : G.phase E = F.phase E)
    (hphaseSub : ∀ {K : C}, s.intervalProp C c d K → ¬IsZero K →
      G.phase K = F.phase K) :
    G.IsSemistable E ψ where
  interval := hI
  nonzero := h.nonzero
  charge_ne := by
    change G.charge E ≠ 0
    rw [hcharge]
    exact h.charge_ne
  phase_eq := hphaseE.trans h.phase_eq
  phase_le_of_triangle := by
    intro K Q i q δ hT hK hQ hKne
    rw [hphaseSub hK hKne]
    exact h.phase_le_of_triangle hT (hmono K hK) (hmono Q hQ) hKne

end SkewedStabilityFunction

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Deformation
