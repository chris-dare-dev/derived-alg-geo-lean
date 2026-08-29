/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.DeformedCuts

/-!
# Shift equivariance of owner deformed phase cuts

Shifting an object by one translates its owner deformed phase by one.  The
same operation preserves the provisional extension-closed cuts after
translating their cutoff.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

/-- Forward shift for the owner deformed predicate. -/
theorem deformedPred_shift_one
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} {X : C}
    (h : σ.deformedPred C W hr0 hr1 hW ε ψ X) :
    σ.deformedPred C W hr0 hr1 hW ε (ψ + 1) (X⟦(1 : ℤ)⟧) := by
  rcases h with hzero | ⟨a, b, hab, hthin, hlo, hhi, hSS⟩
  · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hzero)
  · refine Or.inr ⟨a + 1, b + 1, by linarith, by linarith,
      by linarith, by linarith, ?_⟩
    let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
    let F' := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW
      (show a + 1 < b + 1 by linarith)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rcases hSS.interval with hZ | ⟨G, hG⟩
      · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
      · exact Or.inr ⟨G.shift C σ.slicing 1, fun i => by
          simp only [HNFiltration.shift, Int.cast_one]
          exact ⟨by simpa only [add_lt_add_iff_right] using (hG i).1,
            by simpa only [add_lt_add_iff_right] using (hG i).2⟩⟩
    · exact fun hZ => hSS.nonzero
        (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) X hZ)
    · change W (classOf C κ (X⟦(1 : ℤ)⟧)) ≠ 0
      rw [classOf_shift_one, map_neg]
      exact neg_ne_zero.mpr hSS.charge_ne
    · change relativePhase (W (classOf C κ (X⟦(1 : ℤ)⟧)))
          ((a + 1 + (b + 1)) / 2) = ψ + 1
      rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 by ring,
        classOf_shift_one, map_neg]
      exact (relativePhase_neg hSS.charge_ne ((a + b) / 2)).trans
        (by change F.phase X + 1 = ψ + 1; rw [hSS.phase_eq])
    · intro K Q i q δ hT hK hQ hKne
      have hTshift := Triangle.shift_distinguished _ hT (-1 : ℤ)
      have hsum : (1 : ℤ) + (-1 : ℤ) = 0 := by omega
      let eX := (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) hsum).app X
      let shifted := (Triangle.shiftFunctor C (-1)).obj (Triangle.mk i q δ)
      let T := Triangle.mk (shifted.mor₁ ≫ eX.hom)
        (eX.inv ≫ shifted.mor₂) shifted.mor₃
      have hT' : T ∈ distTriang C := by
        unfold T Triangle.mk
        exact isomorphic_distinguished _ hTshift _
          (Triangle.isoMk _ shifted (Iso.refl _) eX.symm (Iso.refl _)
            (by simp)
            (by change (eX.inv ≫ shifted.mor₂) ≫ 𝟙 _ =
                eX.symm.hom ≫ shifted.mor₂; simp [Iso.symm])
            (by simp))
      have hK' : σ.slicing.intervalProp C a b (K⟦(-1 : ℤ)⟧) := by
        rcases hK with hZ | ⟨G, hG⟩
        · exact Or.inl ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
        · exact Or.inr ⟨G.shift C σ.slicing (-1), fun j => by
            simp only [HNFiltration.shift, Int.cast_neg, Int.cast_one]
            exact ⟨by linarith [(hG j).1], by linarith [(hG j).2]⟩⟩
      have hQ' : σ.slicing.intervalProp C a b (Q⟦(-1 : ℤ)⟧) := by
        rcases hQ with hZ | ⟨G, hG⟩
        · exact Or.inl ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
        · exact Or.inr ⟨G.shift C σ.slicing (-1), fun j => by
            simp only [HNFiltration.shift, Int.cast_neg, Int.cast_one]
            exact ⟨by linarith [(hG j).1], by linarith [(hG j).2]⟩⟩
      have hKne' : ¬IsZero (K⟦(-1 : ℤ)⟧) := fun hZ =>
        hKne (IsZero.of_full_of_faithful_of_isZero
          (shiftFunctor C (-1 : ℤ)) K hZ)
      have hphase : F.phase (K⟦(-1 : ℤ)⟧) ≤ ψ :=
        hSS.phase_le_of_triangle hT' hK' hQ' hKne'
      change relativePhase (W (classOf C κ K)) ((a + 1 + (b + 1)) / 2) ≤ ψ + 1
      rw [show (a + 1 + (b + 1)) / 2 = (a + b) / 2 + 1 by ring]
      change relativePhase (W (classOf C κ (K⟦(-1 : ℤ)⟧))) ((a + b) / 2) ≤ ψ at hphase
      rw [classOf_shift_neg_one, map_neg] at hphase
      by_cases hWK : W (classOf C κ K) = 0
      · simp [hWK] at hphase ⊢
        linarith
      · have hneg := relativePhase_neg hWK ((a + b) / 2 - 1)
        have hperiod := relativePhase_add_two hWK ((a + b) / 2 - 1)
        rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 by ring] at hneg
        rw [show (a + b) / 2 - 1 + 2 = (a + b) / 2 + 1 by ring] at hperiod
        linarith

/-- Converse to forward shift for the owner deformed predicate. -/
theorem deformedPred_of_shift_one
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} {X : C}
    (h : σ.deformedPred C W hr0 hr1 hW ε (ψ + 1) (X⟦(1 : ℤ)⟧)) :
    σ.deformedPred C W hr0 hr1 hW ε ψ X := by
  rcases h with hzero | ⟨a, b, hab, hthin, hlo, hhi, hSS⟩
  · exact Or.inl
      (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) X hzero)
  · refine Or.inr ⟨a - 1, b - 1, by linarith, by linarith,
      by linarith, by linarith, ?_⟩
    let F := skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rcases hSS.interval with hZ | ⟨G, hG⟩
      · exact absurd hZ hSS.nonzero
      · let eX := (shiftFunctorCompIsoId C (1 : ℤ) (-1 : ℤ) (by omega)).app X
        exact Or.inr ⟨(G.shift C σ.slicing (-1)).ofIso C eX, fun i => by
          change a - 1 < (G.shift C σ.slicing (-1)).φ i ∧
            (G.shift C σ.slicing (-1)).φ i < b - 1
          simp only [HNFiltration.shift, Int.cast_neg, Int.cast_one]
          exact ⟨by linarith [(hG i).1], by linarith [(hG i).2]⟩⟩
    · exact fun hZ => hSS.nonzero ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
    · intro hzero
      change W (classOf C κ X) = 0 at hzero
      apply hSS.charge_ne
      change W (classOf C κ (X⟦(1 : ℤ)⟧)) = 0
      rw [classOf_shift_one, map_neg, hzero, neg_zero]
    · change relativePhase (W (classOf C κ X)) ((a - 1 + (b - 1)) / 2) = ψ
      rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 by ring]
      have hphase := hSS.phase_eq
      change relativePhase (W (classOf C κ (X⟦(1 : ℤ)⟧))) ((a + b) / 2) =
        ψ + 1 at hphase
      rw [classOf_shift_one, map_neg] at hphase
      have hWne : W (classOf C κ X) ≠ 0 := by
        intro hzero
        apply hSS.charge_ne
        change W (classOf C κ (X⟦(1 : ℤ)⟧)) = 0
        rw [classOf_shift_one, map_neg, hzero, neg_zero]
      have hneg := relativePhase_neg hWne ((a + b) / 2 - 1)
      rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 by ring] at hneg
      linarith
    · intro K Q i q δ hT hK hQ hKne
      have hT' := Triangle.shift_distinguished _ hT (1 : ℤ)
      have hK' : σ.slicing.intervalProp C a b (K⟦(1 : ℤ)⟧) := by
        rcases hK with hZ | ⟨G, hG⟩
        · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
        · exact Or.inr ⟨G.shift C σ.slicing 1, fun j => by
            simp only [HNFiltration.shift, Int.cast_one]
            exact ⟨by linarith [(hG j).1], by linarith [(hG j).2]⟩⟩
      have hQ' : σ.slicing.intervalProp C a b (Q⟦(1 : ℤ)⟧) := by
        rcases hQ with hZ | ⟨G, hG⟩
        · exact Or.inl ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
        · exact Or.inr ⟨G.shift C σ.slicing 1, fun j => by
            simp only [HNFiltration.shift, Int.cast_one]
            exact ⟨by linarith [(hG j).1], by linarith [(hG j).2]⟩⟩
      have hKne' : ¬IsZero (K⟦(1 : ℤ)⟧) := fun hZ =>
        hKne (IsZero.of_full_of_faithful_of_isZero (shiftFunctor C (1 : ℤ)) K hZ)
      have hphase : F.phase (K⟦(1 : ℤ)⟧) ≤ ψ + 1 :=
        hSS.phase_le_of_triangle hT' hK' hQ' hKne'
      change relativePhase (W (classOf C κ K)) ((a - 1 + (b - 1)) / 2) ≤ ψ
      rw [show (a - 1 + (b - 1)) / 2 = (a + b) / 2 - 1 by ring]
      change relativePhase (W (classOf C κ (K⟦(1 : ℤ)⟧))) ((a + b) / 2) ≤
        ψ + 1 at hphase
      rw [classOf_shift_one, map_neg] at hphase
      by_cases hWK : W (classOf C κ K) = 0
      · simp [hWK] at hphase ⊢
        linarith
      · have hneg := relativePhase_neg hWK ((a + b) / 2 - 1)
        rw [show (a + b) / 2 - 1 + 1 = (a + b) / 2 by ring] at hneg
        linarith

/-- Backward shift for the owner deformed predicate. -/
theorem deformedPred_shift_neg_one
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ : ℝ} {X : C}
    (h : σ.deformedPred C W hr0 hr1 hW ε ψ X) :
    σ.deformedPred C W hr0 hr1 hW ε (ψ - 1) (X⟦(-1 : ℤ)⟧) := by
  let Y := X⟦(-1 : ℤ)⟧
  let e : Y⟦(1 : ℤ)⟧ ≅ X :=
    (shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by omega)).app X
  letI := σ.deformedPred_isClosedUnderIsomorphisms C W hr0 hr1 hW ε ψ
  have hY : σ.deformedPred C W hr0 hr1 hW ε ψ (Y⟦(1 : ℤ)⟧) :=
    ObjectProperty.prop_of_iso _ e.symm h
  apply σ.deformedPred_of_shift_one C W hr0 hr1 hW
  simpa only [sub_add_cancel] using hY

/-- Forward shift preserves the provisional cut `Q(>t)`. -/
theorem deformedGtPred_shift_one
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X : C} (hX : σ.deformedGtPred C W hr0 hr1 hW ε t X) :
    σ.deformedGtPred C W hr0 hr1 hW ε (t + 1) (X⟦(1 : ℤ)⟧) := by
  induction hX with
  | zero hZ => exact .zero ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
  | mem hP =>
      obtain ⟨ψ, hψ, hPred⟩ := hP
      exact .mem ⟨ψ + 1, by linarith,
        σ.deformedPred_shift_one C W hr0 hr1 hW hPred⟩
  | ext hT _ _ ihX ihY =>
      exact .ext (Triangle.shift_distinguished _ hT (1 : ℤ)) ihX ihY

/-- Backward shift preserves the provisional cut `Q(>t)`. -/
theorem deformedGtPred_shift_neg_one
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X : C} (hX : σ.deformedGtPred C W hr0 hr1 hW ε t X) :
    σ.deformedGtPred C W hr0 hr1 hW ε (t - 1) (X⟦(-1 : ℤ)⟧) := by
  induction hX with
  | zero hZ => exact .zero ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
  | mem hP =>
      obtain ⟨ψ, hψ, hPred⟩ := hP
      exact .mem ⟨ψ - 1, by linarith,
        σ.deformedPred_shift_neg_one C W hr0 hr1 hW hPred⟩
  | ext hT _ _ ihX ihY =>
      exact .ext (Triangle.shift_distinguished _ hT (-1 : ℤ)) ihX ihY

/-- Forward shift preserves the provisional cut `Q(≤t)`. -/
theorem deformedLePred_shift_one
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X : C} (hX : σ.deformedLePred C W hr0 hr1 hW ε t X) :
    σ.deformedLePred C W hr0 hr1 hW ε (t + 1) (X⟦(1 : ℤ)⟧) := by
  induction hX with
  | zero hZ => exact .zero ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
  | mem hP =>
      obtain ⟨ψ, hψ, hPred⟩ := hP
      exact .mem ⟨ψ + 1, by linarith,
        σ.deformedPred_shift_one C W hr0 hr1 hW hPred⟩
  | ext hT _ _ ihX ihY =>
      exact .ext (Triangle.shift_distinguished _ hT (1 : ℤ)) ihX ihY

/-- Backward shift preserves the provisional cut `Q(≤t)`. -/
theorem deformedLePred_shift_neg_one
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X : C} (hX : σ.deformedLePred C W hr0 hr1 hW ε t X) :
    σ.deformedLePred C W hr0 hr1 hW ε (t - 1) (X⟦(-1 : ℤ)⟧) := by
  induction hX with
  | zero hZ => exact .zero ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
  | mem hP =>
      obtain ⟨ψ, hψ, hPred⟩ := hP
      exact .mem ⟨ψ - 1, by linarith,
        σ.deformedPred_shift_neg_one C W hr0 hr1 hW hPred⟩
  | ext hT _ _ ihX ihY =>
      exact .ext (Triangle.shift_distinguished _ hT (-1 : ℤ)) ihX ihY

/-- Forward shift preserves the provisional cut `Q(<t)`. -/
theorem deformedLtPred_shift_one
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X : C} (hX : σ.deformedLtPred C W hr0 hr1 hW ε t X) :
    σ.deformedLtPred C W hr0 hr1 hW ε (t + 1) (X⟦(1 : ℤ)⟧) := by
  induction hX with
  | zero hZ => exact .zero ((shiftFunctor C (1 : ℤ)).map_isZero hZ)
  | mem hP =>
      obtain ⟨ψ, hψ, hPred⟩ := hP
      exact .mem ⟨ψ + 1, by linarith,
        σ.deformedPred_shift_one C W hr0 hr1 hW hPred⟩
  | ext hT _ _ ihX ihY =>
      exact .ext (Triangle.shift_distinguished _ hT (1 : ℤ)) ihX ihY

/-- Backward shift preserves the provisional cut `Q(<t)`. -/
theorem deformedLtPred_shift_neg_one
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t : ℝ} {X : C} (hX : σ.deformedLtPred C W hr0 hr1 hW ε t X) :
    σ.deformedLtPred C W hr0 hr1 hW ε (t - 1) (X⟦(-1 : ℤ)⟧) := by
  induction hX with
  | zero hZ => exact .zero ((shiftFunctor C (-1 : ℤ)).map_isZero hZ)
  | mem hP =>
      obtain ⟨ψ, hψ, hPred⟩ := hP
      exact .mem ⟨ψ - 1, by linarith,
        σ.deformedPred_shift_neg_one C W hr0 hr1 hW hPred⟩
  | ext hT _ _ ihX ihY =>
      exact .ext (Triangle.shift_distinguished _ hT (-1 : ℤ)) ihX ihY

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
