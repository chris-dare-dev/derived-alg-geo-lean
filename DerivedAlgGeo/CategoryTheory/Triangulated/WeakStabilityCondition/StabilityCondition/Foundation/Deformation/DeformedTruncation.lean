/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.HNExistence
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.DeformedTriangulated

/-!
# Truncation for owner deformed phase cuts

This file turns owner deformed HN filtrations into cut triangles and proves
the two old-to-deformed phase embeddings used in the global construction.
The embeddings use a two-radius margin; this avoids any boundary-equality
choice while retaining an open neighborhood of every central charge.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace CategoryTheory.Triangulated

open Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

namespace StabilityCondition.WithClassMap

/-- Splitting an owner deformed HN filtration at a real cutoff gives the
corresponding `Q(>t)/Q(≤t)` triangle. -/
theorem exists_deformedCut_triangle_of_hn
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε : ℝ} {E : C}
    (G : HNFiltration C (σ.deformedPred C W hr0 hr1 hW ε) E)
    (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y)
      (δ : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang C ∧
      σ.deformedGtPred C W hr0 hr1 hW ε t X ∧
      σ.deformedLePred C W hr0 hr1 hW ε t Y := by
  obtain ⟨X, Y, GX, GY, f, g, δ, hT, hX, hY, -⟩ :=
    G.exists_split_at_cutoff C t
  exact ⟨X, Y, f, g, δ, hT,
    ExtensionClosure.ofPostnikovTower GX.toPostnikovTower
      (fun j => ⟨GX.φ j, hX j, GX.semistable j⟩),
    ExtensionClosure.ofPostnikovTower GY.toPostnikovTower
      (fun j => ⟨GY.φ j, hY j, GY.semistable j⟩)⟩

/-- The owner deformed HN filtration of an old semistable object stays in
the closed phase window of radius `ε`.  Its factors are nonzero. -/
theorem semistable_has_tight_deformedHN
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
      (∀ j, φ - ε ≤ G.φ j ∧ G.φ j ≤ φ + ε) ∧
      ∀ j, ¬IsZero (G.factor j) := by
  obtain ⟨G, hphase, hnonzero⟩ := σ.semistable_has_deformedHN C W hr0 hr1 hW
    hε₀10 hWide hε hεε₀ hε2 hε8 hsin hP hE
  have hn : 0 < G.n := by
    by_contra h
    push Not at h
    exact hE (G.isZero_of_length_zero (by omega))
  have hinterval : ∀ j,
      σ.slicing.intervalProp C (φ - 4 * ε₀) (φ + 4 * ε₀) (G.factor j) := by
    intro j
    obtain ⟨hminus, hplus⟩ := σ.deformedPred_intrinsic_bounds C W hr0 hr1 hW
      hε hε2 hsin (G.semistable j) (hnonzero j)
    exact σ.slicing.intervalProp_of_intrinsic_phases C (hnonzero j)
      (by linarith [(hphase j).1]) (by linarith [(hphase j).2])
  let first : Fin G.n := ⟨0, hn⟩
  let last : Fin G.n := ⟨G.n - 1, by omega⟩
  have hfirstOld : σ.slicing.phiPlus C (G.factor first) (hnonzero first) ≤ φ := by
    rw [← σ.slicing.phiPlus_eq_of_semistable C E hE φ hP]
    exact G.firstFactor_phiPlus_le_target C σ.slicing hn hE (hnonzero first)
      (by linarith) hinterval
  have hlastOld : φ ≤ σ.slicing.phiMinus C (G.factor last) (hnonzero last) := by
    rw [← σ.slicing.phiMinus_eq_of_semistable C E hE φ hP]
    exact G.target_phiMinus_le_lastFactor C σ.slicing hn hE (hnonzero last)
      (by linarith) hinterval
  have hfirstBound : G.φ first ≤ φ + ε := by
    obtain ⟨hminus, -⟩ := σ.deformedPred_intrinsic_bounds C W hr0 hr1 hW
      hε hε2 hsin (G.semistable first) (hnonzero first)
    linarith [σ.slicing.phiMinus_le_phiPlus C (G.factor first) (hnonzero first)]
  have hlastBound : φ - ε ≤ G.φ last := by
    obtain ⟨-, hplus⟩ := σ.deformedPred_intrinsic_bounds C W hr0 hr1 hW
      hε hε2 hsin (G.semistable last) (hnonzero last)
    linarith [σ.slicing.phiMinus_le_phiPlus C (G.factor last) (hnonzero last)]
  refine ⟨G, fun j => ⟨?_, ?_⟩, hnonzero⟩
  · exact hlastBound.trans
      (G.hφ.antitone (Fin.mk_le_mk.mpr (by omega : j.val ≤ G.n - 1)))
  · exact (G.hφ.antitone
      (Fin.mk_le_mk.mpr (Nat.zero_le j.val))).trans hfirstBound

/-- An old semistable object at least two deformation radii above `t`
belongs to the owner cut `Q(>t)`. -/
theorem semistable_mem_deformedGt
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ t : ℝ} (hφ : t + 2 * ε ≤ φ)
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    σ.deformedGtPred C W hr0 hr1 hW ε t E := by
  obtain ⟨G, hG, -⟩ := σ.semistable_has_tight_deformedHN C W hr0 hr1 hW
    hε₀10 hWide hε hεε₀ hε2 hε8 hsin hP hE
  exact ExtensionClosure.ofPostnikovTower G.toPostnikovTower (fun j =>
    ⟨G.φ j, by linarith [(hG j).1], G.semistable j⟩)

/-- An old semistable object at least two deformation radii below `t`
belongs to the owner cut `Q(<t)`. -/
theorem semistable_mem_deformedLt
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀10 : ε₀ < 1 / 10)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεε₀ : ε < ε₀)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} {φ t : ℝ} (hφ : φ ≤ t - 2 * ε)
    (hP : σ.slicing.P φ E) (hE : ¬IsZero E) :
    σ.deformedLtPred C W hr0 hr1 hW ε t E := by
  obtain ⟨G, hG, -⟩ := σ.semistable_has_tight_deformedHN C W hr0 hr1 hW
    hε₀10 hWide hε hεε₀ hε2 hε8 hsin hP hE
  exact ExtensionClosure.ofPostnikovTower G.toPostnikovTower (fun j =>
    ⟨G.φ j, by linarith [(hG j).2], G.semistable j⟩)

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
