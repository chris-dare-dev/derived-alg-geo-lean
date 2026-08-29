/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Foundation.Deformation.DeformedTruncation

/-!
# Global truncation for the owner deformed phase cuts

Every object is split into old high, middle, and low phase pieces.  The high
and low pieces enter the corresponding deformed cuts by the two-radius
embedding lemmas.  The middle piece lies in one of the uniformly finite
wide sectors and therefore has an owner deformed HN filtration.  Two uses of
the octahedral axiom assemble the three pieces.
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

/-- Every object has a truncation triangle for the owner provisional
deformed phase cuts. -/
theorem exists_global_deformedCut_triangle
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε₀ : ℝ} (hε₀16 : ε₀ < 1 / 16)
    (hWide : WideSectorFiniteLength C σ ε₀)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < ε₀ / 2)
    (hε2 : ε ≤ 1 / 2) (hε8 : ε < 1 / 8)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (E : C) (t : ℝ) :
    ∃ (X Y : C) (f : X ⟶ E) (g : E ⟶ Y)
      (δ : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g δ ∈ distTriang C ∧
      σ.deformedGtPred C W hr0 hr1 hW ε t X ∧
      σ.deformedLePred C W hr0 hr1 hW ε t Y := by
  have hεε₀ : ε < ε₀ := by linarith
  have hε₀10 : ε₀ < 1 / 10 := by linarith
  obtain ⟨F⟩ := σ.slicing.hn_exists E
  obtain ⟨HIGH, REST, GH, GR, fH, gR, δR, hTR,
      hHIGHphase, hRESTphase, -, -⟩ :=
    F.exists_split_at_cutoff C (t + 2 * ε)
  obtain ⟨MID, LOW, GM, GLOW, fM, gL, δL, hTL,
      hMIDphase, hLOWphase, -, hMIDorigin⟩ :=
    GR.exists_split_at_cutoff C (t - 2 * ε)
  have collapseGt : ExtensionClosure
      (σ.deformedGtPred C W hr0 hr1 hW ε t) ≤
      σ.deformedGtPred C W hr0 hr1 hW ε t :=
    ExtensionClosure.le_of_closed
      (fun hzero => .zero hzero) (fun _ h => h)
      (fun hT hX hY => .ext hT hX hY)
  have collapseLe : ExtensionClosure
      (σ.deformedLePred C W hr0 hr1 hW ε t) ≤
      σ.deformedLePred C W hr0 hr1 hW ε t :=
    ExtensionClosure.le_of_closed
      (fun hzero => .zero hzero) (fun _ h => h)
      (fun hT hX hY => .ext hT hX hY)
  have hHIGH : σ.deformedGtPred C W hr0 hr1 hW ε t HIGH := by
    apply collapseGt
    exact ExtensionClosure.ofPostnikovTower GH.toPostnikovTower (fun j => by
      by_cases hj : IsZero (GH.factor j)
      · exact .zero hj
      · exact σ.semistable_mem_deformedGt C W hr0 hr1 hW hε₀10
          hWide hε hεε₀ hε2 hε8 hsin
          (by linarith [hHIGHphase j]) (GH.semistable j) hj)
  have hLOW : σ.deformedLePred C W hr0 hr1 hW ε t LOW := by
    apply collapseLe
    exact ExtensionClosure.ofPostnikovTower GLOW.toPostnikovTower (fun j => by
      by_cases hj : IsZero (GLOW.factor j)
      · exact .zero hj
      · exact σ.deformedLePred_of_deformedLtPred C W hr0 hr1 hW _
          (σ.semistable_mem_deformedLt C W hr0 hr1 hW hε₀10
            hWide hε hεε₀ hε2 hε8 hsin
            (by linarith [hLOWphase j]) (GLOW.semistable j) hj))
  by_cases hMIDzero : IsZero MID
  · exact ⟨HIGH, REST, fH, gR, δR, hTR, hHIGH,
      .ext hTL (.zero hMIDzero) hLOW⟩
  · have hMIDcut :
        ∃ (XM YM : C) (f : XM ⟶ MID) (g : MID ⟶ YM)
          (δ : YM ⟶ XM⟦(1 : ℤ)⟧),
          Triangle.mk f g δ ∈ distTriang C ∧
          σ.deformedGtPred C W hr0 hr1 hW ε t XM ∧
          σ.deformedLePred C W hr0 hr1 hW ε t YM := by
      let a := t + ε - 4 * ε₀
      let b := t + ε + 4 * ε₀
      have hab : a < b := by dsimp [a, b]; linarith
      letI : Fact (a < b) := ⟨hab⟩
      letI : Fact (b - a ≤ 1) := ⟨by dsimp [a, b]; linarith⟩
      have hthin : b - a + 2 * ε < 1 := by
        dsimp [a, b]
        linarith
      have hFinite : ThinStrictFiniteLength C σ a b := by
        intro Y
        have hY := hWide (t + ε) Y
        exact Slicing.IntervalCat.isStrictFiniteLength_of_isFiniteLength C hY
      have hMIDinner :
          σ.slicing.intervalProp C (a + 2 * ε) (b - 4 * ε) MID := by
        refine Or.inr ⟨GM, fun j => ⟨?_, ?_⟩⟩
        · dsimp [a]
          linarith [hMIDphase j]
        · obtain ⟨i, hi⟩ := hMIDorigin j
          dsimp [b]
          rw [hi]
          linarith [hRESTphase i]
      obtain ⟨G, -, -⟩ := σ.interior_has_enveloped_HN C W hr0 hr1 hW
        hab hFinite hε hε2 hε8 hthin hsin hMIDzero hMIDinner
      exact σ.exists_deformedCut_triangle_of_hn C W hr0 hr1 hW G t
    obtain ⟨XM, YM, fXM, gYM, δYM, hTM, hXM, hYM⟩ := hMIDcut
    obtain ⟨V, vR, δV, hTV⟩ := distinguished_cocone_triangle (fXM ≫ fM)
    let oct₁ := Triangulated.someOctahedron rfl hTM hTL hTV
    have hV : σ.deformedLePred C W hr0 hr1 hW ε t V :=
      .ext oct₁.mem hYM hLOW
    obtain ⟨Z, vE, δZ, hTZ⟩ := distinguished_cocone_triangle₁ (gR ≫ vR)
    let oct₂ := Triangulated.someOctahedron' rfl hTR hTV hTZ
    have hZ : σ.deformedGtPred C W hr0 hr1 hW ε t Z :=
      .ext oct₂.mem hHIGH hXM
    exact ⟨Z, V, vE, gR ≫ vR, δZ, hTZ, hZ, hV⟩

end StabilityCondition.WithClassMap

end CategoryTheory.Triangulated
