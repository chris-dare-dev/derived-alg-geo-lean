/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.CoreConsequences
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Foundation.Slicing.PhaseTruncation
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.TorsionPair.Heart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The torsion pair at a phase cutoff (display (14.1))

For a slicing `s` and a cutoff `β ∈ [0, 1]`, the heart `P((0, 1])` of the
slicing-induced t-structure carries the torsion pair

```
T = P((β, 1]),      F = P((0, β]),
```

constructed here as a `HeartTorsionPair` on `s.toTStructure` — so the
reviewed Happel–Reiten–Smalø tilt applies to it, and with `tilt_heart_iff`
(#106) its tilted heart is identified with the extensions of `P((β, 1])` by
`P((0, β])⟦1⟧`, the single-step form of `A^{♯β} = ⟨F^β[1], T^β⟩`.

Everything is unconditional: the Hom-vanishing is the slicing's own
phase-ordered vanishing (`zero_of_gtProp_leProp_general`), and the
decomposition is the Harder–Narasimhan filtration cut at `β`
(`exists_split_at_cutoff`), with the two interval bounds that the cut does
not hand over recovered by rotating the split triangle into the extension
closures of the aisle and co-aisle.

## Relation to display (14.1), stated for the reviewer

The paper's (14.1) is written in slope language on the heart of a weak
stability condition: `T^β = {μ⁻ > β}`, `F^β = {μ⁺ ≤ β}`. This file's pair is
the same construction in **phase** language on the slicing heart.  The exact
finite-slope reparametrisation and equality of the two pairs are formalized
downstream in `TorsionPair/SourceSlope.lean`.  The coverage map remains
`mapped` pending its separate source-review protocol.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated ZeroObject
open CategoryTheory.Triangulated.Tilting

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

variable (s : Slicing C)

/-- The torsion class at cutoff `β`: objects of `P((β, 1])`. -/
def phaseTors (β : ℝ) : ObjectProperty C :=
  fun E => s.gtProp C β E ∧ s.leProp C 1 E

/-- The torsion-free class at cutoff `β`: objects of `P((0, β])`. -/
def phaseFree (β : ℝ) : ObjectProperty C :=
  fun E => s.gtProp C 0 E ∧ s.leProp C β E

omit [IsTriangulated C] in
/-- `leProp` is closed under isomorphisms. -/
theorem leProp_of_iso {t : ℝ} {E E' : C} (e : E ≅ E') (h : s.leProp C t E) :
    s.leProp C t E' := by
  rcases h with hZ | ⟨F, hn, hle⟩
  · exact Or.inl (hZ.of_iso e.symm)
  · exact Or.inr ⟨F.ofIso C e, hn, by
      simpa [CategoryTheory.Triangulated.HNFiltration.phiPlus,
        CategoryTheory.Triangulated.HNFiltration.ofIso] using hle⟩

omit [IsTriangulated C] in
/-- `gtProp` is closed under isomorphisms. -/
theorem gtProp_of_iso {t : ℝ} {E E' : C} (e : E ≅ E') (h : s.gtProp C t E) :
    s.gtProp C t E' := by
  rcases h with hZ | ⟨F, hn, hgt⟩
  · exact Or.inl (hZ.of_iso e.symm)
  · exact Or.inr ⟨F.ofIso C e, hn, by
      simpa [CategoryTheory.Triangulated.HNFiltration.phiMinus,
        CategoryTheory.Triangulated.HNFiltration.ofIso] using hgt⟩

/-- Heart membership from the two interval bounds, through the slicing heart
identification `Slicing.toTStructure_heart_iff`
(`WeakStabilityCondition/Foundation/Slicing/PhaseTruncation.lean`). -/
theorem mem_heart_of_bounds {E : C} (h0 : s.gtProp C 0 E) (h1 : s.leProp C 1 E) :
    (s.toTStructure).heart E :=
  (s.toTStructure_heart_iff C E).mpr ⟨h0, h1⟩

/-- **The torsion pair at a phase cutoff** — display (14.1) in phase
language: `(P((β, 1]), P((0, β]))` is a torsion pair on the heart
`P((0, 1])` of the slicing-induced t-structure. -/
def slicingTorsionPair {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    HeartTorsionPair (s.toTStructure) where
  tors := phaseTors s β
  free := phaseFree s β
  tors_isLE E hE :=
    (((s.toTStructure).mem_heart_iff E).mp
      (mem_heart_of_bounds s (s.gtProp_anti C h0 E hE.1) hE.2)).1
  tors_isGE E hE :=
    (((s.toTStructure).mem_heart_iff E).mp
      (mem_heart_of_bounds s (s.gtProp_anti C h0 E hE.1) hE.2)).2
  free_isLE E hE :=
    (((s.toTStructure).mem_heart_iff E).mp
      (mem_heart_of_bounds s hE.1 (s.leProp_mono C h1 E hE.2))).1
  free_isGE E hE :=
    (((s.toTStructure).mem_heart_iff E).mp
      (mem_heart_of_bounds s hE.1 (s.leProp_mono C h1 E hE.2))).2
  tors_isClosedUnderIsomorphisms :=
    ⟨fun {_ _} e h => ⟨gtProp_of_iso s e h.1, leProp_of_iso s e h.2⟩⟩
  free_isClosedUnderIsomorphisms :=
    ⟨fun {_ _} e h => ⟨gtProp_of_iso s e h.1, leProp_of_iso s e h.2⟩⟩
  hom_eq_zero := fun _ _ hX hY f =>
    s.zero_of_gtProp_leProp_general C β hX.1 hY.2 f
  exists_triangle E hle hge := by
    have hheart : (s.toTStructure).heart E :=
      ((s.toTStructure).mem_heart_iff E).mpr ⟨hle, hge⟩
    obtain ⟨hgt0, hle1⟩ := (s.toTStructure_heart_iff C E).mp hheart
    by_cases hE : IsZero E
    · exact ⟨E, 0, ⟨Or.inl hE, Or.inl hE⟩, ⟨s.gtProp_zero C 0, s.leProp_zero C β⟩,
        𝟙 E, 0, 0, contractible_distinguished E⟩
    -- a single HN filtration with both bounds, from the intrinsic phases
    have hminus : (0 : ℝ) < s.phiMinus C E hE := s.phiMinus_gt_of_gtProp C hE hgt0
    have hplus : s.phiPlus C E hE < 2 :=
      lt_of_le_of_lt (s.phiPlus_le_of_leProp C hE hle1) (by norm_num)
    have hint := s.intervalProp_of_intrinsic_phases C hE hminus hplus
    rcases hint with hZ | ⟨F, hI⟩
    · exact absurd hZ hE
    have hn : 0 < F.n := F.n_pos C hE
    obtain ⟨X, Y, f, g, h, hT, hXgt, hYle, -⟩ :=
      s.exists_split_at_cutoff_with_upper_bound C F hI hn
    -- `X ∈ P((β, 1])`: the co-aisle bound comes from the inverse rotation.
    have hX1 : s.leProp C 1 X := by
      have hYshift : s.leProp C 1 (Y⟦(-1 : ℤ)⟧) := by
        have := s.leProp_shift C β Y (-1) hYle
        exact s.leProp_mono C (by push_cast; linarith) _ this
      exact s.leProp_of_triangle C 1 hYshift hle1
        (inv_rot_of_distTriang _ hT)
    -- `Y ∈ P((0, β])`: the aisle bound comes from the rotation.
    have hY0 : s.gtProp C 0 Y := by
      have hXshift : s.gtProp C 0 (X⟦(1 : ℤ)⟧) := by
        have := s.gtProp_shift C β X 1 hXgt
        exact s.gtProp_anti C (by push_cast; linarith) _ this
      exact s.gtProp_of_triangle C 0 hgt0 hXshift (rot_of_distTriang _ hT)
    exact ⟨X, Y, ⟨hXgt, hX1⟩, ⟨hY0, hYle⟩, f, g, h, hT⟩

@[simp]
theorem slicingTorsionPair_tors {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    (slicingTorsionPair s h0 h1).tors = phaseTors s β := rfl

@[simp]
theorem slicingTorsionPair_free {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) :
    (slicingTorsionPair s h0 h1).free = phaseFree s β := rfl

/-- **The tilted heart at the cutoff is `⟨P((0, β])⟦1⟧, P((β, 1])⟩`** in the
single-step form: an object lies in the heart of the tilt of the slicing
heart at `β` iff it is an extension of a `P((β, 1])`-object by a shifted
`P((0, β])`-object. Direct from `tilt_heart_iff` (#106). This is the
`A^{♯β}` of display (14.1), up to the unformalized slope–phase
reparametrisation. -/
theorem slicingTilt_heart_iff {β : ℝ} (h0 : 0 ≤ β) (h1 : β ≤ 1) (X : C) :
    ((slicingTorsionPair s h0 h1).tilt).heart X ↔
      ∃ (F₀ T₀ : C) (_ : phaseFree s β F₀) (_ : phaseTors s β T₀)
        (f : F₀⟦(1 : ℤ)⟧ ⟶ X) (g : X ⟶ T₀)
        (h : T₀ ⟶ F₀⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
        Triangle.mk f g h ∈ distTriang C :=
  (slicingTorsionPair s h0 h1).tilt_heart_iff X

end CategoryTheory.Triangulated.WeakStabilityCondition
