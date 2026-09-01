/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakExtrema

/-!
# The two classes at a weak slope cutoff

`Cutoff.lean` cuts two classes out of an abelian category by a **phase**
`β : ℝ`, which is available for a strict stability function.  This file cuts
them by a **slope** `μ₀ : WithTop ℝ` for a weak one:

```
T μ₀ = {E | every weak HN slope of E exceeds μ₀}
F μ₀ = {E | every weak HN slope of E is at most μ₀}
```

## Why the cutoff is `WithTop ℝ`, and what that buys

Because slopes are.  A rank-zero object has charge on the real boundary, so
slope `⊤`, so `μMinus = ⊤ > μ₀` for **every finite** `μ₀`, so it lies in
`T μ₀` — `mem_hnTors_of_slope_eq_top` below.  That is the classical convention:
torsion sheaves are in the torsion class at every finite slope cutoff.

This is the correct replacement for `SlopeCutoff.lean`'s
`mem_hnTors_of_rank_zero`, and the replacement is not cosmetic.  The strict
lemma reaches its conclusion through `phase_eq_one_of_rank_zero`, which needs
`degree_pos_of_rank_zero` — the **curve** hypothesis, false on a surface, where
a skyscraper has `c₁ = 0` and so degree `0`.  With charge exactly `0` there is
no phase at all (`arg 0 = 0` is not a phase), and no phase comparison can place
the object.  The slope `⊤` places it, with no positivity hypothesis whatever.

The cutoff `μ₀ = ⊤` is permitted and degenerate in the expected direction: no
slope exceeds `⊤`, so `T ⊤` contains only the zero object while `F ⊤` is
everything.  Nothing below excludes it.

## What is here and what is next

`hom_eq_zero_of_mem_hnTors_of_mem_hnFree` is the Hom-vanishing half of a torsion
pair.  The splitting half is `WeakSplitting.lean`, and with both present the two
classes **are** a torsion pair — assembled as
`WeakStabilityFunctionOn.hnTorsionPair` in
`Weak/Tilting/TorsionPair/WeakStabilityFunction.lean`.  This file still states
only the Hom-vanishing, which is all it needs.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.Triangulated

variable {A : Type u} [Category.{v} A] [Abelian A]

namespace WeakStabilityFunctionOn

variable (W : WeakStabilityFunctionOn (abelianDatum A)) (μ₀ : WithTop ℝ)

/-- The **torsion class** at a weak slope cutoff: the zero object, and the
objects whose weak HN slopes all exceed `μ₀`. -/
def hnTors : Set A :=
  {E | IsZero E ∨ ∃ F : AbelianWeakHNFiltration W E, μ₀ < F.μMinus}

/-- The **torsion-free class** at a weak slope cutoff: the zero object, and the
objects whose weak HN slopes are all at most `μ₀`. -/
def hnFree : Set A :=
  {E | IsZero E ∨ ∃ F : AbelianWeakHNFiltration W E, F.μPlus ≤ μ₀}

variable {W μ₀}

theorem isZero_mem_hnTors {E : A} (hE : IsZero E) : E ∈ hnTors W μ₀ := Or.inl hE

theorem isZero_mem_hnFree {E : A} (hE : IsZero E) : E ∈ hnFree W μ₀ := Or.inl hE

/-- Membership is independent of the filtration chosen, because `μ⁻` is.

The HN property is needed for the reverse direction only: without a filtration
to exhibit, the universally quantified condition is vacuous while membership
asks for a witness. -/
theorem mem_hnTors_iff_forall (hHN : W.HasHNProperty) {E : A} (hE : ¬IsZero E) :
    E ∈ hnTors W μ₀ ↔ ∀ F : AbelianWeakHNFiltration W E, μ₀ < F.μMinus := by
  obtain ⟨G⟩ := hHN E hE
  constructor
  · rintro (h | ⟨F, hF⟩) K
    · exact absurd h hE
    · rwa [AbelianWeakHNFiltration.μMinus_eq K F]
  · exact fun h => Or.inr ⟨G, h G⟩

/-- Membership is independent of the filtration chosen, because `μ⁺` is. -/
theorem mem_hnFree_iff_forall (hHN : W.HasHNProperty) {E : A} (hE : ¬IsZero E) :
    E ∈ hnFree W μ₀ ↔ ∀ F : AbelianWeakHNFiltration W E, F.μPlus ≤ μ₀ := by
  obtain ⟨G⟩ := hHN E hE
  constructor
  · rintro (h | ⟨F, hF⟩) K
    · exact absurd h hE
    · rwa [AbelianWeakHNFiltration.μPlus_eq K F]
  · exact fun h => Or.inr ⟨G, h G⟩

/-- **A weak-semistable object of slope `⊤` lies in the torsion class at every
finite cutoff.**  This is the skyscraper, and it is the whole reason the cutoff
is valued in `WithTop ℝ` rather than in `ℝ`. -/
theorem mem_hnTors_of_slope_eq_top {E : A} (hE : W.IsSemistable E)
    (hslope : W.slope E = ⊤) (hμ : μ₀ ≠ ⊤) : E ∈ hnTors W μ₀ :=
  Or.inr ⟨AbelianWeakHNFiltration.ofSemistable hE, by
    rw [AbelianWeakHNFiltration.ofSemistable_μMinus, hslope]
    exact Ne.lt_top hμ⟩

/-- A weak-semistable object of charge `0` lies in the torsion class at every
finite cutoff.  The rank-zero, degree-zero case in charge terms. -/
theorem mem_hnTors_of_charge_eq_zero {E : A} (hE : W.IsSemistable E)
    (hcharge : W.charge E = 0) (hμ : μ₀ ≠ ⊤) : E ∈ hnTors W μ₀ :=
  mem_hnTors_of_slope_eq_top hE (W.slope_eq_top_of_charge_eq_zero hcharge) hμ

/-- **The two classes meet only in zero.**  An object in both would have
`μ₀ < μ⁻ ≤ μ⁺ ≤ μ₀`. -/
theorem isZero_of_mem_hnTors_of_mem_hnFree {E : A} (hT : E ∈ hnTors W μ₀)
    (hF : E ∈ hnFree W μ₀) : IsZero E := by
  by_contra hE
  obtain ⟨F, hmin⟩ : ∃ F : AbelianWeakHNFiltration W E, μ₀ < F.μMinus := by
    rcases hT with h0 | h; · exact absurd h0 hE
    · exact h
  obtain ⟨K, hmax⟩ : ∃ K : AbelianWeakHNFiltration W E, K.μPlus ≤ μ₀ := by
    rcases hF with h0 | h; · exact absurd h0 hE
    · exact h
  rw [AbelianWeakHNFiltration.μPlus_eq K F] at hmax
  exact absurd (lt_of_lt_of_le (lt_of_lt_of_le hmin F.μMinus_le_μPlus) hmax)
    (lt_irrefl μ₀)

/-- **Hom-vanishing, for a weak-semistable target.**  A map from an object whose
weak HN slopes all exceed `μ₀` to a weak-semistable object of slope at most
`μ₀` is zero. -/
theorem hom_eq_zero_of_mem_hnTors_of_semistable {E B : A} (hE : ¬IsZero E)
    (hT : E ∈ hnTors W μ₀) (hB : W.IsSemistable B) (hslope : W.slope B ≤ μ₀)
    (f : E ⟶ B) : f = 0 := by
  obtain ⟨F, hmin⟩ : ∃ F : AbelianWeakHNFiltration W E, μ₀ < F.μMinus := by
    rcases hT with h0 | h; · exact absurd h0 hE
    · exact h
  exact F.hom_eq_zero_to_semistable_of_μ_lt_μMinus hB
    (lt_of_le_of_lt hslope hmin) f

/-- **Hom-vanishing.**  A map from an object whose weak HN slopes all exceed
`μ₀` to an object whose weak HN slopes are all at most `μ₀` is zero: its image
is a quotient of the source and a subobject of the target, so
`μ₀ < μ⁻(image)` and `μ⁺(image) ≤ μ₀`, which `μMinus_le_μPlus` contradicts
unless the image is zero.

The HN property is needed for the image, which is neither of the two given
objects. -/
theorem hom_eq_zero_of_mem_hnTors_of_mem_hnFree (hHN : W.HasHNProperty)
    {E B : A} (hT : E ∈ hnTors W μ₀) (hFr : B ∈ hnFree W μ₀) (f : E ⟶ B) :
    f = 0 := by
  by_cases hE : IsZero E
  · exact hE.eq_zero_of_src f
  by_cases hI : IsZero ((imageSubobject f : A))
  · rw [← imageSubobject_arrow_comp f, hI.eq_zero_of_src (imageSubobject f).arrow,
      comp_zero]
  have hB : ¬IsZero B := by
    intro hzero
    apply hI
    rw [hzero.eq_zero_of_tgt f, imageSubobject_zero]
    simp
  obtain ⟨F, hmin⟩ : ∃ F : AbelianWeakHNFiltration W E, μ₀ < F.μMinus := by
    rcases hT with h0 | h; · exact absurd h0 hE
    · exact h
  obtain ⟨G, hmax⟩ : ∃ G : AbelianWeakHNFiltration W B, G.μPlus ≤ μ₀ := by
    rcases hFr with h0 | h; · exact absurd h0 hB
    · exact h
  obtain ⟨K⟩ := hHN _ hI
  exfalso
  refine absurd (lt_of_lt_of_le (lt_of_lt_of_le hmin ?_) hmax) (lt_irrefl μ₀)
  exact ((F.μMinus_le_of_epi K (factorThruImageSubobject f)).trans
    K.μMinus_le_μPlus).trans (K.μPlus_le_of_mono G (imageSubobject f).arrow)

end WeakStabilityFunctionOn

end CategoryTheory.Triangulated
