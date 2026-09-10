/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Stability.Gieseker.HarderNarasimhan.Existence
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Weak.Foundation.StabilityFunction.WeakSplitting

/-!
# What the Harder–Narasimhan property unlocks on `Coh X`

`hasHNProperty` is the hypothesis the abstract theory takes at every one of its use sites. With it
proved, those sites become theorems about coherent sheaves, and this file collects them. Nothing
here re-proves anything: each declaration applies an existing result from
`Foundation/StabilityFunction/WeakHarderNarasimhan.lean` or
`Foundation/StabilityFunction/WeakSplitting.lean` to the filtration `Existence.lean` builds.

## The chosen filtration

The HN filtration is not unique as a term, only as a mathematical object, and the abstract theory
states existence as `Nonempty`. `hnFiltration` picks one with choice. Everything downstream that
mentions `μPlus` or `μMinus` is therefore about *that* choice, which is why the genuinely
mathematical statement below, `filtration_muPlus_ne_top_of_isPure`, is proved for an arbitrary
filtration first and only then specialized.

## The torsion/torsion-free splitting

For a cutoff `μ₀`, `exists_shortExact_hnTors_hnFree` cuts the filtration at its crossing index and
produces a short exact sequence whose subsheaf has all slopes above `μ₀` and whose quotient has
all slopes at or below it. That is the input a tilted heart is built from; constructing the tilt
belongs to the abstract tilting lane, not here.
-/

universe u

open CategoryTheory Limits CategoryTheory.Triangulated

namespace AlgebraicGeometry.Stability.Gieseker

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [IsVariety k X]

namespace PolarizedVarietyData

variable {P : PolarizedVarietyData k X}

/-- **The Harder–Narasimhan filtration of a nonzero coherent sheaf.** A choice of one of the
filtrations `exists_filtration` produces. -/
noncomputable def hnFiltration (h : MuPositivityData P) (I : MuHNInput P h) {F : Coh X}
    (hF : ¬IsZero F) :
    AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction F :=
  (exists_filtration h I hF).some

/-- The largest Harder–Narasimhan slope of a nonzero coherent sheaf. -/
noncomputable def muPlus (h : MuPositivityData P) (I : MuHNInput P h) {F : Coh X}
    (hF : ¬IsZero F) : WithTop ℝ :=
  (hnFiltration h I hF).μPlus

/-- The smallest Harder–Narasimhan slope of a nonzero coherent sheaf. -/
noncomputable def muMinus (h : MuPositivityData P) (I : MuHNInput P h) {F : Coh X}
    (hF : ¬IsZero F) : WithTop ℝ :=
  (hnFiltration h I hF).μMinus

/-- The smallest Harder–Narasimhan slope does not exceed the largest. -/
theorem muMinus_le_muPlus (h : MuPositivityData P) (I : MuHNInput P h) {F : Coh X}
    (hF : ¬IsZero F) : muMinus h I hF ≤ muPlus h I hF :=
  (hnFiltration h I hF).μMinus_le_μPlus

/-- **The first chain step of a filtration realizes `μPlus` as the slope of a subobject.**

This is `firstFactorIso` read as a statement about `μPlus`: the opening factor runs out of the
bottom subobject, so it *is* the first chain step. -/
theorem muPlus_eq_topSlope_chain_one (h : MuPositivityData P) {Y : Coh X}
    (G : AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction Y) :
    G.μPlus = (P.weakSlopeData h).topSlope
      ((G.chain (Fin.succ ⟨0, G.nonempty⟩) : Subobject Y) : Coh X) := by
  rw [AbelianWeakHNFiltration.μPlus, ← G.factor_slope ⟨0, G.nonempty⟩]
  exact (P.weakSlopeData h).toWeakStabilityFunction.slope_eq_of_iso (firstFactorIso h G)

/-- The first chain step of a filtration is a nonzero subobject. -/
theorem not_isZero_chain_one (h : MuPositivityData P) {Y : Coh X}
    (G : AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction Y) :
    ¬IsZero ((G.chain (Fin.succ ⟨0, G.nonempty⟩) : Subobject Y) : Coh X) := by
  intro hz
  exact G.factor_not_isZero ⟨0, G.nonempty⟩ (hz.of_iso (firstFactorIso h G))

/-- **For a pure sheaf the largest Harder–Narasimhan slope is finite.**

`μPlus` is the slope of the first chain step, which is a nonzero subobject; purity gives it
positive multiplicity, and only multiplicity zero produces `⊤`. -/
theorem filtration_muPlus_ne_top_of_isPure (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsPure F)
    (G : AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction F) :
    G.μPlus ≠ ⊤ := by
  have hne := not_isZero_chain_one h G
  have hpos : 0 < P.multiplicity
      ((G.chain (Fin.succ ⟨0, G.nonempty⟩) : Subobject F) : Coh X) :=
    hF.2 _ (G.chain (Fin.succ ⟨0, G.nonempty⟩)).arrow inferInstance hne
  rw [muPlus_eq_topSlope_chain_one h G, weakSlopeData_topSlope_of_multiplicity_pos h hpos]
  exact WithTop.coe_ne_top

/-- **`μPlus` of a pure coherent sheaf is finite.** -/
theorem muPlus_ne_top_of_isPure (h : MuPositivityData P) (I : MuHNInput P h) {F : Coh X}
    (hF : P.IsPure F) : muPlus h I hF.not_isZero ≠ ⊤ :=
  filtration_muPlus_ne_top_of_isPure h hF _

/-- **A Gieseker-semistable sheaf has a one-step Harder–Narasimhan filtration.**

Gieseker semistability implies μ-semistability, and a semistable object is its own filtration.
This closes the loop back to the Gieseker order: the coarser numerical invariant sees no
destabilizing subsheaf either. -/
noncomputable def giesekerSemistable_implies_hn_trivial (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    AbelianWeakHNFiltration (P.weakSlopeData h).toWeakStabilityFunction F :=
  AbelianWeakHNFiltration.ofSemistable (giesekerSemistable_implies_muSemistable h hF)

/-- The trivial filtration has exactly one factor. -/
theorem giesekerSemistable_hn_trivial_n (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    (giesekerSemistable_implies_hn_trivial h hF).n = 1 := rfl

/-- Both extrema of the trivial filtration are the slope of the sheaf itself. -/
theorem giesekerSemistable_hn_trivial_muPlus (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    (giesekerSemistable_implies_hn_trivial h hF).μPlus =
      (P.weakSlopeData h).topSlope F := rfl

/-- Both extrema of the trivial filtration are the slope of the sheaf itself. -/
theorem giesekerSemistable_hn_trivial_muMinus (h : MuPositivityData P) {F : Coh X}
    (hF : P.IsGiesekerSemistable F) :
    (giesekerSemistable_implies_hn_trivial h hF).μMinus =
      (P.weakSlopeData h).topSlope F := rfl

/-- **The Harder–Narasimhan torsion subsheaf at a cutoff.** Every coherent sheaf has a subsheaf
whose Harder–Narasimhan slopes all exceed `μ₀` and whose quotient's all fail to. -/
theorem exists_subobject_hnTors_cokernel_hnFree (h : MuPositivityData P) (I : MuHNInput P h)
    (μ₀ : WithTop ℝ) (F : Coh X) :
    ∃ T : Subobject F,
      ((T : Coh X) ∈ WeakStabilityFunctionOn.hnTors
        (P.weakSlopeData h).toWeakStabilityFunction μ₀) ∧
      (cokernel T.arrow ∈ WeakStabilityFunctionOn.hnFree
        (P.weakSlopeData h).toWeakStabilityFunction μ₀) :=
  WeakStabilityFunctionOn.exists_subobject_hnTors_cokernel_hnFree
    (μ₀ := μ₀) (hasHNProperty h I) F

/-- **The torsion/torsion-free splitting as a short exact sequence.** This is the input a tilted
heart is built from; the tilt itself belongs to the abstract tilting lane. -/
theorem exists_shortExact_hnTors_hnFree (h : MuPositivityData P) (I : MuHNInput P h)
    (μ₀ : WithTop ℝ) (F : Coh X) :
    ∃ (T Q : Coh X) (i : T ⟶ F) (p : F ⟶ Q) (w : i ≫ p = 0),
      T ∈ WeakStabilityFunctionOn.hnTors (P.weakSlopeData h).toWeakStabilityFunction μ₀ ∧
      Q ∈ WeakStabilityFunctionOn.hnFree (P.weakSlopeData h).toWeakStabilityFunction μ₀ ∧
      (ShortComplex.mk i p w).ShortExact :=
  WeakStabilityFunctionOn.exists_shortExact_hnTors_hnFree
    (μ₀ := μ₀) (hasHNProperty h I) F

end PolarizedVarietyData

end AlgebraicGeometry.Stability.Gieseker
