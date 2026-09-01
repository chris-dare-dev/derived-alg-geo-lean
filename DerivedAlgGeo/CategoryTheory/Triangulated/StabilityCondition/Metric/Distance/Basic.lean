/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Uniqueness
import MathFormalContract

/-!
# The three-coordinate stability distance

This file adds the mass coordinate to the two-coordinate `slicingDist` of
`WeakStabilityCondition/StabilityCondition/Foundation/Deformation/SlicingDistance.lean`.  For every
nonzero object it takes the maximum of

* the `φ⁺` discrepancy;
* the `φ⁻` discrepancy;
* the logarithmic discrepancy of the HN masses.

The supremum of those objectwise terms is an `ℝ≥0∞`-valued symmetric extended
pseudodistance and satisfies the triangle inequality.

`WeakStabilityCondition/StabilityCondition/Metric/Mass/Uniqueness.lean` proves that the choice-free definition of
`stabilityMass` is equal to the finite mass sum of every HN filtration.
`logMassDist` is nevertheless defined on all of `ℝ≥0∞`: it places `⊤` at
infinite distance from finite values and at distance zero from itself.  On the
positive finite masses occurring here it is exactly `|log m₁ - log m₂|`,
equivalently the absolute log-ratio used by Bridgeland.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open scoped ENNReal

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

/-- Extended absolute logarithmic distance on `ℝ≥0∞`.

Finite inputs use the ordinary real logarithm.  `⊤` is infinitely far from
every finite input and zero distance from itself.

**The `0` input is not a distance.**  `ENNReal.toReal 0 = 0` and
`Real.log 0 = 0`, so this function reads mass `0` as mass `1`: `logMassDist 0 1`
is `0`, and `logMassDist 0 n` is finite where the true value is `+∞`.  That is
unreachable in this development and deliberately not guarded against — every
application is to `stabilityMass`, which `stabilityMass_pos` and
`stabilityMass_ne_top` pin inside `(0, ⊤)`, and `stabilityDist` takes its
supremum only over `¬IsZero E`.  Do not reuse this function on a mass that has
not been shown nonzero. -/
def logMassDist (m n : ℝ≥0∞) : ℝ≥0∞ :=
  if m = ⊤ then
    if n = ⊤ then 0 else ⊤
  else if n = ⊤ then ⊤
  else ENNReal.ofReal |Real.log m.toReal - Real.log n.toReal|

@[simp]
theorem logMassDist_self (m : ℝ≥0∞) : logMassDist m m = 0 := by
  by_cases hm : m = ⊤ <;> simp [logMassDist, hm]

theorem logMassDist_comm (m n : ℝ≥0∞) : logMassDist m n = logMassDist n m := by
  by_cases hm : m = ⊤ <;> by_cases hn : n = ⊤
  · simp [logMassDist, hm, hn]
  · simp [logMassDist, hm, hn]
  · simp [logMassDist, hm, hn]
  · simp [logMassDist, hm, hn, abs_sub_comm]

/-- The extended logarithmic discrepancy satisfies the triangle inequality. -/
theorem logMassDist_triangle (m n k : ℝ≥0∞) :
    logMassDist m k ≤ logMassDist m n + logMassDist n k := by
  by_cases hm : m = ⊤ <;> by_cases hn : n = ⊤ <;> by_cases hk : k = ⊤
  · simp [logMassDist, hm, hn, hk]
  · simp [logMassDist, hm, hn, hk]
  · simp [logMassDist, hm, hn, hk]
  · simp [logMassDist, hm, hn, hk]
  · simp [logMassDist, hm, hn, hk]
  · simp [logMassDist, hm, hn, hk]
  · simp [logMassDist, hm, hn, hk]
  · simp [logMassDist, hm, hn, hk]
    rw [← ENNReal.ofReal_add
      (abs_nonneg (Real.log m.toReal - Real.log n.toReal))
      (abs_nonneg (Real.log n.toReal - Real.log k.toReal))]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le
      (Real.log m.toReal) (Real.log n.toReal) (Real.log k.toReal))

/-- On finite inputs, `logMassDist` is the ordinary absolute logarithmic
difference. -/
theorem logMassDist_eq_of_ne_top {m n : ℝ≥0∞} (hm : m ≠ ⊤) (hn : n ≠ ⊤) :
    logMassDist m n =
      ENNReal.ofReal |Real.log m.toReal - Real.log n.toReal| := by
  simp [logMassDist, hm, hn]

/-- The `φ⁺` coordinate discrepancy for a fixed nonzero object. -/
def phiPlusDist (σ τ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E) : ℝ≥0∞ :=
  ENNReal.ofReal |σ.slicing.phiPlus C E hE - τ.slicing.phiPlus C E hE|

/-- The `φ⁻` coordinate discrepancy for a fixed nonzero object. -/
def phiMinusDist (σ τ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E) : ℝ≥0∞ :=
  ENNReal.ofReal |σ.slicing.phiMinus C E hE - τ.slicing.phiMinus C E hE|

/-- The logarithmic mass coordinate discrepancy for a fixed object. -/
def massDist (σ τ : StabilityCondition.WithClassMap C v) (E : C) : ℝ≥0∞ :=
  logMassDist (stabilityMass σ E) (stabilityMass τ E)

/-- The maximum of the two phase discrepancies and the mass discrepancy for
one nonzero object. -/
def stabilityDistTerm (σ τ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E) : ℝ≥0∞ :=
  max (phiPlusDist σ τ E hE) (max (phiMinusDist σ τ E hE) (massDist σ τ E))

/-- The three-coordinate, `ℝ≥0∞`-valued stability distance. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.prop-8.1" (relation := no_claim)
        (note := "The same three-coordinate formula, with stabilityMass proved equal to the finite mass sum of every HN filtration. WeakStabilityCondition/StabilityCondition/Metric/Distance/Separation.lean proves separation for ordinary stability conditions and for surjective class maps. The comparison with the Section 6 topology is proved unconditionally as stabilityDistanceTopologyCompatible in WeakStabilityCondition/StabilityCondition/Metric/Mass/Subadditivity/Triangle/Consequences.lean: full-distance balls are a neighbourhood basis for the basisNhd topology. The citation stays no_claim pending exact-head source-faithfulness review; no topology or metric instance is installed.")]
def stabilityDist (σ τ : StabilityCondition.WithClassMap C v) : ℝ≥0∞ :=
  ⨆ (E : C) (hE : ¬IsZero E), stabilityDistTerm σ τ E hE

omit [IsTriangulated C] in
@[simp]
theorem phiPlusDist_self (σ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E) : phiPlusDist σ σ E hE = 0 := by
  simp [phiPlusDist]

omit [IsTriangulated C] in
@[simp]
theorem phiMinusDist_self (σ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E) : phiMinusDist σ σ E hE = 0 := by
  simp [phiMinusDist]

omit [IsTriangulated C] in
@[simp]
theorem massDist_self (σ : StabilityCondition.WithClassMap C v) (E : C) :
    massDist σ σ E = 0 := by
  simp [massDist]

omit [IsTriangulated C] in
theorem phiPlusDist_comm (σ τ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E) : phiPlusDist σ τ E hE = phiPlusDist τ σ E hE := by
  simp [phiPlusDist, abs_sub_comm]

omit [IsTriangulated C] in
theorem phiMinusDist_comm (σ τ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E) : phiMinusDist σ τ E hE = phiMinusDist τ σ E hE := by
  simp [phiMinusDist, abs_sub_comm]

omit [IsTriangulated C] in
theorem massDist_comm (σ τ : StabilityCondition.WithClassMap C v) (E : C) :
    massDist σ τ E = massDist τ σ E := by
  exact logMassDist_comm _ _

omit [IsTriangulated C] in
theorem phiPlusDist_triangle (σ τ υ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E) :
    phiPlusDist σ υ E hE ≤ phiPlusDist σ τ E hE + phiPlusDist τ υ E hE := by
  unfold phiPlusDist
  rw [← ENNReal.ofReal_add
    (abs_nonneg (σ.slicing.phiPlus C E hE - τ.slicing.phiPlus C E hE))
    (abs_nonneg (τ.slicing.phiPlus C E hE - υ.slicing.phiPlus C E hE))]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le
    (σ.slicing.phiPlus C E hE) (τ.slicing.phiPlus C E hE)
    (υ.slicing.phiPlus C E hE))

omit [IsTriangulated C] in
theorem phiMinusDist_triangle (σ τ υ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E) :
    phiMinusDist σ υ E hE ≤ phiMinusDist σ τ E hE + phiMinusDist τ υ E hE := by
  unfold phiMinusDist
  rw [← ENNReal.ofReal_add
    (abs_nonneg (σ.slicing.phiMinus C E hE - τ.slicing.phiMinus C E hE))
    (abs_nonneg (τ.slicing.phiMinus C E hE - υ.slicing.phiMinus C E hE))]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le
    (σ.slicing.phiMinus C E hE) (τ.slicing.phiMinus C E hE)
    (υ.slicing.phiMinus C E hE))

omit [IsTriangulated C] in
theorem massDist_triangle (σ τ υ : StabilityCondition.WithClassMap C v) (E : C) :
    massDist σ υ E ≤ massDist σ τ E + massDist τ υ E :=
  logMassDist_triangle _ _ _

/-- The mass coordinate used by `stabilityDist` is always the ordinary finite
absolute logarithmic difference. -/
theorem massDist_eq_abs_log (σ τ : StabilityCondition.WithClassMap C v) (E : C) :
    massDist σ τ E = ENNReal.ofReal
      |Real.log (stabilityMass σ E).toReal -
        Real.log (stabilityMass τ E).toReal| := by
  unfold massDist
  exact logMassDist_eq_of_ne_top (stabilityMass_ne_top σ E)
    (stabilityMass_ne_top τ E)

/-- Ratio form of the preceding theorem, matching the mass term in
Bridgeland's formula. -/
theorem massDist_eq_abs_log_ratio
    (σ τ : StabilityCondition.WithClassMap C v) (E : C) (hE : ¬IsZero E) :
    massDist σ τ E = ENNReal.ofReal
      |Real.log ((stabilityMass τ E).toReal /
        (stabilityMass σ E).toReal)| := by
  rw [massDist_eq_abs_log, Real.log_div
    (ne_of_gt (stabilityMass_toReal_pos τ hE))
    (ne_of_gt (stabilityMass_toReal_pos σ hE))]
  congr 1
  rw [show Real.log (stabilityMass σ E).toReal -
      Real.log (stabilityMass τ E).toReal =
      -(Real.log (stabilityMass τ E).toReal -
        Real.log (stabilityMass σ E).toReal) by ring, abs_neg]

omit [IsTriangulated C] in
@[simp]
theorem stabilityDist_self (σ : StabilityCondition.WithClassMap C v) :
    stabilityDist σ σ = 0 := by
  simp [stabilityDist, stabilityDistTerm]

omit [IsTriangulated C] in
theorem stabilityDist_comm (σ τ : StabilityCondition.WithClassMap C v) :
    stabilityDist σ τ = stabilityDist τ σ := by
  unfold stabilityDist
  apply iSup_congr
  intro E
  apply iSup_congr
  intro hE
  simp only [stabilityDistTerm, phiPlusDist_comm σ τ E hE,
    phiMinusDist_comm σ τ E hE, massDist_comm σ τ E]

omit [IsTriangulated C] in
/-- The full stability distance satisfies the triangle inequality. -/
theorem stabilityDist_triangle (σ τ υ : StabilityCondition.WithClassMap C v) :
    stabilityDist σ υ ≤ stabilityDist σ τ + stabilityDist τ υ := by
  refine iSup₂_le fun E hE ↦ ?_
  have hp : phiPlusDist σ υ E hE ≤
      stabilityDistTerm σ τ E hE + stabilityDistTerm τ υ E hE := by
    calc
      phiPlusDist σ υ E hE
          ≤ phiPlusDist σ τ E hE + phiPlusDist τ υ E hE :=
            phiPlusDist_triangle σ τ υ E hE
      _ ≤ stabilityDistTerm σ τ E hE + stabilityDistTerm τ υ E hE :=
        add_le_add (le_max_left _ _) (le_max_left _ _)
  have hm : phiMinusDist σ υ E hE ≤
      stabilityDistTerm σ τ E hE + stabilityDistTerm τ υ E hE := by
    calc
      phiMinusDist σ υ E hE
          ≤ phiMinusDist σ τ E hE + phiMinusDist τ υ E hE :=
            phiMinusDist_triangle σ τ υ E hE
      _ ≤ stabilityDistTerm σ τ E hE + stabilityDistTerm τ υ E hE :=
        add_le_add (le_trans (le_max_left _ _) (le_max_right _ _))
          (le_trans (le_max_left _ _) (le_max_right _ _))
  have hmass : massDist σ υ E ≤
      stabilityDistTerm σ τ E hE + stabilityDistTerm τ υ E hE := by
    calc
      massDist σ υ E ≤ massDist σ τ E + massDist τ υ E :=
        massDist_triangle σ τ υ E
      _ ≤ stabilityDistTerm σ τ E hE + stabilityDistTerm τ υ E hE :=
        add_le_add (le_trans (le_max_right _ _) (le_max_right _ _))
          (le_trans (le_max_right _ _) (le_max_right _ _))
  have hστ : stabilityDistTerm σ τ E hE ≤ stabilityDist σ τ := by
    unfold stabilityDist
    exact le_iSup₂ (f := fun (X : C) (hX : ¬IsZero X) ↦
      stabilityDistTerm σ τ X hX) E hE
  have hτυ : stabilityDistTerm τ υ E hE ≤ stabilityDist τ υ := by
    unfold stabilityDist
    exact le_iSup₂ (f := fun (X : C) (hX : ¬IsZero X) ↦
      stabilityDistTerm τ υ X hX) E hE
  calc
    stabilityDistTerm σ υ E hE
        ≤ stabilityDistTerm σ τ E hE + stabilityDistTerm τ υ E hE := by
          exact max_le hp (max_le hm hmass)
    _ ≤ stabilityDist σ τ + stabilityDist τ υ :=
      add_le_add hστ hτυ

omit [IsTriangulated C] in
/-- Every objectwise three-coordinate term is bounded by the full stability
distance.  This is the basic elimination rule for the supremum defining
`stabilityDist`. -/
theorem stabilityDistTerm_le_stabilityDist
    (σ τ : StabilityCondition.WithClassMap C v) (E : C) (hE : ¬IsZero E) :
    stabilityDistTerm σ τ E hE ≤ stabilityDist σ τ := by
  unfold stabilityDist
  exact le_iSup₂ (f := fun (X : C) (hX : ¬IsZero X) ↦
    stabilityDistTerm σ τ X hX) E hE

omit [IsTriangulated C] in
/-- The positive-phase coordinate of an object is bounded by the full
stability distance. -/
theorem phiPlusDist_le_stabilityDist
    (σ τ : StabilityCondition.WithClassMap C v) (E : C) (hE : ¬IsZero E) :
    phiPlusDist σ τ E hE ≤ stabilityDist σ τ :=
  (le_max_left _ _).trans (stabilityDistTerm_le_stabilityDist σ τ E hE)

omit [IsTriangulated C] in
/-- The negative-phase coordinate of an object is bounded by the full
stability distance. -/
theorem phiMinusDist_le_stabilityDist
    (σ τ : StabilityCondition.WithClassMap C v) (E : C) (hE : ¬IsZero E) :
    phiMinusDist σ τ E hE ≤ stabilityDist σ τ :=
  (le_max_left _ _).trans (le_max_right _ _ |>.trans
    (stabilityDistTerm_le_stabilityDist σ τ E hE))

omit [IsTriangulated C] in
/-- The mass coordinate of an object is bounded by the full stability
distance. -/
theorem massDist_le_stabilityDist
    (σ τ : StabilityCondition.WithClassMap C v) (E : C) (hE : ¬IsZero E) :
    massDist σ τ E ≤ stabilityDist σ τ :=
  (le_max_right _ _).trans (le_max_right _ _ |>.trans
    (stabilityDistTerm_le_stabilityDist σ τ E hE))

omit [IsTriangulated C] in
/-- The phase-only `slicingDist` is bounded by the full three-coordinate
distance. -/
theorem slicingDist_le_stabilityDist (σ τ : StabilityCondition.WithClassMap C v) :
    slicingDist C σ.slicing τ.slicing ≤ stabilityDist σ τ := by
  refine iSup₂_le fun E hE ↦ ?_
  have hterm : stabilityDistTerm σ τ E hE ≤ stabilityDist σ τ := by
    unfold stabilityDist
    exact le_iSup₂ (f := fun (X : C) (hX : ¬IsZero X) ↦
      stabilityDistTerm σ τ X hX) E hE
  rw [ENNReal.ofReal_max]
  -- Unfold explicitly rather than relying on default-transparency delta: the
  -- `le_trans` below otherwise unifies only by silently unfolding three
  -- definitions the proof never names.
  simp only [stabilityDistTerm, phiPlusDist, phiMinusDist] at hterm ⊢
  exact le_trans (max_le_max le_rfl (le_max_left _ _)) hterm

end

end CategoryTheory.Triangulated
