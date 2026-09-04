/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Distance.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Isometry.Phase
import MathFormalContract

/-!
# Autoequivalences preserve the full stability distance

The phase coordinates were handled in `WeakStabilityCondition/StabilityCondition/Metric/Isometry/Phase.lean`.  The new input is
`AutPair.act_stabilityMass`: transporting every HN filtration through the
equivalence preserves its finite charge-norm sum, so it preserves the HN
mass.  The three coordinates can then be transported
objectwise, and the two supremum inequalities use `Φ⁻¹ E` and `Φ E` exactly as
in the phase-only proof.

The final quotient theorem is the full-distance analogue of
`AutPairQuot_smul_slicingDist`.  It is still stated for `AutPairQuot v`, not
for the paper's bare `Aut(D)`.  The trust annotation records that remaining
group-level boundary rather than identifying this theorem with Lemma 8.2.
-/

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open scoped ENNReal

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ C →+ Λ}

variable (a : CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair v)

/-- The acted `φ⁺` discrepancy at `E` is the original discrepancy at `Φ⁻¹E`. -/
theorem act_phiPlusDist (σ τ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E)
    (hE' : ¬IsZero (a.Φ.e.inverse.obj E)) :
    phiPlusDist (a.act σ) (a.act τ) E hE =
      phiPlusDist σ τ (a.Φ.e.inverse.obj E) hE' := by
  unfold phiPlusDist
  change ENNReal.ofReal
      |(CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing a.Φ.e).phiPlus C E hE -
        (CategoryTheory.Triangulated.Slicing.mapEquiv τ.slicing a.Φ.e).phiPlus C E hE| = _
  rw [mapEquiv_phiPlus a.Φ.e σ.slicing E hE hE',
    mapEquiv_phiPlus a.Φ.e τ.slicing E hE hE']

/-- The acted `φ⁻` discrepancy at `E` is the original discrepancy at `Φ⁻¹E`. -/
theorem act_phiMinusDist (σ τ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E)
    (hE' : ¬IsZero (a.Φ.e.inverse.obj E)) :
    phiMinusDist (a.act σ) (a.act τ) E hE =
      phiMinusDist σ τ (a.Φ.e.inverse.obj E) hE' := by
  unfold phiMinusDist
  change ENNReal.ofReal
      |(CategoryTheory.Triangulated.Slicing.mapEquiv σ.slicing a.Φ.e).phiMinus C E hE -
        (CategoryTheory.Triangulated.Slicing.mapEquiv τ.slicing a.Φ.e).phiMinus C E hE| = _
  rw [mapEquiv_phiMinus a.Φ.e σ.slicing E hE hE',
    mapEquiv_phiMinus a.Φ.e τ.slicing E hE hE']

/-- The acted logarithmic mass discrepancy at `E` is the original discrepancy
at `Φ⁻¹E`. -/
theorem act_massDist (σ τ : StabilityCondition.WithClassMap C v) (E : C) :
    massDist (a.act σ) (a.act τ) E =
      massDist σ τ (a.Φ.e.inverse.obj E) := by
  unfold massDist
  rw [a.act_stabilityMass σ E, a.act_stabilityMass τ E]

/-- All three objectwise coordinates transport through the inverse-image
object. -/
theorem act_stabilityDistTerm (σ τ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E)
    (hE' : ¬IsZero (a.Φ.e.inverse.obj E)) :
    stabilityDistTerm (a.act σ) (a.act τ) E hE =
      stabilityDistTerm σ τ (a.Φ.e.inverse.obj E) hE' := by
  unfold stabilityDistTerm
  rw [a.act_phiPlusDist σ τ E hE hE', a.act_phiMinusDist σ τ E hE hE',
    a.act_massDist σ τ E]

/-- Forward-object form of the objectwise three-coordinate invariance. -/
theorem act_stabilityDistTerm_functor_obj
    (σ τ : StabilityCondition.WithClassMap C v) (E : C)
    (hE : ¬IsZero E)
    (hFE : ¬IsZero (a.Φ.e.functor.obj E)) :
    stabilityDistTerm (a.act σ) (a.act τ) (a.Φ.e.functor.obj E) hFE =
      stabilityDistTerm σ τ E hE := by
  have hIFE : ¬IsZero (a.Φ.e.inverse.obj (a.Φ.e.functor.obj E)) := fun h ↦
    hFE ((isZero_inverse_iff a.Φ.e (a.Φ.e.functor.obj E)).mp h)
  rw [a.act_stabilityDistTerm σ τ (a.Φ.e.functor.obj E) hFE hIFE]
  unfold stabilityDistTerm phiPlusDist phiMinusDist massDist
  have hpσ := CategoryTheory.Triangulated.Slicing.phiPlus_congr σ.slicing
    (a.Φ.e.unitIso.app E) hE hIFE
  have hpτ := CategoryTheory.Triangulated.Slicing.phiPlus_congr τ.slicing
    (a.Φ.e.unitIso.app E) hE hIFE
  have hmσ := CategoryTheory.Triangulated.Slicing.phiMinus_congr σ.slicing
    (a.Φ.e.unitIso.app E) hE hIFE
  have hmτ := CategoryTheory.Triangulated.Slicing.phiMinus_congr τ.slicing
    (a.Φ.e.unitIso.app E) hE hIFE
  have hmassσ := stabilityMass_congr σ (a.Φ.e.unitIso.app E)
  have hmassτ := stabilityMass_congr τ (a.Φ.e.unitIso.app E)
  change σ.slicing.phiPlus C E hE =
    σ.slicing.phiPlus C (a.Φ.e.inverse.obj (a.Φ.e.functor.obj E)) hIFE at hpσ
  change τ.slicing.phiPlus C E hE =
    τ.slicing.phiPlus C (a.Φ.e.inverse.obj (a.Φ.e.functor.obj E)) hIFE at hpτ
  change σ.slicing.phiMinus C E hE =
    σ.slicing.phiMinus C (a.Φ.e.inverse.obj (a.Φ.e.functor.obj E)) hIFE at hmσ
  change τ.slicing.phiMinus C E hE =
    τ.slicing.phiMinus C (a.Φ.e.inverse.obj (a.Φ.e.functor.obj E)) hIFE at hmτ
  change stabilityMass σ E =
    stabilityMass σ (a.Φ.e.inverse.obj (a.Φ.e.functor.obj E)) at hmassσ
  change stabilityMass τ E =
    stabilityMass τ (a.Φ.e.inverse.obj (a.Φ.e.functor.obj E)) at hmassτ
  rw [← hpσ, ← hpτ, ← hmσ, ← hmτ]
  rw [← hmassσ, ← hmassτ]

/-- A compatible autoequivalence pair preserves the complete three-coordinate
stability distance. -/
@[cites "stmt:a520a8d4f877:bridgeland2007.lem-8.2" (relation := no_claim)
        (note := "Full three-coordinate isometry using the ordinary finite HN mass. It is not identified with Lemma 8.2 because the acting group is AutPairQuot v, carrying compatible lattice data, rather than bare Aut(D).")]
theorem act_stabilityDist (σ τ : StabilityCondition.WithClassMap C v) :
    stabilityDist (a.act σ) (a.act τ) = stabilityDist σ τ := by
  apply le_antisymm
  · refine iSup₂_le fun E hE ↦ ?_
    have hE' : ¬IsZero (a.Φ.e.inverse.obj E) := fun h ↦
      hE ((isZero_inverse_iff a.Φ.e E).mp h)
    rw [a.act_stabilityDistTerm σ τ E hE hE']
    exact le_iSup₂
      (f := fun (X : C) (hX : ¬IsZero X) ↦ stabilityDistTerm σ τ X hX)
      (a.Φ.e.inverse.obj E) hE'
  · refine iSup₂_le fun E hE ↦ ?_
    have hFE : ¬IsZero (a.Φ.e.functor.obj E) := fun h ↦
      hE ((isZero_functor_iff a.Φ.e E).mp h)
    rw [← a.act_stabilityDistTerm_functor_obj σ τ E hE hFE]
    exact le_iSup₂
      (f := fun (X : C) (hX : ¬IsZero X) ↦
        stabilityDistTerm (a.act σ) (a.act τ) X hX)
      (a.Φ.e.functor.obj E) hFE

end

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPair

namespace CategoryTheory.Triangulated

noncomputable section

universe w u u'

variable {C : Type u} [Category.{w} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] (v : K₀ C →+ Λ)

/-- **The compatible autoequivalence group acts by full-distance isometries.** -/
@[cites "stmt:a520a8d4f877:bridgeland2007.lem-8.2" (relation := no_claim)
        (note := "Quotient-group form of AutPair.act_stabilityDist for the ordinary finite HN mass. The remaining boundary is group-theoretic: AutPairQuot v has extra compatible lattice data and is not proved equivalent to Aut(D).")]
theorem AutPairQuot_smul_stabilityDist
    (g : CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction.AutPairQuot v)
    (σ τ : StabilityCondition.WithClassMap C v) :
    stabilityDist (g • σ) (g • τ) = stabilityDist σ τ := by
  induction g using _root_.Quotient.inductionOn with
  | h a => exact a.act_stabilityDist σ τ

end

end CategoryTheory.Triangulated
