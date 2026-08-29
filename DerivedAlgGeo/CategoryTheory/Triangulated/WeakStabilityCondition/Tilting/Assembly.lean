/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.HarderNarasimhan.Heart
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Support.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.WeakStabilityCondition.Tilting.HarderNarasimhan

/-!
# Heart-level assembly for the weak upper tilt

This file gathers the three heart-level obligations in Proposition 14.16:

* the weak Harder--Narasimhan property;
* the noetherian zero-charge torsion subcategory;
* transport of the support property.

The generic HN recursion is discharged by
`hasHNProperty_of_quotientInduction`; the noetherian structure is discharged
by `phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty`; and support is
transported unconditionally by `phaseTilt_hasSupportProperty`.

The first constructor keeps the relative zero-charge chain condition and
rank-decreasing quotient induction visible.  The second discharges both from
phase-compatible envelopes.  The final constructor starts directly from the
raw Definition 14.12 tilting property: envelope Ext-vanishing terminates
zero-charge chains, while `TiltHarderNarasimhan` saturates the boundary factor
and iterates the cohomological reduction over the original `H⁻¹` and `H⁰`
HN filtrations.
-/

namespace CategoryTheory.Triangulated.WeakStabilityCondition

open CategoryTheory.Triangulated
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated

noncomputable section

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {v : K₀ C →+ V}

namespace WeakPreStabilityCondition

/-- The heart-level input to the ambient phase-tilt constructor.  It packages
the HN, noetherian, and support conclusions without itself asserting a
paper-level source statement. -/
structure PhaseTiltHeartObligations
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    (Zlin : V →ₗ[ℝ] ℂ) where
  /-- Harder--Narasimhan filtrations for the rotated weak function. -/
  hasHN :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).HasHNProperty
  /-- The tilted zero-charge class, with its torsion-pair and chain data. -/
  zeroChargeNoetherian : NoetherianTorsionSubcategory
    (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt
  /-- Its torsion class is exactly the new zero-charge class. -/
  zeroCharge_tors : zeroChargeNoetherian.pair.tors =
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge
  /-- Support for numerical classes of tilted weak-semistable objects. -/
  support :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).HasSupportProperty
      v (phaseTiltLinearCharge beta Zlin)

/-- Assemble all heart-level obligations for Proposition 14.16 from its two
remaining constructive seams. -/
noncomputable def phaseTiltHeartObligations
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin)
    (hacc : ∀ (E : C),
      ((slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt).heart E →
      ∀ c : SubobjectChain
        (slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).zeroCharge E,
        c.Terminates)
    (rank :
      ((slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt).heart.FullSubcategory
        → ℕ)
    (hquot : WeakStabilityFunction.HasHNQuotientInduction
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1) rank) :
    sigma.PhaseTiltHeartObligations beta hbeta0.le hbeta1 Zlin := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1
  let Nsharp :=
    sigma.phaseTiltNoetherianTorsionSubcategoryOfChainCondition
      beta hbeta0.le hbeta1 htilt hacc
  exact
    { hasHN := W.hasHNProperty_of_quotientInduction rank hquot
      zeroChargeNoetherian := Nsharp
      zeroCharge_tors := rfl
      support := sigma.phaseTilt_hasSupportProperty
        beta hbeta0 hbeta1 Zlin hcompat hsupport }

/-- Assemble the heart-level obligations with the relative zero-charge chain
condition discharged by phase-compatible envelopes.  Compared with
`phaseTiltHeartObligations`, this constructor removes the order-theoretic
`hacc` input: the envelope reduction, reduced-chain termination, and pullback
of the maximal zero-charge subobject are performed in `TiltNoetherian`.

The weak HN property is then obtained by boundary saturation followed by the
`H⁻¹` and `H⁰` filtration inductions in `TiltHarderNarasimhan`; no external
rank or quotient-induction premise remains. -/
noncomputable def phaseTiltHeartObligationsOfPhaseEnvelopes
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin)
    (henv : ∀ (F : C), phaseFree sigma.slicing beta F →
      sigma.HasPhaseTiltingEnvelope beta F) :
    sigma.PhaseTiltHeartObligations beta hbeta0.le hbeta1 Zlin := by
  let N0 := Classical.choose htilt.zeroCharge_noetherian
  have hN0 : N0.pair.tors = sigma.zeroCharge :=
    Classical.choose_spec htilt.zeroCharge_noetherian
  let hdec := sigma.phaseTilt_hasZeroChargeDecompositions_of_phaseEnvelopes
    beta hbeta0.le hbeta1 N0 hN0 henv
  let Nsharp :=
    sigma.phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
      beta hbeta0.le hbeta1 htilt hdec
  exact
    { hasHN := sigma.phaseTilt_hasHNProperty_of_zeroChargeDecompositions
        beta hbeta0 hbeta1 N0 hN0 hdec
      zeroChargeNoetherian := Nsharp
      zeroCharge_tors := rfl
      support := sigma.phaseTilt_hasSupportProperty
        beta hbeta0 hbeta1 Zlin hcompat hsupport }

/-- Assemble all heart-level obligations for the weak upper tilt directly
from Definition 14.12's raw `TiltingProperty`.

The raw envelope middle term is not asserted to be phase-free.  Instead,
`phaseTilt_zeroChargeChain_terminates_of_tiltingEnvelope` uses its
Ext-vanishing to bound tilted zero-charge subobject chains; maximal
subobjects then provide the phase-compatible decompositions consumed by the
HN and noetherian assemblies. -/
noncomputable def phaseTiltHeartObligationsOfTiltingProperty
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty)
    (Zlin : V →ₗ[ℝ] ℂ) (hcompat : ∀ x : V, Zlin x = sigma.Z x)
    (hsupport : sigma.weakStabilityFunctionOnHeart.HasSupportProperty v Zlin) :
    sigma.PhaseTiltHeartObligations beta hbeta0.le hbeta1 Zlin := by
  let N0 := Classical.choose htilt.zeroCharge_noetherian
  have hN0 : N0.pair.tors = sigma.zeroCharge :=
    Classical.choose_spec htilt.zeroCharge_noetherian
  let henv : ∀ (F : C), phaseFree sigma.slicing beta F →
      sigma.HasTiltingEnvelope F :=
    fun F hF => TiltingProperty.hasTiltingEnvelope_of_phaseFree
      sigma htilt beta hbeta1 F hF
  let hdec := sigma.phaseTilt_hasZeroChargeDecompositions_of_tiltingEnvelopes
    beta hbeta0.le hbeta1 N0 hN0 henv
  let Nsharp :=
    sigma.phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
      beta hbeta0.le hbeta1 htilt hdec
  exact
    { hasHN := sigma.phaseTilt_hasHNProperty_of_zeroChargeDecompositions
        beta hbeta0 hbeta1 N0 hN0 hdec
      zeroChargeNoetherian := Nsharp
      zeroCharge_tors := rfl
      support := sigma.phaseTilt_hasSupportProperty
        beta hbeta0 hbeta1 Zlin hcompat hsupport }

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Definition 14.12's tilting property supplies the heart-level HN property
for the rotated weak stability function, independently of any numerical
realization or support-property input. -/
theorem phaseTilt_hasHNPropertyOfTiltingProperty
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (htilt : sigma.TiltingProperty) :
    (sigma.phaseTiltWeakStabilityFunction
      beta hbeta0.le hbeta1).HasHNProperty := by
  let N0 := Classical.choose htilt.zeroCharge_noetherian
  have hN0 : N0.pair.tors = sigma.zeroCharge :=
    Classical.choose_spec htilt.zeroCharge_noetherian
  let henv : ∀ (F : C), phaseFree sigma.slicing beta F →
      sigma.HasTiltingEnvelope F :=
    fun F hF => TiltingProperty.hasTiltingEnvelope_of_phaseFree
      sigma htilt beta hbeta1 F hF
  let hdec := sigma.phaseTilt_hasZeroChargeDecompositions_of_tiltingEnvelopes
    beta hbeta0.le hbeta1 N0 hN0 henv
  exact sigma.phaseTilt_hasHNProperty_of_zeroChargeDecompositions
    beta hbeta0 hbeta1 N0 hN0 hdec

end WeakPreStabilityCondition

end


end CategoryTheory.Triangulated.WeakStabilityCondition
