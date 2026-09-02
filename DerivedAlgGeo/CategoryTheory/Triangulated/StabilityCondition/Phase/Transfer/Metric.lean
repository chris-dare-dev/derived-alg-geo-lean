/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.LocallyFinite
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Distance.Basic
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Metric.Mass.Uniqueness

/-!
# Mass and the stability metric under transfer

Lemma 3.5(3) and Lemma 3.9(3) of arXiv:2607.28411v1 compare the generalized
distance of two slicings before and after transfer.  On stability conditions
the metric has a third coordinate, the logarithmic ratio of masses, and it
behaves at least as well: the mass of an object for the transferred condition
is the mass of its image, because the HN filtration is detected by the
functor and the charges agree factor by factor.

## Main results

* `HNFiltration.mass_mapPreimage` and `stabilityMass_preimage`: the mass of
  an object for the transferred condition is the mass of its image.
* `phiPlusDist_preimage`, `phiMinusDist_preimage`, `massDist_preimage`: the
  three coordinates separately, each computed at the image object.
* `stabilityDistTerm_preimage`: every objectwise three-coordinate term of
  the transferred conditions is the corresponding term of the originals at
  the image object.
* `stabilityDist_preimage_le`: the full three-coordinate distance does not
  increase under transfer, extending `slicingDist_preimage_le`.

## Implementation notes

`stabilityMass` is choice-free, a supremum over all HN filtrations, and
`stabilityMass_eq_mass` identifies it with the mass of any one of them.  The
transfer statement is therefore proved on one filtration of the source
object, pushed forward by `HNFiltration.mapPreimage`, and then lifted to the
supremum on both sides.

## References

* arXiv:2607.28411v1, Lemmas 3.5(3) and 3.9(3), and the mass `m_σ` of
  Definition 2.2.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal BigOperators

universe v₁ u₁ v₂ u₂ u'

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ D →+ Λ}
variable (σ τ : StabilityCondition.WithClassMap D v) (F : C ⥤ D) [F.Additive]
  [F.CommShift ℤ] [F.IsTriangulated] (hσ : σ.slicing.PreimageData F)
  (hτ : τ.slicing.PreimageData F)

/-- The pushed-forward HN filtration has the same mass: its factors are the
images of the original factors, and the transferred charge of a factor is
the charge of its image. -/
theorem HNFiltration.mass_mapPreimage {E : C}
    (Fil : HNFiltration C (σ.slicing.preimage F hσ).P E) :
    (Fil.mapPreimage σ.slicing F hσ).mass σ = Fil.mass (σ.preimage F hσ) := by
  show ∑ i : Fin Fil.n, ENNReal.ofReal ‖σ.charge (F.obj (Fil.factor i))‖ =
    ∑ i : Fin Fil.n, ENNReal.ofReal ‖(σ.preimage F hσ).charge (Fil.factor i)‖
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [StabilityCondition.WithClassMap.preimage_charge]

/-- **Mass is computed on the image.**  The HN mass of an object for the
transferred stability condition equals the HN mass of its image for the
original one.  This is the mass coordinate behind Lemmas 3.5(3) and 3.9(3)
of arXiv:2607.28411v1, which the paper states only for phases. -/
theorem stabilityMass_preimage (E : C) :
    stabilityMass (σ.preimage F hσ) E = stabilityMass σ (F.obj E) := by
  obtain ⟨Fil⟩ := (σ.slicing.preimage F hσ).hn_exists E
  rw [stabilityMass_eq_mass (σ.preimage F hσ) Fil,
    stabilityMass_eq_mass σ (Fil.mapPreimage σ.slicing F hσ),
    HNFiltration.mass_mapPreimage]

/-- The `φ⁺` coordinate transports exactly: both `φ⁺` values are computed on
the image by `Slicing.preimage_phiPlus`, and the nonvanishing side condition
at the image is supplied by `Slicing.PreimageData.not_isZero_obj`, so no
conservativity hypothesis enters. -/
theorem phiPlusDist_preimage (E : C) (hE : ¬IsZero E) :
    phiPlusDist (σ.preimage F hσ) (τ.preimage F hτ) E hE =
      phiPlusDist σ τ (F.obj E) (hσ.not_isZero_obj hE) := by
  simp only [phiPlusDist, StabilityCondition.WithClassMap.preimage_slicing]
  rw [σ.slicing.preimage_phiPlus F hσ hσ.reflectsZeroObjects E hE,
    τ.slicing.preimage_phiPlus F hτ hτ.reflectsZeroObjects E hE]

/-- The `φ⁻` coordinate transports exactly, by `Slicing.preimage_phiMinus`,
mirroring `phiPlusDist_preimage`. -/
theorem phiMinusDist_preimage (E : C) (hE : ¬IsZero E) :
    phiMinusDist (σ.preimage F hσ) (τ.preimage F hτ) E hE =
      phiMinusDist σ τ (F.obj E) (hσ.not_isZero_obj hE) := by
  simp only [phiMinusDist, StabilityCondition.WithClassMap.preimage_slicing]
  rw [σ.slicing.preimage_phiMinus F hσ hσ.reflectsZeroObjects E hE,
    τ.slicing.preimage_phiMinus F hτ hτ.reflectsZeroObjects E hE]

/-- The mass coordinate needs no phase argument at all: `stabilityMass_preimage`
is an equality, so the logarithmic mass discrepancy transports without a
`≤`, unlike the supremum in `stabilityDist_preimage_le`. -/
theorem massDist_preimage (E : C) :
    massDist (σ.preimage F hσ) (τ.preimage F hτ) E = massDist σ τ (F.obj E) := by
  simp only [massDist, stabilityMass_preimage]

/-- The `max` of the three coordinates transports termwise.  This is what
makes `stabilityDist_preimage_le` a comparison of suprema over different index
sets rather than an equality: the transferred supremum ranges over the image
objects only. -/
theorem stabilityDistTerm_preimage (E : C) (hE : ¬IsZero E) :
    stabilityDistTerm (σ.preimage F hσ) (τ.preimage F hτ) E hE =
      stabilityDistTerm σ τ (F.obj E) (hσ.not_isZero_obj hE) := by
  simp only [stabilityDistTerm, phiPlusDist_preimage, phiMinusDist_preimage,
    massDist_preimage]

/-- **Transfer does not increase the stability distance.**  The transferred
supremum runs over the terms of the original one at image objects, so it is
bounded by the original supremum.  This extends `slicingDist_preimage_le`,
Lemmas 3.5(3) and 3.9(3) of arXiv:2607.28411v1, by the mass coordinate. -/
theorem stabilityDist_preimage_le :
    stabilityDist (σ.preimage F hσ) (τ.preimage F hτ) ≤ stabilityDist σ τ := by
  refine iSup₂_le fun E hE => ?_
  rw [stabilityDistTerm_preimage]
  exact stabilityDistTerm_le_stabilityDist σ τ (F.obj E) (hσ.not_isZero_obj hE)

end CategoryTheory.Triangulated
