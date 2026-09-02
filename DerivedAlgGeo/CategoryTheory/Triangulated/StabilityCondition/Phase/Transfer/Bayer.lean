/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Equivariance
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Order.Bayer

/-!
# The Bayer property under transfer

Lemma 3.25 of arXiv:2607.28411v1 ends with the observation that the Bayer
property of a slicing survives pullback: if `𝒫 ⪯ 𝒫 ⊗ L[l]` on the target,
then `f^♯𝒫 ⪯ f^♯𝒫 ⊗ f^*L[l]` on the source, "by Lemma 3.5(1) and Remark
3.14(3)".  The same two ingredients give the pushforward statement.  This
file proves that observation at the categorical level, where the twist is a
pair of compatible autoequivalences and the shift is a phase translation.

## Main results

* `HasBayerProperty.preimage`: the slicing-level Bayer property transfers
  along a phase-detecting functor to the transported twist.
* `BayerProperty.preimage`: the same for stability conditions with class
  maps, the twist carried by `AutPair.preimage`.

## Implementation notes

The proof is exactly the paper's: `Slicing.PreimageData.preimage_mapEquiv`
(Lemma 3.5(1)) identifies the twist of the transferred slicing with the
transfer of the twisted slicing, `Slicing.preimage_phaseShift_self` moves the
phase translation through the transfer, and
`Slicing.PrecedesWeak.preimage_of_preimageData` (Remark 3.14(3)) transports
the weak order.  No conservativity hypothesis is taken; the lifting witness
supplies it.

## References

* arXiv:2607.28411v1, Definition 3.16, Lemma 3.25, Remark 3.14(3).
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂ u'

namespace CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction

open CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **The Bayer property survives transfer.**  If `s ⪯ (PhiD • s)[l]` on the
target and `PhiC` is the compatible twist on the source, then the transferred
slicing satisfies `s_F ⪯ (PhiC • s_F)[l]`.  Geometrically: pullback and
pushforward of a slicing with the Bayer property for `L` have the Bayer
property for `f^*L`, as used in Lemma 3.25 of arXiv:2607.28411v1. -/
theorem HasBayerProperty.preimage {s : Slicing D} {F : C ⥤ D} [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated] (h : s.PreimageData F)
    (PhiC : TriEquiv C) (PhiD : TriEquiv D)
    (alpha : F ⋙ PhiD.e.inverse ≅ PhiC.e.inverse ⋙ F) (l : ℤ)
    (hB : HasBayerProperty s (AutQuot.mk PhiD) l) :
    HasBayerProperty (s.preimage F h) (AutQuot.mk PhiC) l := by
  change (s.preimage F h).PrecedesWeak C
    (((s.preimage F h).mapEquiv PhiC.e).phaseShift C (l : ℝ))
  change s.PrecedesWeak D ((s.mapEquiv PhiD.e).phaseShift D (l : ℝ)) at hB
  rw [← h.preimage_mapEquiv PhiC.e PhiD.e alpha, ← Slicing.preimage_phaseShift_self]
  exact Slicing.PrecedesWeak.preimage_of_preimageData F h _ hB

variable [IsTriangulated C] [IsTriangulated D]
variable {Λ : Type u'} [AddCommGroup Λ] {v : K₀ D →+ Λ}

/-- The paper-facing Bayer property of a stability condition transfers, with
the twist carried across the class map by `AutPair.preimage`.  Reduces to
`HasBayerProperty.preimage` through `bayerProperty_iff`; the class-lattice
component plays no role in the comparison of slicings. -/
theorem BayerProperty.preimage (σ : StabilityCondition.WithClassMap D v)
    (F : C ⥤ D) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (h : σ.slicing.PreimageData F) (aD : AutPair v) (PhiC : TriEquiv C)
    (alpha : F ⋙ aD.Φ.e.inverse ≅ PhiC.e.inverse ⋙ F) (l : ℤ)
    (hB : BayerProperty σ (AutPairQuot.mk aD) l) :
    BayerProperty (σ.preimage F h) (AutPairQuot.mk (aD.preimage F PhiC alpha)) l := by
  rw [bayerProperty_iff] at hB ⊢
  exact HasBayerProperty.preimage h PhiC aD.Φ alpha l hB

end CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.GroupAction
