/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeSequence

/-!
# Generation and fullness after scheme base change

This file isolates the generation inputs in Proposition 3.15 from the
semiorthogonality construction. Concrete K-flat external products define a
generator property on the compact carrier. If those objects classically
generate, the perfect base-change sequence is full.

For `Dqc`, compact generation reduces fullness to two formal compatibility
facts: perfect filtrations remain quasicoherent filtrations after forgetting
compactness, and the resulting total envelope is closed under coproducts.
Neither fact is replaced by a prepackaged fullness assumption.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated
  AlgebraicGeometry

universe u w

namespace KFlatBaseChangeData

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]
  (A : SemiorthogonalSequence (SourceDqc X) ι)

/-- Concrete K-flat external products, regarded as objects of the compact
carrier of `Dqc(X_T)`. -/
def perfectCategoryExternalProductGenerators :
    ObjectProperty (TargetPerfect X T) :=
  fun E ↦ ∃ i, ∃ (F : SourcePerfectPartCategory X (A.component i)),
    ∃ (G : CompactDqcFiber T),
      Nonempty (((D.externalProduct (A.component i)).obj F).obj G ≅ E.obj)

/-- Every external-product generator lies in the total property of the
perfect base-change sequence. -/
theorem perfectCategoryExternalProductGenerators_le_total
    (horth : D.PerfectComponentsSemiorthogonal A) :
    D.perfectCategoryExternalProductGenerators A ≤
      (D.perfectCategorySequence A horth).total := by
  rintro E ⟨i, F, G, h⟩
  apply (D.perfectCategorySequence A horth).component_le_total i
  change D.perfectEnvelope (A.component i) E.obj
  exact (D.perfectGenerators (A.component i)).le_triangEnvelope E.obj
    ⟨F, G, h⟩

/-- External-product generation implies fullness of the perfect
base-change sequence. -/
theorem perfectCategorySequence_isFull_of_externalProducts
    (horth : D.PerfectComponentsSemiorthogonal A)
    (hgen : (D.perfectCategoryExternalProductGenerators A).IsClassicalTriangulatedGenerator) :
    (D.perfectCategorySequence A horth).IsFull := by
  apply le_antisymm le_top
  rw [← hgen]
  exact ObjectProperty.monotone_triangEnvelope
    (D.perfectCategoryExternalProductGenerators_le_total A horth)

/-- The compatibility data needed to propagate perfect fullness to `Dqc`.

`perfectToQuasicoherent` is a filtration comparison, not a fullness field:
it only says that a finite perfect filtration remains a finite filtration
after forgetting compactness. Compact generation and coproduct closure then
prove quasicoherent fullness. -/
structure QuasicoherentFullnessPropagationData
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A) where
  /-- Compact objects generate the target `Dqc` category. -/
  targetCompactlyGenerated :
    (ObjectProperty.compactObjects.{u} (C := TargetDqc X T)).coprodClosure.{u} = ⊤
  /-- Perfect filtrations remain filtrations by the quasicoherent
  components after applying the compact-object inclusion. -/
  perfectToQuasicoherent (E : TargetPerfect X T) :
    (D.perfectCategorySequence A horth).total.triangEnvelope E →
      (D.quasicoherentSequence A hcompact horth).total.triangEnvelope E.obj
  /-- The finite envelope of the quasicoherent components is closed under
  scheme-universe coproducts. -/
  quasicoherentEnvelopeCoproducts (κ : Type u) :
    ObjectProperty.IsClosedUnderColimitsOfShape
      ((D.quasicoherentSequence A hcompact horth).total.triangEnvelope)
      (Discrete κ)

namespace QuasicoherentFullnessPropagationData

variable {D A}
  {hcompact : D.PreservesCompactObjects}
  {horth : D.PerfectComponentsSemiorthogonal A}
  (G : D.QuasicoherentFullnessPropagationData A hcompact horth)

include G

/-- Perfect fullness propagates to quasicoherent fullness through compact
generation and the stated filtration/coproduct compatibilities. -/
theorem quasicoherentSequence_isFull
    (hperfect : (D.perfectCategorySequence A horth).IsFull) :
    (D.quasicoherentSequence A hcompact horth).IsFull := by
  letI (κ : Type u) :
      ObjectProperty.IsClosedUnderColimitsOfShape
        ((D.quasicoherentSequence A hcompact horth).total.triangEnvelope)
        (Discrete κ) :=
    G.quasicoherentEnvelopeCoproducts κ
  apply le_antisymm le_top
  rw [← G.targetCompactlyGenerated]
  apply (ObjectProperty.compactObjects.{u} (C := TargetDqc X T)).coprodClosure_le
    (Q := (D.quasicoherentSequence A hcompact horth).total.triangEnvelope)
  intro E hE
  let E' : TargetPerfect X T := ⟨E, hE⟩
  apply G.perfectToQuasicoherent E'
  rw [hperfect]
  trivial

end QuasicoherentFullnessPropagationData

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
