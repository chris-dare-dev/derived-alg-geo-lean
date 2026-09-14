/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeSLinearity

/-!
# K-flat base-scheme action for base-change semiorthogonality

This file removes the last abstract pullback from the `S`-linearity route to
perfect-component semiorthogonality. A `KFlatBasePullbackData X` constructs
the derived pullback `Dqc(S) ⥤ Dqc(X)` from a K-flat resolution on `S`, its
pullback-acyclicity along `X → S`, and resolved quasicoherence preservation.

The resulting aliases and end-to-end theorems state both compact and
quasicoherent base-coefficient/`S`-linearity inputs entirely in terms of this
constructed pullback.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]

/-- K-flat geometric data constructing derived pullback along the structure
morphism `X → S`.

The resolution lives on `S`, the source category of the contravariant
pullback. The two remaining fields are exactly the operational hypotheses
required by `kFlatDqcLeftDerivedPullback`. -/
structure KFlatBasePullbackData (X : SchemeBaseChange S) where
  /-- A K-flat replacement on the base scheme. -/
  resolution : SchemeKFlatResolution S
  /-- Pullback along `X → S` is acyclic on the chosen replacements. -/
  acyclic : KFlatPullbackAcyclic resolution (toIdentityBaseChange X)
  /-- Resolved pullback along `X → S` preserves quasicoherent cohomology. -/
  quasicoherent :
    KFlatResolvedPullbackPreservesQuasicoherentCohomology
      resolution (toIdentityBaseChange X)

namespace KFlatBasePullbackData

/-- The genuine `Dqc` pullback along `X → S` constructed from the bundled
K-flat base resolution. -/
def pullback (B : KFlatBasePullbackData X) :
    DqcLeftDerivedPullback (toIdentityBaseChange X) :=
  kFlatDqcLeftDerivedPullback B.resolution (toIdentityBaseChange X)
    B.acyclic B.quasicoherent

end KFlatBasePullbackData

namespace KFlatBaseChangeData

namespace SourceTensorData

/-- `S`-linearity using the base action constructed from K-flat pullback data,
rather than a separately supplied derived pullback. -/
def KFlatSLinearComponents
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X)
    (A : SemiorthogonalSequence (SourceDqc X) ι) : Prop :=
  SLinearComponents (D := D) Q B.pullback A

/-- `Dqc(S)`-linearity using the base action constructed from K-flat
pullback data. -/
def KFlatDqcSLinearComponents
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X)
    (A : SemiorthogonalSequence (SourceDqc X) ι) : Prop :=
  DqcSLinearComponents (D := D) Q B.pullback A

end SourceTensorData

namespace CompactFiberProjectionFormula

/-- Projection coefficients represented by compact base objects through the
K-flat-constructed pullback `Dqc(S) ⥤ Dqc(X)`. -/
abbrev KFlatBaseCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (B : KFlatBasePullbackData X) :=
  BaseCoefficientData (D := D) P B.pullback

/-- Quasicoherent base coefficients represented through the
K-flat-constructed pullback `Dqc(S) ⥤ Dqc(X)`. -/
abbrev KFlatDqcBaseCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (B : KFlatBasePullbackData X) :=
  DqcBaseCoefficientData (D := D) P B.pullback

end CompactFiberProjectionFormula

/-- Compact-fibre duality, a first-projection formula with compact base
coefficients, and `S`-linearity prove perfect-component semiorthogonality,
with the base pullback constructed from K-flat resolution data. -/
theorem perfectComponentsSemiorthogonal_of_kFlatProjectionFormula_of_sLinear
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (C : CompactFiberProjectionFormula.KFlatBaseCoefficientData
      (D := D) P B)
    (hS : SourceTensorData.KFlatSLinearComponents
      (D := D) Q B A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_projectionFormula_of_sLinear
    A hA hIso H Q B.pullback pushFst adj P C hS

/-- The fully K-flat route from quasicoherent base coefficients and
`Dqc(S)`-linearity to perfect-component semiorthogonality. -/
theorem perfectComponentsSemiorthogonal_of_kFlatProjectionFormula_of_dqcSLinear
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (C : CompactFiberProjectionFormula.KFlatDqcBaseCoefficientData
      (D := D) P B)
    (hS : SourceTensorData.KFlatDqcSLinearComponents
      (D := D) Q B A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_projectionFormula_of_dqcSLinear
    A hA hIso H Q B.pullback pushFst adj P C hS

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
