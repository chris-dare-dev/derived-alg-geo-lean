/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeDecomposition
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeFiberCoefficient
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeGeneration
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeProjection

/-!
# Proposition 3.15 assembly for scheme base change

This file assembles the formal core of Proposition 3.15 of
arXiv:1902.08184 from the independent geometric inputs isolated by the
base-change API.

The first package combines presentable `S`-linearity with the explicit
K-flat fibre-coefficient comparison and faithful derived base change. The
second adds external-product generation and propagation from perfect objects
to `Dqc`. Thus it produces semiorthogonality and fullness for both the perfect
and quasicoherent sequences.

The projection layer constructs the `Dqc` projectors from componentwise
compact-generator approximations and obtains the perfect projectors by
restriction to compact objects. `Proposition315ProjectionConstructionData`
records the remaining geometric inputs: cocontinuity of the corresponding
truncations, preservation of compact objects, and the compact-intersection
identification. It produces `Proposition315ProjectionData`, which in turn
converts the core package to `DecompositionData`.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

namespace KFlatBaseChangeData

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]

/-- The semiorthogonality part of Proposition 3.15, with the source
triangulatedness and the presentably extended base-linearity retained for
later construction steps. -/
structure Proposition315SemiorthogonalityData
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X) where
  /-- The original source components are triangulated. -/
  sourceComponentsTriangulated : A.HasTriangulatedComponents
  /-- The `Perf(S)`-linear source action has been extended to `Dqc(S)`. -/
  sourceComponentsDqcSLinear :
    SourceTensorData.KFlatDqcSLinearComponents (D := D) Q B A
  /-- The perfect external-product envelopes are semiorthogonal. -/
  perfectSemiorthogonal : D.PerfectComponentsSemiorthogonal A

namespace Proposition315SemiorthogonalityData

/-- Assemble semiorthogonality from the atomic K-flat tensor comparisons.

The source only has to be `Perf(S)`-linear at input. Presentability extends
that action to `Dqc(S)`, after which the explicit coefficient comparison and
faithful base change prove the required external-product Hom vanishing. -/
theorem ofKFlatTensorCoefficientComparison
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (hCoprod : ∀ j (κ : Type u),
      (A.component j).IsClosedUnderColimitsOfShape (Discrete κ))
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X)
    (presentable : SourceTensorData.PresentableBaseActionData
      (D := D) Q B.pullback)
    (K : KFlatFiberTensorData T)
    (V : KFlatCompactFiberDualityData K)
    (pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T))
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (faithful : D.DqcFaithfulBaseChange B.pullback pushBase pushFst)
    (C : CompactFiberProjectionFormula.KFlatTensorCoefficientComparison
      (D := D) P K V)
    (hS : SourceTensorData.KFlatSLinearComponents (D := D) Q B A) :
    D.Proposition315SemiorthogonalityData A Q B := by
  let hDqcS : SourceTensorData.KFlatDqcSLinearComponents
      (D := D) Q B A :=
    SourceTensorData.PresentableBaseActionData.dqcSLinearComponents
      (D := D) Q B.pullback presentable A hA hIso hCoprod hS
  exact
    { sourceComponentsTriangulated := hA
      sourceComponentsDqcSLinear := hDqcS
      perfectSemiorthogonal :=
        D.perfectComponentsSemiorthogonal_of_kFlatTensorCoefficientComparison
          A hA hIso H Q B K V pushBase pushFst adj P faithful C hDqcS }

end Proposition315SemiorthogonalityData

/-- The formal core of Proposition 3.15: the perfect and quasicoherent
base-change sequences are semiorthogonal and full, and the source linearity
used in the construction is available at the `Dqc(S)` level. -/
structure Proposition315CoreData
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X)
    (hcompact : D.PreservesCompactObjects) where
  /-- Semiorthogonality and presentable source linearity. -/
  semiorthogonality : D.Proposition315SemiorthogonalityData A Q B
  /-- External products generate the perfect base-change category. -/
  perfectFull :
    (D.perfectCategorySequence A
      semiorthogonality.perfectSemiorthogonal).IsFull
  /-- The corresponding quasicoherent components generate `Dqc(X_T)`. -/
  quasicoherentFull :
    (D.quasicoherentSequence A hcompact
      semiorthogonality.perfectSemiorthogonal).IsFull

namespace Proposition315SemiorthogonalityData

variable {D : KFlatBaseChangeData X T}
  {A : SemiorthogonalSequence (SourceDqc X) ι}
  {Q : D.SourceTensorData}
  {B : KFlatBasePullbackData X}
  (C : D.Proposition315SemiorthogonalityData A Q B)

/-- Add the two generation inputs to the semiorthogonality package.

Classical generation by explicit external products proves perfect fullness;
compact generation and filtration/coproduct compatibility then propagate it
to quasicoherent fullness. -/
theorem toCoreData
    (hcompact : D.PreservesCompactObjects)
    (hgen : (D.perfectCategoryExternalProductGenerators A).IsClassicalTriangulatedGenerator)
    (G : D.QuasicoherentFullnessPropagationData A hcompact
      C.perfectSemiorthogonal) :
    D.Proposition315CoreData A Q B hcompact := by
  let hperfect := D.perfectCategorySequence_isFull_of_externalProducts
    A C.perfectSemiorthogonal hgen
  exact
    { semiorthogonality := C
      perfectFull := hperfect
      quasicoherentFull := G.quasicoherentSequence_isFull hperfect }

end Proposition315SemiorthogonalityData

/-- The exact remaining projection boundary after the Proposition 3.15 core
has been assembled. No existence or cocontinuity theorem for these projectors
is inferred from semiorthogonality or generation. -/
structure Proposition315ProjectionData
    {A : SemiorthogonalSequence (SourceDqc X) ι}
    {Q : D.SourceTensorData}
    {B : KFlatBasePullbackData X}
    {hcompact : D.PreservesCompactObjects}
    (C : D.Proposition315CoreData A Q B hcompact) where
  /-- Chosen right projections onto the perfect components. -/
  perfectProjections :
    (D.perfectCategorySequence A
      C.semiorthogonality.perfectSemiorthogonal).RightProjectionData
  /-- Chosen right projections onto the quasicoherent components. -/
  quasicoherentProjections :
    (D.quasicoherentSequence A hcompact
      C.semiorthogonality.perfectSemiorthogonal).RightProjectionData
  /-- The ambient quasicoherent projection functors preserve coproducts. -/
  quasicoherentProjectionCocontinuous :
    ∀ i, (quasicoherentProjections.ambientProjection i).PreservesSmallCoproducts.{u}

/-- Geometric inputs from which all chosen projections in Proposition 3.15
are constructed. -/
structure Proposition315ProjectionConstructionData
    {A : SemiorthogonalSequence (SourceDqc X) ι}
    {Q : D.SourceTensorData}
    {B : KFlatBasePullbackData X}
    {hcompact : D.PreservesCompactObjects}
    (C : D.Proposition315CoreData A Q B hcompact) : Prop where
  /-- Compact-generator approximations for the perfect envelopes. -/
  approximation : D.QuasicoherentProjectionApproximationData A
  /-- The zero truncation attached to each approximation preserves
  coproducts in the scheme universe. -/
  truncationCocontinuous (i : ι) :
    Functor.PreservesSmallCoproducts.{u}
      ((approximation.componentApproximation i).tStructure.truncLE 0)
  /-- The quasicoherent projectors preserve compact objects, and compact
  intersection identifies their restrictions with the perfect components. -/
  compactRestriction :
    D.PerfectProjectionRestrictionData A hcompact
      C.semiorthogonality.perfectSemiorthogonal
      (approximation.quasicoherentProjections hcompact
        C.semiorthogonality.perfectSemiorthogonal)

namespace Proposition315ProjectionConstructionData

variable {D : KFlatBaseChangeData X T}
  {A : SemiorthogonalSequence (SourceDqc X) ι}
  {Q : D.SourceTensorData}
  {B : KFlatBasePullbackData X}
  {hcompact : D.PreservesCompactObjects}
  {C : D.Proposition315CoreData A Q B hcompact}
  (P : D.Proposition315ProjectionConstructionData C)

/-- Construct all perfect and quasicoherent projection data required by the
Proposition 3.15 core. -/
noncomputable def toProjectionData : D.Proposition315ProjectionData C where
  perfectProjections := P.compactRestriction.perfectProjections
  quasicoherentProjections :=
    P.approximation.quasicoherentProjections hcompact
      C.semiorthogonality.perfectSemiorthogonal
  quasicoherentProjectionCocontinuous :=
    P.approximation.quasicoherentProjectionCocontinuous hcompact
      C.semiorthogonality.perfectSemiorthogonal P.truncationCocontinuous

end Proposition315ProjectionConstructionData

namespace Proposition315CoreData

variable {D : KFlatBaseChangeData X T}
  {A : SemiorthogonalSequence (SourceDqc X) ι}
  {Q : D.SourceTensorData}
  {B : KFlatBasePullbackData X}
  {hcompact : D.PreservesCompactObjects}
  (C : D.Proposition315CoreData A Q B hcompact)

/-- Supply the remaining projection data to obtain the existing
paper-strength decomposition package. -/
def toDecompositionData
    (P : D.Proposition315ProjectionData C) :
    D.DecompositionData A hcompact
      C.semiorthogonality.perfectSemiorthogonal where
  sourceComponentsTriangulated :=
    C.semiorthogonality.sourceComponentsTriangulated
  perfectFull := C.perfectFull
  perfectProjections := P.perfectProjections
  quasicoherentFull := C.quasicoherentFull
  quasicoherentProjections := P.quasicoherentProjections
  quasicoherentProjectionCocontinuous :=
    P.quasicoherentProjectionCocontinuous

/-- Construct the projectors from compact-generator approximations and pass
directly to the paper-strength decomposition package. -/
noncomputable def toDecompositionDataOfProjectionConstruction
    (P : D.Proposition315ProjectionConstructionData C) :
    D.DecompositionData A hcompact
      C.semiorthogonality.perfectSemiorthogonal :=
  C.toDecompositionData P.toProjectionData

end Proposition315CoreData

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
