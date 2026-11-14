/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeDecomposition
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeFiberCoefficient
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeGeneration
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeProjection

/-!
# Base change of a semiorthogonal decomposition

The formal core of Proposition 3.15 of arXiv:1902.08184: a semiorthogonal
decomposition of the source base-changes to one of the target, assembled from
the independent geometric inputs that the base-change API isolates.

## Main definitions

* `KFlatBaseChangeHypotheses.DecompositionSemiorthogonalityData` — presentable
  `S`-linearity, the K-flat fibre-coefficient comparison and faithful derived
  base change.
* `KFlatBaseChangeHypotheses.DecompositionCoreData` — that package with
  external-product generation and propagation from perfect objects to `Dqc`.
* `KFlatBaseChangeHypotheses.DecompositionProjectionData` — the chosen perfect and
  quasicoherent projections.
* `KFlatBaseChangeHypotheses.DecompositionProjectionHypotheses` — the geometric
  inputs the projections are built from: cocontinuity of the truncations,
  preservation of compact objects, and the compact-intersection identification.

## Main results

* `DecompositionSemiorthogonalityData.ofKFlatTensorCoefficientComparison` —
  semiorthogonality from the atomic K-flat tensor comparisons.
* `DecompositionSemiorthogonalityData.toCoreData` — semiorthogonality and
  fullness for both the perfect and the quasicoherent sequences.
* `DecompositionProjectionHypotheses.toProjectionData` — the `Dqc` projectors
  from componentwise compact-generator approximations, and the perfect ones by
  restriction to compact objects.
* `DecompositionCoreData.toDecompositionData` and
  `DecompositionCoreData.toDecompositionDataOfProjectionConstruction` — the
  existing `DecompositionData`.

## Implementation notes

The structures name inputs; none of them is constructed from scheme geometry
in this file. Each conversion consumes exactly the inputs it names.

## References

* Bayer, Lahoz, Macrì, Nuer, Perry, Stellari, *Stability conditions in
  families*, arXiv:1902.08184, Proposition 3.15.

## Tags

semiorthogonal decomposition, base change, K-flat, compact generation
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

namespace KFlatBaseChangeHypotheses

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeHypotheses X T)
  {ι : Type w} [Preorder ι]

/-- The semiorthogonality part of Proposition 3.15, with the source
triangulatedness and the presentably extended base-linearity retained for
later construction steps. -/
structure DecompositionSemiorthogonalityData
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (Q : D.SourceTensorHypotheses)
    (B : KFlatBasePullbackHypotheses X) where
  /-- The original source components are triangulated. -/
  sourceComponentsTriangulated : A.HasTriangulatedComponents
  /-- The `Perf(S)`-linear source action has been extended to `Dqc(S)`. -/
  sourceComponentsDqcSLinear :
    SourceTensorHypotheses.KFlatDqcSLinearComponents (D := D) Q B A
  /-- The perfect external-product envelopes are semiorthogonal. -/
  perfectSemiorthogonal :
    D.toDerivedBaseChangeData.PerfectComponentsSemiorthogonal A

namespace DecompositionSemiorthogonalityData

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
    (H : D.toDerivedBaseChangeData.CompactFiberTensorDuality)
    (Q : D.SourceTensorHypotheses)
    (B : KFlatBasePullbackHypotheses X)
    (presentable : SourceTensorHypotheses.PresentableBaseActionHypotheses
      (D := D) Q B.pullback)
    (K : KFlatFiberTensorHypotheses T)
    (V : KFlatCompactFiberDualityHypotheses K)
    (pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T))
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (faithful : D.DqcFaithfulBaseChange B.pullback pushBase pushFst)
    (C : CompactFiberProjectionFormula.KFlatTensorCoefficientComparison
      (D := D) P K V)
    (hS : SourceTensorHypotheses.KFlatSLinearComponents (D := D) Q B A) :
    D.DecompositionSemiorthogonalityData A Q B := by
  let hDqcS : SourceTensorHypotheses.KFlatDqcSLinearComponents
      (D := D) Q B A :=
    SourceTensorHypotheses.PresentableBaseActionHypotheses.dqcSLinearComponents
      (D := D) Q B.pullback presentable A hA hIso hCoprod hS
  exact
    { sourceComponentsTriangulated := hA
      sourceComponentsDqcSLinear := hDqcS
      perfectSemiorthogonal :=
        D.perfectComponentsSemiorthogonal_of_kFlatTensorCoefficientComparison
          A hA hIso H Q B K V pushBase pushFst adj P faithful C hDqcS }

end DecompositionSemiorthogonalityData

/-- The formal core of Proposition 3.15: the perfect and quasicoherent
base-change sequences are semiorthogonal and full, and the source linearity
used in the construction is available at the `Dqc(S)` level. -/
structure DecompositionCoreData
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (Q : D.SourceTensorHypotheses)
    (B : KFlatBasePullbackHypotheses X)
    (hcompact : D.PreservesCompactObjects) where
  /-- Semiorthogonality and presentable source linearity. -/
  semiorthogonality : D.DecompositionSemiorthogonalityData A Q B
  /-- External products generate the perfect base-change category. -/
  perfectFull :
    (D.toDerivedBaseChangeData.perfectCategorySequence A
      semiorthogonality.perfectSemiorthogonal).IsFull
  /-- The corresponding quasicoherent components generate `Dqc(X_T)`. -/
  quasicoherentFull :
    (D.toDerivedBaseChangeData.quasicoherentSequence A
      (D.toDerivedPreservesCompactObjects hcompact)
      semiorthogonality.perfectSemiorthogonal).IsFull

namespace DecompositionSemiorthogonalityData

variable {D : KFlatBaseChangeHypotheses X T}
  {A : SemiorthogonalSequence (SourceDqc X) ι}
  {Q : D.SourceTensorHypotheses}
  {B : KFlatBasePullbackHypotheses X}
  (C : D.DecompositionSemiorthogonalityData A Q B)

/-- Add the two generation inputs to the semiorthogonality package.

Classical generation by explicit external products proves perfect fullness;
compact generation and filtration/coproduct compatibility then propagate it
to quasicoherent fullness. -/
theorem toCoreData
    (hcompact : D.PreservesCompactObjects)
    (hgen : ObjectProperty.IsClassicalTriangulatedGenerator
      (D.toDerivedBaseChangeData.perfectCategoryExternalProductGenerators A))
    (G : D.toDerivedBaseChangeData.QuasicoherentFullnessPropagationHypotheses A
      (D.toDerivedPreservesCompactObjects hcompact)
      C.perfectSemiorthogonal) :
    D.DecompositionCoreData A Q B hcompact := by
  let hperfect := D.toDerivedBaseChangeData.perfectCategorySequence_isFull_of_externalProducts
    A C.perfectSemiorthogonal hgen
  exact
    { semiorthogonality := C
      perfectFull := hperfect
      quasicoherentFull := G.quasicoherentSequence_isFull hperfect }

end DecompositionSemiorthogonalityData

/-- The exact remaining projection boundary after the Proposition 3.15 core
has been assembled. No existence or cocontinuity theorem for these projectors
is inferred from semiorthogonality or generation. -/
structure DecompositionProjectionData
    {A : SemiorthogonalSequence (SourceDqc X) ι}
    {Q : D.SourceTensorHypotheses}
    {B : KFlatBasePullbackHypotheses X}
    {hcompact : D.PreservesCompactObjects}
    (C : D.DecompositionCoreData A Q B hcompact) where
  /-- Chosen right projections onto the perfect components. -/
  perfectProjections :
    (D.toDerivedBaseChangeData.perfectCategorySequence A
      C.semiorthogonality.perfectSemiorthogonal).RightProjectionData
  /-- Chosen right projections onto the quasicoherent components. -/
  quasicoherentProjections :
    (D.toDerivedBaseChangeData.quasicoherentSequence A
      (D.toDerivedPreservesCompactObjects hcompact)
      C.semiorthogonality.perfectSemiorthogonal).RightProjectionData
  /-- The ambient quasicoherent projection functors preserve coproducts. -/
  quasicoherentProjectionCocontinuous :
    ∀ i, (quasicoherentProjections.ambientProjection i).PreservesSmallCoproducts.{u}

/-- Geometric inputs from which all chosen projections in Proposition 3.15
are constructed. -/
structure DecompositionProjectionHypotheses
    {A : SemiorthogonalSequence (SourceDqc X) ι}
    {Q : D.SourceTensorHypotheses}
    {B : KFlatBasePullbackHypotheses X}
    {hcompact : D.PreservesCompactObjects}
    (C : D.DecompositionCoreData A Q B hcompact) : Prop where
  /-- Compact-generator approximations for the perfect envelopes. -/
  approximation : D.toDerivedBaseChangeData.QuasicoherentProjectionApproximationHypotheses A
  /-- The zero truncation attached to each approximation preserves
  coproducts in the scheme universe. -/
  truncationCocontinuous (i : ι) :
    Functor.PreservesSmallCoproducts.{u}
      ((approximation.componentApproximation i).tStructure.truncLE 0)
  /-- The quasicoherent projectors preserve compact objects, and compact
  intersection identifies their restrictions with the perfect components. -/
  compactRestriction :
    D.toDerivedBaseChangeData.PerfectProjectionRestrictionHypotheses A
      (D.toDerivedPreservesCompactObjects hcompact)
      C.semiorthogonality.perfectSemiorthogonal
      (approximation.quasicoherentProjections
        (D.toDerivedPreservesCompactObjects hcompact)
        C.semiorthogonality.perfectSemiorthogonal)

namespace DecompositionProjectionHypotheses

variable {D : KFlatBaseChangeHypotheses X T}
  {A : SemiorthogonalSequence (SourceDqc X) ι}
  {Q : D.SourceTensorHypotheses}
  {B : KFlatBasePullbackHypotheses X}
  {hcompact : D.PreservesCompactObjects}
  {C : D.DecompositionCoreData A Q B hcompact}
  (P : D.DecompositionProjectionHypotheses C)

/-- Construct all perfect and quasicoherent projection data required by the
Proposition 3.15 core. -/
noncomputable def toProjectionData : D.DecompositionProjectionData C where
  perfectProjections := P.compactRestriction.perfectProjections
  quasicoherentProjections :=
    P.approximation.quasicoherentProjections
      (D.toDerivedPreservesCompactObjects hcompact)
      C.semiorthogonality.perfectSemiorthogonal
  quasicoherentProjectionCocontinuous :=
    P.approximation.quasicoherentProjectionCocontinuous
      (D.toDerivedPreservesCompactObjects hcompact)
      C.semiorthogonality.perfectSemiorthogonal P.truncationCocontinuous

end DecompositionProjectionHypotheses

namespace DecompositionCoreData

variable {D : KFlatBaseChangeHypotheses X T}
  {A : SemiorthogonalSequence (SourceDqc X) ι}
  {Q : D.SourceTensorHypotheses}
  {B : KFlatBasePullbackHypotheses X}
  {hcompact : D.PreservesCompactObjects}
  (C : D.DecompositionCoreData A Q B hcompact)

/-- Supply the remaining projection data to obtain the existing
paper-strength decomposition package. -/
def toDecompositionData
    (P : D.DecompositionProjectionData C) :
    D.toDerivedBaseChangeData.DecompositionData A
      (D.toDerivedPreservesCompactObjects hcompact)
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
    (P : D.DecompositionProjectionHypotheses C) :
    D.toDerivedBaseChangeData.DecompositionData A
      (D.toDerivedPreservesCompactObjects hcompact)
      C.semiorthogonality.perfectSemiorthogonal :=
  C.toDecompositionData P.toProjectionData

end DecompositionCoreData

end KFlatBaseChangeHypotheses

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
