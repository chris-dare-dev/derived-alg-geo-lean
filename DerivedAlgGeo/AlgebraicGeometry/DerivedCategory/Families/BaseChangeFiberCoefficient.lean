/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeFaithfulness

/-!
# K-flat fibre coefficients for base-change semiorthogonality

This file makes the fibre object in the faithful-base-change argument
concrete. A K-flat resolution on `T` supplies the derived tensor on `Dqc(T)`,
and compact duality chooses `G⁺` right-adjoint to tensoring by each compact
fibre object `G`. The coefficient attached to `Gi[a]` and `Gj[b]` is then

`(Gj ⊗ Gi⁺)[b - a]`.

The remaining comparison with the coefficient produced by the first
projection formula is kept explicit. It is precisely the associativity,
pullback/tensor, and duality coherence still missing from the current K-flat
monoidal layer.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]

/-- A K-flat construction of the derived tensor on `Dqc(T)`. -/
structure KFlatFiberTensorData (T : SchemeBaseChange S) where
  /-- A K-flat replacement on the fibre scheme. -/
  resolution : SchemeKFlatResolution T.left
  /-- Resolved tensor preserves quasicoherent cohomology. -/
  tensorQuasicoherent :
    resolution.ResolvedTensorPreservesQuasicoherentCohomology

namespace KFlatFiberTensorData

/-- The derived tensor on `Dqc(T)` selected by the K-flat fibre data. -/
noncomputable def derivedTensor (K : KFlatFiberTensorData T) :
    BaseDqc T.left ⥤ BaseDqc T.left ⥤ BaseDqc T.left :=
  K.resolution.derivedTensorToDqc
    (K.resolution.preservesQuasicoherentCohomology_of_resolvedTensor
      K.tensorQuasicoherent)

@[simp]
theorem derivedTensor_obj_obj_obj (K : KFlatFiberTensorData T)
    (E F : BaseDqc T.left) :
    (((K.derivedTensor).obj E).obj F).obj =
      ((K.resolution.derivedTensor.obj E.obj).obj F.obj) :=
  rfl

end KFlatFiberTensorData

/-- Chosen compact duals for the actual K-flat tensor on `Dqc(T)`.

The adjunction records that tensoring on the right by `G⁺` is right adjoint
to tensoring on the right by `G`. -/
structure KFlatCompactFiberDualityData
    (K : KFlatFiberTensorData T) where
  /-- The chosen compact dual of a compact fibre object. -/
  dual : CompactDqcFiber T → CompactDqcFiber T
  /-- Tensor-duality adjunction for the chosen compact dual. -/
  adjunction (G : CompactDqcFiber T) :
    K.derivedTensor.flip.obj G.obj ⊣
      K.derivedTensor.flip.obj (dual G).obj

namespace KFlatCompactFiberDualityData

/-- The explicit fibre coefficient left by dualizing `Gi[a]` against
`Gj[b]`: tensor `Gj` by the chosen dual of `Gi`, then shift by `b - a`. -/
noncomputable def coefficient
    {K : KFlatFiberTensorData T}
    (V : KFlatCompactFiberDualityData K)
    (Gi Gj : CompactDqcFiber T) (a b : ℤ) : BaseDqc T.left :=
  ((K.derivedTensor.obj Gj.obj).obj (V.dual Gi).obj)⟦b - a⟧

@[simp]
theorem coefficient_obj
    {K : KFlatFiberTensorData T}
    (V : KFlatCompactFiberDualityData K)
    (Gi Gj : CompactDqcFiber T) (a b : ℤ) :
    (V.coefficient Gi Gj a b).obj =
      (((K.derivedTensor.obj Gj.obj).obj
        (V.dual Gi).obj)⟦b - a⟧).obj :=
  rfl

end KFlatCompactFiberDualityData

namespace KFlatBaseChangeData

/-- The target-side tensor coefficient obtained by pulling back the two
compact fibre factors separately, tensoring them with the target K-flat
tensor, and applying the shift left by compact duality.

This is the intermediate object at which the projection-formula comparison
and the monoidality of fibre pullback meet. -/
noncomputable def pulledBackTensorCoefficient
    (K : KFlatFiberTensorData T)
    (V : KFlatCompactFiberDualityData K)
    (Gi Gj : CompactDqcFiber T) (a b : ℤ) : TargetDqc X T :=
  ((D.derivedTensor.obj (D.pullSnd.functor.obj Gj.obj)).obj
    (D.pullSnd.functor.obj (V.dual Gi).obj))⟦b - a⟧

namespace CompactFiberProjectionFormula

/-- Atomic comparisons underlying the explicit K-flat fibre coefficient.

The first isomorphism is the projection-formula/duality calculation on
`X_T`. The second isomorphism is the tensor compatibility of pullback from
`T`. Keeping them separate prevents either geometric theorem from being
hidden in the final coefficient comparison. -/
structure KFlatTensorCoefficientComparison
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (K : KFlatFiberTensorData T)
    (V : KFlatCompactFiberDualityData K) where
  /-- Projection formula and compact duality identify the source coefficient
  with the pushforward of the separately pulled-back tensor coefficient. -/
  projectionIso (Gi Gj : CompactDqcFiber T) (a b : ℤ) :
    P.coefficient Gi Gj a b ≅
      pushFst.functor.obj
        (D.pulledBackTensorCoefficient K V Gi Gj a b)
  /-- Pullback from the fibre commutes with its K-flat tensor coefficient. -/
  pullbackTensorIso (Gi Gj : CompactDqcFiber T) (a b : ℤ) :
    D.pulledBackTensorCoefficient K V Gi Gj a b ≅
      D.pullSnd.functor.obj (V.coefficient Gi Gj a b)

/-- The first-projection coefficient is represented by the explicit K-flat
fibre tensor of the later factor with the dual of the earlier factor. -/
structure KFlatTensorCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (K : KFlatFiberTensorData T)
    (V : KFlatCompactFiberDualityData K) where
  /-- Comparison between the abstract projection coefficient and the
  pushforward of the explicit pulled-back fibre tensor coefficient. -/
  coefficientIso (Gi Gj : CompactDqcFiber T) (a b : ℤ) :
    P.coefficient Gi Gj a b ≅
      pushFst.functor.obj
        (D.pullSnd.functor.obj (V.coefficient Gi Gj a b))

namespace KFlatTensorCoefficientData

/-- Forget the explicit tensor formula while retaining its fibre coefficient
and comparison. -/
def toFiberCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    {P : D.CompactFiberProjectionFormula H Q pushFst}
    {K : KFlatFiberTensorData T}
    {V : KFlatCompactFiberDualityData K}
    (C : KFlatTensorCoefficientData (D := D) P K V) :
    FiberCoefficientData (D := D) P where
  fiberCoefficient Gi Gj a b := V.coefficient Gi Gj a b
  coefficientIso Gi Gj a b := C.coefficientIso Gi Gj a b

end KFlatTensorCoefficientData

namespace KFlatTensorCoefficientComparison

/-- Compose the projection/duality comparison with monoidality of fibre
pullback to obtain the coefficient comparison used by faithful base change. -/
def toKFlatTensorCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    {P : D.CompactFiberProjectionFormula H Q pushFst}
    {K : KFlatFiberTensorData T}
    {V : KFlatCompactFiberDualityData K}
    (C : KFlatTensorCoefficientComparison (D := D) P K V) :
    KFlatTensorCoefficientData (D := D) P K V where
  coefficientIso Gi Gj a b :=
    C.projectionIso Gi Gj a b ≪≫
      pushFst.functor.mapIso (C.pullbackTensorIso Gi Gj a b)

/-- The atomic K-flat comparisons also supply the fibre-coefficient datum
consumed by the faithful-base-change argument. -/
def toFiberCoefficientData
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    {P : D.CompactFiberProjectionFormula H Q pushFst}
    {K : KFlatFiberTensorData T}
    {V : KFlatCompactFiberDualityData K}
    (C : KFlatTensorCoefficientComparison (D := D) P K V) :
    FiberCoefficientData (D := D) P :=
  C.toKFlatTensorCoefficientData.toFiberCoefficientData

end KFlatTensorCoefficientComparison

end CompactFiberProjectionFormula

/-- The end-to-end semiorthogonality theorem with all three tensor operations
and the base pullback pinned to K-flat constructions, and with faithful base
change applied to the explicit dual fibre coefficient. -/
theorem perfectComponentsSemiorthogonal_of_kFlatTensorCoefficients
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X)
    (K : KFlatFiberTensorData T)
    (V : KFlatCompactFiberDualityData K)
    (pushBase : DqcRightDerivedPushforward (toIdentityBaseChange T))
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (faithful : D.DqcFaithfulBaseChange B.pullback pushBase pushFst)
    (C : CompactFiberProjectionFormula.KFlatTensorCoefficientData
      (D := D) P K V)
    (hS : SourceTensorData.KFlatDqcSLinearComponents
      (D := D) Q B A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_kFlatProjectionFormula_of_faithfulBaseChange
    A hA hIso H Q B pushBase pushFst adj P faithful
      C.toFiberCoefficientData hS

/-- The end-to-end semiorthogonality theorem stated using the two atomic
coherence comparisons rather than a bundled coefficient isomorphism. -/
theorem perfectComponentsSemiorthogonal_of_kFlatTensorCoefficientComparison
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (B : KFlatBasePullbackData X)
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
    (hS : SourceTensorData.KFlatDqcSLinearComponents
      (D := D) Q B A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_kFlatTensorCoefficients
    A hA hIso H Q B K V pushBase pushFst adj P faithful
      C.toKFlatTensorCoefficientData hS

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
