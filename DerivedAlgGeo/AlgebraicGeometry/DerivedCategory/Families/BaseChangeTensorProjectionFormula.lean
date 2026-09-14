/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeTensorDuality

/-!
# Projection formula for external-product Hom reductions

This file separates the last component-membership input in the
semiorthogonality proof into a projection-formula isomorphism and source
tensor closure.

The source tensor is constructed from the same K-flat resolution on `X` that
the base-change datum uses for the first pullback. A
`CompactFiberProjectionFormula` identifies the pushforward of a dualized
external product with the later source factor tensored by a coefficient on
`X`. Membership then follows either from closure under these coefficients or
from the stronger condition that every source component is a right tensor
ideal.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

variable {S : Scheme.{u}} {X T : SchemeBaseChange S}
  (D : KFlatBaseChangeData X T)
  {ι : Type w} [Preorder ι]

namespace KFlatBaseChangeData

/-- The additional quasicoherence input needed to use the first K-flat
resolution as the derived tensor on the source `Dqc(X)`. -/
structure SourceTensorData where
  /-- Resolved tensor on `X` preserves quasicoherent cohomology. -/
  tensorQuasicoherent :
    D.fstResolution.ResolvedTensorPreservesQuasicoherentCohomology

namespace SourceTensorData

/-- The source K-flat derived tensor selected by `SourceTensorData`. -/
noncomputable def derivedTensor (Q : D.SourceTensorData) :
    SourceDqc X ⥤ SourceDqc X ⥤ SourceDqc X :=
  D.fstResolution.derivedTensorToDqc
    (D.fstResolution.preservesQuasicoherentCohomology_of_resolvedTensor
      Q.tensorQuasicoherent)

@[simp]
theorem derivedTensor_obj_obj_obj (Q : D.SourceTensorData)
    (E F : SourceDqc X) :
    (((Q.derivedTensor).obj E).obj F).obj =
      ((D.fstResolution.derivedTensor.obj E.obj).obj F.obj) :=
  rfl

/-- Every source component is closed under tensoring on the right by an
arbitrary object of `Dqc(X)`.

This strong form is useful as a generic sufficient condition. The projection
formula below also exposes a weaker coefficient-local condition. -/
def RightTensorClosedComponents
    (Q : D.SourceTensorData)
    (A : SemiorthogonalSequence (SourceDqc X) ι) : Prop :=
  ∀ ⦃j : ι⦄ (F : SourceDqc X), A.component j F →
    ∀ B : SourceDqc X,
      A.component j ((Q.derivedTensor.obj F).obj B)

end SourceTensorData

/-- Projection formula for the dualized external products used in the Hom
reduction.

The coefficient depends only on the two compact fibre factors and shifts.
The isomorphism is stated for every source object, independently of a chosen
semiorthogonal sequence. -/
structure CompactFiberProjectionFormula
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T)) where
  /-- The source-side coefficient left after duality and pushforward. -/
  coefficient :
    CompactDqcFiber T → CompactDqcFiber T → ℤ → ℤ → SourceDqc X
  /-- Pushing forward a dualized shifted external tensor is tensoring its
  source factor by the corresponding coefficient. -/
  iso (F : SourceDqc X) (Gi Gj : CompactDqcFiber T) (a b : ℤ) :
    pushFst.functor.obj ((H.rightAdjoint Gi a).obj
        ((D.shiftedFiberTensor Gj b).obj (D.pullFst.functor.obj F))) ≅
      (Q.derivedTensor.obj F).obj (coefficient Gi Gj a b)

namespace CompactFiberProjectionFormula

/-- The exact source-linearity condition needed for a particular projection
formula: its coefficient twists preserve the corresponding source
components. -/
def PreservesSourceComponents
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (A : SemiorthogonalSequence (SourceDqc X) ι) : Prop :=
  ∀ ⦃j : ι⦄ (Fj : SourcePerfectPartCategory X (A.component j))
    (Gi Gj : CompactDqcFiber T) (a b : ℤ),
    A.component j
      ((Q.derivedTensor.obj Fj.obj).obj (P.coefficient Gi Gj a b))

/-- Closure of all source components under right tensor twists implies the
coefficient-local source-linearity condition. -/
theorem preservesSourceComponents_of_rightTensorClosed
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : SourceTensorData.RightTensorClosedComponents
      (D := D) Q A) :
    PreservesSourceComponents (D := D) P A := by
  intro j Fj Gi Gj a b
  exact hA Fj.obj Fj.property.1 (P.coefficient Gi Gj a b)

/-- The projection-formula isomorphism transports source tensor closure back
to the pushforward object required by compact-fibre duality. -/
theorem pushforwardPreservesSourceComponents
    {H : D.CompactFiberTensorDuality}
    {Q : D.SourceTensorData}
    {pushFst : DqcRightDerivedPushforward (baseChangeFst X T)}
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (hP : PreservesSourceComponents (D := D) P A) :
    CompactFiberTensorDuality.PushforwardPreservesSourceComponents
      (D := D) H A pushFst := by
  intro j Fj Gi Gj a b
  letI : (A.component j).IsClosedUnderIsomorphisms := hIso j
  change A.component j
    (pushFst.functor.obj ((H.rightAdjoint Gi a).obj
      ((D.shiftedFiberTensor Gj b).obj (D.pullFst.functor.obj Fj.obj))))
  exact (A.component j).prop_of_iso (P.iso Fj.obj Gi Gj a b).symm
    (hP Fj Gi Gj a b)

end CompactFiberProjectionFormula

/-- Compact-fibre duality, the first-projection formula, and coefficient-local
source tensor closure prove perfect-component semiorthogonality. -/
theorem perfectComponentsSemiorthogonal_of_projectionFormula
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (hP : CompactFiberProjectionFormula.PreservesSourceComponents
      (D := D) P A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_compactFiberTensorDuality A hA H
    pushFst adj
    (CompactFiberProjectionFormula.pushforwardPreservesSourceComponents
      (D := D) P A hIso hP)

/-- The same conclusion under the stronger, sequence-wide assumption that
every source component is closed under every right tensor twist on `Dqc(X)`. -/
theorem perfectComponentsSemiorthogonal_of_projectionFormula_of_rightTensorClosed
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (hIso : ∀ j, (A.component j).IsClosedUnderIsomorphisms)
    (H : D.CompactFiberTensorDuality)
    (Q : D.SourceTensorData)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (P : D.CompactFiberProjectionFormula H Q pushFst)
    (hTensor : SourceTensorData.RightTensorClosedComponents
      (D := D) Q A) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_projectionFormula A hA hIso H Q
    pushFst adj P
    (CompactFiberProjectionFormula.preservesSourceComponents_of_rightTensorClosed
      (D := D) P A hTensor)

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
