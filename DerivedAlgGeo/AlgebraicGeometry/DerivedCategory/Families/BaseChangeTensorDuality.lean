/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeHomReduction
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeLinearity

/-!
# Compact-fibre tensor duality after base change

This file realizes the tensor-duality half of the external-product Hom
reduction as an adjunction for the actual K-flat derived tensor. For a compact
object `G` of `Dqc(T)`, `shiftedFiberTensor D G a` tensors on the right by its
pullback to `X_T` and then shifts by `a`. A right adjoint to this functor is the
precise duality input needed to expose the earlier source factor in a Hom
between shifted external products.

No global monoidal structure on unbounded `Dqc` is assumed. This keeps the
interface at the level currently constructed by the repository while still
pinning the duality datum to the genuine K-flat tensor bifunctor.
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

/-- Tensor on the right by the pullback of a compact object of `Dqc(T)`. -/
noncomputable def fiberTensor (G : CompactDqcFiber T) :
    TargetDqc X T ⥤ TargetDqc X T :=
  D.derivedTensor.flip.obj (D.pullSnd.functor.obj G.obj)

@[simp]
theorem fiberTensor_obj (G : CompactDqcFiber T) (E : TargetDqc X T) :
    (D.fiberTensor G).obj E =
      (D.derivedTensor.obj E).obj (D.pullSnd.functor.obj G.obj) :=
  rfl

/-- Tensor by a pulled-back compact fibre object and then shift. -/
noncomputable def shiftedFiberTensor (G : CompactDqcFiber T) (a : ℤ) :
    TargetDqc X T ⥤ TargetDqc X T :=
  D.fiberTensor G ⋙ shiftFunctor (TargetDqc X T) a

@[simp]
theorem shiftedFiberTensor_obj (G : CompactDqcFiber T) (a : ℤ)
    (E : TargetDqc X T) :
    (D.shiftedFiberTensor G a).obj E =
      ((D.derivedTensor.obj E).obj (D.pullSnd.functor.obj G.obj))⟦a⟧ :=
  rfl

/-- On a pulled-back source object, `shiftedFiberTensor` is definitionally the
shifted K-flat external product used to generate the base-change component. -/
@[simp]
theorem shiftedFiberTensor_obj_pullFst
    (P : ObjectProperty (SourceDqc X))
    (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) (a : ℤ) :
    (D.shiftedFiberTensor G a).obj (D.pullFst.functor.obj F.obj) =
      (((D.externalProduct P).obj F).obj G)⟦a⟧ :=
  rfl

/-- Duality for compact fibre factors, expressed as a right adjoint to the
actual shifted K-flat tensor twist.

Additivity is recorded explicitly because the downstream semiorthogonality
argument uses an additive Hom equivalence, while the current unbounded K-flat
tensor API does not yet bundle exactness or monoidal coherence. -/
structure CompactFiberTensorDuality where
  /-- The dual tensor-and-shift functor. -/
  rightAdjoint (G : CompactDqcFiber T) (a : ℤ) :
    TargetDqc X T ⥤ TargetDqc X T
  /-- Tensoring by the compact factor and shifting is additive. -/
  left_additive (G : CompactDqcFiber T) (a : ℤ) :
    (D.shiftedFiberTensor G a).Additive
  /-- The tensor-duality adjunction. -/
  adjunction (G : CompactDqcFiber T) (a : ℤ) :
    D.shiftedFiberTensor G a ⊣ rightAdjoint G a

namespace CompactFiberTensorDuality

/-- A compact-fibre tensor adjunction supplies the target-side Hom reduction
for every source semiorthogonal sequence. -/
noncomputable def toExternalProductTensorDuality
    (H : D.CompactFiberTensorDuality)
    (A : SemiorthogonalSequence (SourceDqc X) ι) :
    D.ExternalProductTensorDuality A where
  dualizedTarget _ Fj Gi Gj a b :=
    (H.rightAdjoint Gi a).obj
      ((((D.externalProduct (A.component _)).obj Fj).obj Gj)⟦b⟧)
  homEquiv _ _ Fi Gi Fj Gj a b := by
    letI : (D.shiftedFiberTensor Gi a).Additive := H.left_additive Gi a
    exact (H.adjunction Gi a).homAddEquiv
      (D.pullFst.functor.obj Fi.obj)
      ((((D.externalProduct (A.component _)).obj Fj).obj Gj)⟦b⟧)

/-- The remaining geometric obligation after compact-fibre duality: pushing
the dualized later external product to `X` preserves its source component. -/
def PushforwardPreservesSourceComponents
    (H : D.CompactFiberTensorDuality)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T)) : Prop :=
  ∀ ⦃j : ι⦄ (Fj : SourcePerfectPartCategory X (A.component j))
    (Gi Gj : CompactDqcFiber T) (a b : ℤ),
    A.component j
      (pushFst.functor.obj ((H.rightAdjoint Gi a).obj
        ((((D.externalProduct (A.component j)).obj Fj).obj Gj)⟦b⟧)))

/-- The compact-fibre pushforward obligation is exactly the preservation
condition required by the induced target-side Hom reduction. -/
theorem toExternalProductTensorDuality_preservesSourceComponents
    (H : D.CompactFiberTensorDuality)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (hH : PushforwardPreservesSourceComponents
      (D := D) H A pushFst) :
    ExternalProductTensorDuality.PushforwardPreservesSourceComponents
      (D := D) (A := A)
        (toExternalProductTensorDuality (D := D) H A) pushFst :=
  hH

end CompactFiberTensorDuality

/-- Compact-fibre tensor duality, pullback-pushforward adjunction, and the
remaining pushforward-membership input prove semiorthogonality of the perfect
base-change envelopes. -/
theorem perfectComponentsSemiorthogonal_of_compactFiberTensorDuality
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hA : A.HasTriangulatedComponents)
    (H : D.CompactFiberTensorDuality)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (hH : CompactFiberTensorDuality.PushforwardPreservesSourceComponents
      (D := D) H A pushFst) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_tensorDualityAdjunction A hA
    (CompactFiberTensorDuality.toExternalProductTensorDuality
      (D := D) H A) pushFst adj
    (CompactFiberTensorDuality.toExternalProductTensorDuality_preservesSourceComponents
      (D := D) H A pushFst hH)

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
