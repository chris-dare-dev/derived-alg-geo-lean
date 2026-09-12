/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeAdjunction
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeSequence
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Tensor-duality and adjunction Hom reductions after base change

This file splits the geometric Hom reduction for external products into two
composable inputs. `ExternalProductTensorDuality` moves the earlier pullback
factor out of the source external product, leaving a morphism out of
`pullFst.obj Fi`. The pullback-pushforward adjunction then returns that Hom to
the source category.

The remaining component-membership statement is isolated as
`PushforwardPreservesSourceComponents`; geometrically, this is where
`S`-linearity and a projection formula enter. Together these inputs imply the
perfect-component semiorthogonality required by the base-change sequence.
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

variable (A : SemiorthogonalSequence (SourceDqc X) ι)

/-- The target-side tensor-duality part of the external-product Hom
reduction.

The object `dualizedTarget Fj Gi Gj a b` packages the later external product,
the dual of the earlier compact fibre factor, and the two shifts. Its precise
geometric construction is left independent of the formal adjunction step. -/
structure ExternalProductTensorDuality where
  /-- The target-side object left after tensor duality exposes the first
  pullback factor. -/
  dualizedTarget :
    ∀ ⦃j : ι⦄, SourcePerfectPartCategory X (A.component j) →
      CompactDqcFiber T → CompactDqcFiber T → ℤ → ℤ → TargetDqc X T
  /-- Tensor duality rewrites a Hom between external products as a Hom out of
  the pullback of the earlier source factor. -/
  homEquiv :
    ∀ ⦃i j : ι⦄ (Fi : SourcePerfectPartCategory X (A.component i))
      (Gi : CompactDqcFiber T)
      (Fj : SourcePerfectPartCategory X (A.component j))
      (Gj : CompactDqcFiber T) (a b : ℤ),
      ((((D.externalProduct (A.component i)).obj Fi).obj Gi)⟦a⟧ ⟶
          (((D.externalProduct (A.component j)).obj Fj).obj Gj)⟦b⟧) ≃+
        (D.pullFst.functor.obj Fi.obj ⟶ dualizedTarget Fj Gi Gj a b)

namespace ExternalProductTensorDuality

/-- The pushforwards of the tensor-dualized target objects remain in the
source component of their later external-product factor.

This is the component-membership input expected from `S`-linearity and a
projection formula. -/
def PushforwardPreservesSourceComponents
    (H : D.ExternalProductTensorDuality A)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T)) : Prop :=
  ∀ ⦃j : ι⦄ (Fj : SourcePerfectPartCategory X (A.component j))
    (Gi Gj : CompactDqcFiber T) (a b : ℤ),
    A.component j
      (pushFst.functor.obj (H.dualizedTarget Fj Gi Gj a b))

/-- Compose target-side tensor duality with pullback-pushforward adjunction to
obtain the source-side external-product Hom reduction. -/
noncomputable def toHomReduction
    (H : D.ExternalProductTensorDuality A)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive] :
    D.ExternalProductHomReduction A where
  reductionObject _ Fj Gi Gj a b :=
    pushFst.functor.obj (H.dualizedTarget Fj Gi Gj a b)
  homEquiv _ _ Fi Gi Fj Gj a b :=
    (H.homEquiv Fi Gi Fj Gj a b).trans
      (adj.homAddEquiv Fi.obj (H.dualizedTarget Fj Gi Gj a b))

/-- The explicit pushforward-membership obligation is exactly the component
preservation required by the resulting source-side Hom reduction. -/
theorem toHomReduction_preservesSourceComponents
    (H : D.ExternalProductTensorDuality A)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (hH : PushforwardPreservesSourceComponents (D := D) (A := A) H pushFst) :
    (toHomReduction (D := D) (A := A) H pushFst adj).PreservesSourceComponents :=
  hH

end ExternalProductTensorDuality

/-- Tensor duality, the pullback-pushforward adjunction, and preservation of
the later source component prove semiorthogonality of the concrete external
products. -/
theorem perfectExternalProductsSemiorthogonal_of_tensorDualityAdjunction
    (H : D.ExternalProductTensorDuality A)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (hH : ExternalProductTensorDuality.PushforwardPreservesSourceComponents
      (D := D) (A := A) H pushFst) :
    D.PerfectExternalProductsSemiorthogonal A :=
  D.perfectExternalProductsSemiorthogonal_of_homReduction A
    (ExternalProductTensorDuality.toHomReduction
      (D := D) (A := A) H pushFst adj)
    (ExternalProductTensorDuality.toHomReduction_preservesSourceComponents
      (D := D) (A := A) H pushFst adj hH)

/-- Tensor duality, the pullback-pushforward adjunction, and preservation of
the later source component imply semiorthogonality of the perfect base-change
envelopes. -/
theorem perfectComponentsSemiorthogonal_of_tensorDualityAdjunction
    (hA : A.HasTriangulatedComponents)
    (H : D.ExternalProductTensorDuality A)
    (pushFst : DqcRightDerivedPushforward (baseChangeFst X T))
    (adj : D.pullFst.functor ⊣ pushFst.functor)
    [D.pullFst.functor.Additive]
    (hH : ExternalProductTensorDuality.PushforwardPreservesSourceComponents
      (D := D) (A := A) H pushFst) :
    D.PerfectComponentsSemiorthogonal A :=
  D.perfectComponentsSemiorthogonal_of_homReduction A hA
    (ExternalProductTensorDuality.toHomReduction
      (D := D) (A := A) H pushFst adj)
    (ExternalProductTensorDuality.toHomReduction_preservesSourceComponents
      (D := D) (A := A) H pushFst adj hH)

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
