/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeDecomposition
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeLinearity

/-!
# Functoriality of base-changed semiorthogonal sequences

This file lifts the componentwise pullback, pushforward, and tensor interfaces
to the full base-changed sequences of Proposition 3.15 of arXiv:1902.08184.
It does not assert new geometric preservation results: the relevant
componentwise or perfect-envelope hypotheses remain explicit.

The linearity and projection-formula isomorphisms are likewise assembled as
families indexed by the components of the original sequence.
-/

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

universe u w

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S} {f : T ⟶ U}
  {ι : Type w} [Preorder ι]

namespace KFlatBaseChangeData

/-- Pullback preserves every quasicoherent component of a base-changed
sequence. -/
def PullbackPreservesQuasicoherentSequence
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (pull : DqcLeftDerivedPullback (baseChangeMap X f)) : Prop :=
  ∀ i, PullbackPreservesQuasicoherentComponent DT DU (A.component i) pull

/-- Pullback maps every perfect envelope into the corresponding target
quasicoherent component. -/
def PullbackMapsPerfectSequence
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (pull : DqcLeftDerivedPullback (baseChangeMap X f)) : Prop :=
  ∀ i, PullbackMapsPerfectEnvelope DT DU (A.component i) pull

/-- Perfect-envelope preservation and cocontinuity imply preservation of all
quasicoherent components at once. -/
theorem pullback_preservesQuasicoherentSequence_of_perfectSequence
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    [pull.functor.CommShift ℤ] [pull.functor.IsTriangulated]
    (hCoproducts : pull.functor.PreservesSmallCoproducts.{u})
    (hPerfect : PullbackMapsPerfectSequence DT DU A pull) :
    PullbackPreservesQuasicoherentSequence DT DU A pull :=
  fun i ↦ pullback_preservesQuasicoherentComponent_of_perfectEnvelope
    DT DU (A.component i) pull hCoproducts (hPerfect i)

/-- Pullback is compatible with the two quasicoherent base-change
sequences. -/
theorem quasicoherentSequence_pullback_compatible
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hcompactT : DT.PreservesCompactObjects)
    (hcompactU : DU.PreservesCompactObjects)
    (horthT : DT.PerfectComponentsSemiorthogonal A)
    (horthU : DU.PerfectComponentsSemiorthogonal A)
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hPull : PullbackPreservesQuasicoherentSequence DT DU A pull) :
    (DU.quasicoherentSequence A hcompactU horthU).CompatibleWith
      pull.functor (DT.quasicoherentSequence A hcompactT horthT) :=
  hPull

/-- Pullback is compatible with the bounded base-change sequences whenever
it preserves intrinsic bounded-coherent cohomology. -/
theorem boundedSequence_pullback_compatible
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hcompactT : DT.PreservesCompactObjects)
    (hcompactU : DU.PreservesCompactObjects)
    (horthT : DT.PerfectComponentsSemiorthogonal A)
    (horthU : DU.PerfectComponentsSemiorthogonal A)
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hPull : PullbackPreservesQuasicoherentSequence DT DU A pull)
    (hBounded : pull.PreservesBoundedCoherent) :
    (DU.boundedSequence A hcompactU horthU).CompatibleWith
      (pull.boundedFunctor hBounded)
      (DT.boundedSequence A hcompactT horthT) := by
  intro i
  change DU.boundedComponent (A.component i) ≤
    (DT.boundedComponent (A.component i)).inverseImage
      (pull.boundedFunctor hBounded)
  exact pullback_preservesBoundedComponent DT DU (A.component i) pull
    (hPull i) hBounded

/-- Pushforward preserves every quasicoherent component of a base-changed
sequence. -/
def PushforwardPreservesQuasicoherentSequence
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (push : DqcRightDerivedPushforward (baseChangeMap X f)) : Prop :=
  ∀ i, PushforwardPreservesQuasicoherentComponent DT DU (A.component i) push

/-- Pushforward maps every perfect envelope into the corresponding target
quasicoherent component. -/
def PushforwardMapsPerfectSequence
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (push : DqcRightDerivedPushforward (baseChangeMap X f)) : Prop :=
  ∀ i, PushforwardMapsPerfectEnvelope DT DU (A.component i) push

/-- Perfect-envelope preservation and cocontinuity imply preservation of all
quasicoherent components under pushforward. -/
theorem pushforward_preservesQuasicoherentSequence_of_perfectSequence
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    [push.functor.CommShift ℤ] [push.functor.IsTriangulated]
    (hCoproducts : push.functor.PreservesSmallCoproducts.{u})
    (hPerfect : PushforwardMapsPerfectSequence DT DU A push) :
    PushforwardPreservesQuasicoherentSequence DT DU A push :=
  fun i ↦ pushforward_preservesQuasicoherentComponent_of_perfectEnvelope
    DT DU (A.component i) push hCoproducts (hPerfect i)

/-- Pushforward is compatible with the two quasicoherent base-change
sequences. -/
theorem quasicoherentSequence_pushforward_compatible
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hcompactT : DT.PreservesCompactObjects)
    (hcompactU : DU.PreservesCompactObjects)
    (horthT : DT.PerfectComponentsSemiorthogonal A)
    (horthU : DU.PerfectComponentsSemiorthogonal A)
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (hPush : PushforwardPreservesQuasicoherentSequence DT DU A push) :
    (DT.quasicoherentSequence A hcompactT horthT).CompatibleWith
      push.functor (DU.quasicoherentSequence A hcompactU horthU) :=
  hPush

/-- Pushforward is compatible with the bounded base-change sequences whenever
it preserves intrinsic bounded-coherent cohomology. -/
theorem boundedSequence_pushforward_compatible
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hcompactT : DT.PreservesCompactObjects)
    (hcompactU : DU.PreservesCompactObjects)
    (horthT : DT.PerfectComponentsSemiorthogonal A)
    (horthU : DU.PerfectComponentsSemiorthogonal A)
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (hPush : PushforwardPreservesQuasicoherentSequence DT DU A push)
    (hBounded : push.PreservesBoundedCoherent) :
    (DT.boundedSequence A hcompactT horthT).CompatibleWith
      (push.boundedFunctor hBounded)
      (DU.boundedSequence A hcompactU horthU) := by
  intro i
  change DT.boundedComponent (A.component i) ≤
    (DU.boundedComponent (A.component i)).inverseImage
      (push.boundedFunctor hBounded)
  exact pushforward_preservesBoundedComponent DT DU (A.component i) push
    (hPush i) hBounded

/-- Tensor by `B` preserves every quasicoherent component of the sequence. -/
def TensorPreservesQuasicoherentSequence
    (D : KFlatBaseChangeData X T)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (B : TargetDqc X T) : Prop :=
  ∀ i, D.TensorPreservesQuasicoherentComponent (A.component i) B

/-- Tensor by `B` is compatible with the quasicoherent base-change sequence. -/
theorem quasicoherentSequence_tensor_compatible
    (D : KFlatBaseChangeData X T)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (hcompact : D.PreservesCompactObjects)
    (horth : D.PerfectComponentsSemiorthogonal A)
    (B : TargetDqc X T)
    (hTensor : D.TensorPreservesQuasicoherentSequence A B) :
    (D.quasicoherentSequence A hcompact horth).CompatibleWith
      (D.derivedTensor.obj B) (D.quasicoherentSequence A hcompact horth) :=
  hTensor

/-- Pullback linearity, simultaneously parameterized by every component of
the base-changed sequence. -/
noncomputable def quasicoherentSequencePullbackTensorIso
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hPull : PullbackPreservesQuasicoherentSequence DT DU A pull)
    (hTensor : PullbackTensorCompatibility DT DU pull)
    (B : TargetDqc X U)
    (hBU : DU.TensorPreservesQuasicoherentSequence A B)
    (hBT : DT.TensorPreservesQuasicoherentSequence A (pull.functor.obj B))
    (i : ι) :
    DU.quasicoherentTensor (A.component i) B (hBU i) ⋙
        quasicoherentPullback DT DU (A.component i) pull (hPull i) ≅
      quasicoherentPullback DT DU (A.component i) pull (hPull i) ⋙
        DT.quasicoherentTensor (A.component i) (pull.functor.obj B) (hBT i) :=
  quasicoherentPullbackTensorIso DT DU (A.component i) pull (hPull i)
    hTensor B (hBU i) (hBT i)

/-- The projection formula, simultaneously parameterized by every component
of the base-changed sequence. -/
noncomputable def quasicoherentSequenceProjectionFormulaIso
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (A : SemiorthogonalSequence (SourceDqc X) ι)
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (hPush : PushforwardPreservesQuasicoherentSequence DT DU A push)
    (hProjection : ProjectionFormula DT DU pull push)
    (B : TargetDqc X U)
    (hBT : DT.TensorPreservesQuasicoherentSequence A (pull.functor.obj B))
    (hBU : DU.TensorPreservesQuasicoherentSequence A B)
    (i : ι) :
    DT.quasicoherentTensor (A.component i) (pull.functor.obj B) (hBT i) ⋙
        quasicoherentPushforward DT DU (A.component i) push (hPush i) ≅
      quasicoherentPushforward DT DU (A.component i) push (hPush i) ⋙
        DU.quasicoherentTensor (A.component i) B (hBU i) :=
  quasicoherentProjectionFormulaIso DT DU (A.component i) pull push
    (hPush i) hProjection B (hBT i) (hBU i)

end KFlatBaseChangeData

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
