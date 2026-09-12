/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangePushforward

/-!
# Adjunctions on constructed base-change categories

Once the derived pullback and pushforward preserve the base-change components, their ambient
adjunction restricts to the full subcategories. The same argument first restricts the ambient
`Dqc` adjunction to intrinsic bounded-coherent complexes and then to `D_T`.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S} {f : T ⟶ U}

namespace DqcLeftDerivedPullback

/-- A `Dqc` left-derived pullback is essentially surjective when it has a
right adjoint with invertible counit. -/
theorem essSurj_of_adjunction_counit_isIso
    (pull : DqcLeftDerivedPullback f) (push : DqcRightDerivedPushforward f)
    (adj : pull.functor ⊣ push.functor)
    (hCounit : ∀ E, IsIso (adj.counit.app E)) : pull.functor.EssSurj := by
  constructor
  intro E
  letI := hCounit E
  exact adj.mem_essImage_of_counit_isIso E

/-- A `Dqc` left-derived pullback with a fully faithful right adjoint is
essentially surjective.  For a quasi-compact open immersion, this is the
formal categorical conclusion once derived pushforward is known to preserve
quasicoherent cohomology and remain fully faithful. -/
theorem essSurj_of_adjunction_of_fullyFaithful
    (pull : DqcLeftDerivedPullback f) (push : DqcRightDerivedPushforward f)
    (adj : pull.functor ⊣ push.functor) [push.functor.Full]
    [push.functor.Faithful] : pull.functor.EssSurj :=
  pull.essSurj_of_adjunction_counit_isIso push adj (fun _ ↦ inferInstance)

end DqcLeftDerivedPullback

namespace KFlatBaseChangeData

/-- An adjunction between the ambient `Dqc` pullback and pushforward restricts to the constructed
quasicoherent base-change components. -/
noncomputable def quasicoherentPullbackPushforwardAdjunction
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (adj : pull.functor ⊣ push.functor)
    (hPull : PullbackPreservesQuasicoherentComponent DT DU P pull)
    (hPush : PushforwardPreservesQuasicoherentComponent DT DU P push) :
    quasicoherentPullback DT DU P pull hPull ⊣
      quasicoherentPushforward DT DU P push hPush :=
  adj.restrictFullyFaithful
    (DU.quasicoherentComponent P).fullyFaithfulι
    (DT.quasicoherentComponent P).fullyFaithfulι
    (quasicoherentPullbackCompInclusion DT DU P pull hPull).symm
    (quasicoherentPushforwardCompInclusion DT DU P push hPush).symm

/-- The ambient `Dqc` adjunction restricts to intrinsic bounded-coherent complexes when both
functors preserve that locus. -/
noncomputable def boundedCoherentPullbackPushforwardAdjunction
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (adj : pull.functor ⊣ push.functor)
    (hPull : pull.PreservesBoundedCoherent)
    (hPush : push.PreservesBoundedCoherent) :
    pull.boundedFunctor hPull ⊣ push.boundedFunctor hPush :=
  adj.restrictFullyFaithful
    (Dqc.schemeBoundedCoherentCohomology (X ⨯ U).left).fullyFaithfulι
    (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).fullyFaithfulι
    (pull.boundedFunctorCompInclusion hPull).symm
    (push.boundedFunctorCompInclusion hPush).symm

/-- The pullback-pushforward adjunction on the constructed bounded base-change categories. -/
noncomputable def boundedPullbackPushforwardAdjunction
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (adj : pull.functor ⊣ push.functor)
    (hPullDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
    (hPushDqc : PushforwardPreservesQuasicoherentComponent DT DU P push)
    (hPullBounded : pull.PreservesBoundedCoherent)
    (hPushBounded : push.PreservesBoundedCoherent) :
    boundedPullback DT DU P pull hPullDqc hPullBounded ⊣
      boundedPushforward DT DU P push hPushDqc hPushBounded :=
  (boundedCoherentPullbackPushforwardAdjunction pull push adj
      hPullBounded hPushBounded).restrictFullyFaithful
    (DU.boundedComponent P).fullyFaithfulι
    (DT.boundedComponent P).fullyFaithfulι
    (boundedPullbackCompInclusion DT DU P pull hPullDqc hPullBounded).symm
    (boundedPushforwardCompInclusion DT DU P push hPushDqc hPushBounded).symm

/-- Lemma 3.18 for the constructed quasicoherent base-change component,
reduced to the geometric inputs: a fully faithful right adjoint on `Dqc` and
detection of component membership by pullback. -/
theorem quasicoherentPullbackOfDetection_essSurj_of_adjunction
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (adj : pull.functor ⊣ push.functor)
    (hDetect : ∀ E : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ U).left,
      DU.quasicoherentComponent P E ↔
        DT.quasicoherentComponent P (pull.functor.obj E))
    [push.functor.Full] [push.functor.Faithful] :
    (quasicoherentPullbackOfDetection DT DU P pull hDetect).EssSurj := by
  letI : pull.functor.EssSurj :=
    pull.essSurj_of_adjunction_of_fullyFaithful push adj
  infer_instance

/-- Lemma 3.18 for the constructed bounded base-change component.  Full
faithfulness of the `Dqc` right adjoint descends to the bounded-coherent
restriction, whose counit supplies essential surjectivity before the final
membership-detection restriction to `D_T`. -/
theorem boundedPullbackOfDetection_essSurj_of_adjunction
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (adj : pull.functor ⊣ push.functor)
    (hPull : pull.PreservesBoundedCoherent)
    (hPush : push.PreservesBoundedCoherent)
    (hDetect : ∀ E : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left,
      DU.boundedComponent P E ↔
        DT.boundedComponent P ((pull.boundedFunctor hPull).obj E))
    [push.functor.Full] [push.functor.Faithful] :
    (boundedPullbackOfDetection DT DU P pull hPull hDetect).EssSurj := by
  let boundedAdj :=
    boundedCoherentPullbackPushforwardAdjunction pull push adj hPull hPush
  letI : (pull.boundedFunctor hPull).EssSurj := by
    constructor
    intro E
    letI : IsIso (boundedAdj.counit.app E) := inferInstance
    exact boundedAdj.mem_essImage_of_counit_isIso E
  infer_instance

end KFlatBaseChangeData

end


end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
