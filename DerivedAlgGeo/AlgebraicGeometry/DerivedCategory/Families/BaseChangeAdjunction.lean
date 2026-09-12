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

end KFlatBaseChangeData

end


end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
