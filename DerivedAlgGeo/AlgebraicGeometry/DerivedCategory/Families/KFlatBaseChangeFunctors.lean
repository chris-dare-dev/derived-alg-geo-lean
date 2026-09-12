/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatBaseChange
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Lift

/-!
# Pullback between K-flat base-change categories

A morphism `f : T ⟶ U` over `S` induces `X ×_S T ⟶ X ×_S U`. This file constructs
its derived pullback from the K-flat resolution already carried by the target base-change data and
then restricts that functor to `(Dqc)_U ⟶ (Dqc)_T` and `D_U ⟶ D_T`.

The only component-level hypothesis is preservation of `(Dqc)`. Once the derived pullback also
preserves bounded coherent cohomology, preservation of `D_U` follows formally because `D_U` was
constructed as the inverse image of `(Dqc)_U` in that intrinsic bounded-coherent locus.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S}

/-- The morphism `X ×_S T ⟶ X ×_S U` induced by `f : T ⟶ U`. -/
abbrev baseChangeMap (X : SchemeBaseChange S) {T U : SchemeBaseChange S} (f : T ⟶ U) :
    X ⨯ T ⟶ X ⨯ U :=
  Limits.prod.map (𝟙 X) f

namespace DqcLeftDerivedPullback

variable {V W : SchemeBaseChange S} {f : V ⟶ W}

/-- A `Dqc` derived pullback preserves the intrinsic bounded-coherent locus. -/
def PreservesBoundedCoherent (pull : DqcLeftDerivedPullback f) : Prop :=
  ∀ E : Dqc.SchemeBoundedCoherentDqcCategory W.left,
    Dqc.schemeBoundedCoherentCohomology V.left (pull.functor.obj E.obj)

/-- Restrict a `Dqc` derived pullback to intrinsic bounded-coherent complexes. -/
noncomputable def boundedFunctor (pull : DqcLeftDerivedPullback f)
    (h : pull.PreservesBoundedCoherent) :
    Dqc.SchemeBoundedCoherentDqcCategory W.left ⥤
      Dqc.SchemeBoundedCoherentDqcCategory V.left :=
  (Dqc.schemeBoundedCoherentCohomology V.left).lift
    (Dqc.SchemeBoundedCoherentDqcCategory.ι W.left ⋙ pull.functor) h

/-- Forgetting bounded-coherent witnesses recovers the `Dqc` pullback. -/
noncomputable def boundedFunctorCompInclusion (pull : DqcLeftDerivedPullback f)
    (h : pull.PreservesBoundedCoherent) :
    pull.boundedFunctor h ⋙ Dqc.SchemeBoundedCoherentDqcCategory.ι V.left ≅
      Dqc.SchemeBoundedCoherentDqcCategory.ι W.left ⋙ pull.functor :=
  (Dqc.schemeBoundedCoherentCohomology V.left).liftCompιIso
    (Dqc.SchemeBoundedCoherentDqcCategory.ι W.left ⋙ pull.functor) h

@[simp]
theorem boundedFunctor_obj_obj (pull : DqcLeftDerivedPullback f)
    (h : pull.PreservesBoundedCoherent)
    (E : Dqc.SchemeBoundedCoherentDqcCategory W.left) :
    ((pull.boundedFunctor h).obj E).obj = pull.functor.obj E.obj :=
  rfl

end DqcLeftDerivedPullback

namespace KFlatBaseChangeData

variable {f : T ⟶ U}

/-- Construct pullback along `X ×_S T ⟶ X ×_S U` from the K-flat resolution on
`X ×_S U` carried by the target base-change data. -/
def pullbackAlong (D : KFlatBaseChangeData X U) (f : T ⟶ U)
    (hAcyclic : KFlatPullbackAcyclic D.tensorResolution (baseChangeMap X f))
    (hQuasicoherent : KFlatResolvedPullbackPreservesQuasicoherentCohomology
      D.tensorResolution (baseChangeMap X f)) :
    DqcLeftDerivedPullback (baseChangeMap X f) :=
  kFlatDqcLeftDerivedPullback D.tensorResolution (baseChangeMap X f)
    hAcyclic hQuasicoherent

/-- The exact component-level statement that pullback along `f` preserves the constructed
quasicoherent base-change component. -/
def PullbackPreservesQuasicoherentComponent
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f)) : Prop :=
  DU.quasicoherentComponent P ≤
    (DT.quasicoherentComponent P).inverseImage pull.functor

/-- Pullback between the constructed quasicoherent base-change categories. -/
noncomputable def quasicoherentPullback
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (h : PullbackPreservesQuasicoherentComponent DT DU P pull) :
    DU.QuasicoherentCategory P ⥤ DT.QuasicoherentCategory P :=
  ObjectProperty.liftOfLE pull.functor h

/-- Forgetting component witnesses recovers the ambient `Dqc` pullback. -/
noncomputable def quasicoherentPullbackCompInclusion
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (h : PullbackPreservesQuasicoherentComponent DT DU P pull) :
    quasicoherentPullback DT DU P pull h ⋙ (DT.quasicoherentComponent P).ι ≅
      (DU.quasicoherentComponent P).ι ⋙ pull.functor :=
  (DT.quasicoherentComponent P).liftCompιIso
    ((DU.quasicoherentComponent P).ι ⋙ pull.functor)
    (fun E ↦ h E.obj E.property)

/-- Preservation of the bounded component follows from preservation of `(Dqc)` together with
preservation of bounded coherent cohomology by the same derived pullback. -/
theorem pullback_preservesBoundedComponent
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
    (hBounded : pull.PreservesBoundedCoherent) :
    DU.boundedComponent P ≤
      (DT.boundedComponent P).inverseImage (pull.boundedFunctor hBounded) := by
  intro E hE
  exact hDqc E.obj hE

/-- Pullback between the constructed bounded base-change categories. -/
noncomputable def boundedPullback
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
    (hBounded : pull.PreservesBoundedCoherent) :
    DU.BoundedCategory P ⥤ DT.BoundedCategory P :=
  ObjectProperty.liftOfLE (pull.boundedFunctor hBounded)
    (pullback_preservesBoundedComponent DT DU P pull hDqc hBounded)

/-- Forgetting component witnesses recovers pullback on the intrinsic bounded-coherent loci. -/
noncomputable def boundedPullbackCompInclusion
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (pull : DqcLeftDerivedPullback (baseChangeMap X f))
    (hDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
    (hBounded : pull.PreservesBoundedCoherent) :
    boundedPullback DT DU P pull hDqc hBounded ⋙ (DT.boundedComponent P).ι ≅
      (DU.boundedComponent P).ι ⋙ pull.boundedFunctor hBounded :=
  (DT.boundedComponent P).liftCompιIso
    ((DU.boundedComponent P).ι ⋙ pull.boundedFunctor hBounded)
    (fun E ↦ pullback_preservesBoundedComponent DT DU P pull hDqc hBounded
      E.obj E.property)

/-- The fully K-flat form of pullback on `(Dqc)`: both the ambient derived functor and its
restriction to the constructed component are obtained from the resolutions. -/
noncomputable def kFlatQuasicoherentPullback
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (f : T ⟶ U)
    (hAcyclic : KFlatPullbackAcyclic DU.tensorResolution (baseChangeMap X f))
    (hQuasicoherent : KFlatResolvedPullbackPreservesQuasicoherentCohomology
      DU.tensorResolution (baseChangeMap X f))
    (hComponent : PullbackPreservesQuasicoherentComponent DT DU P
      (DU.pullbackAlong f hAcyclic hQuasicoherent)) :
    DU.QuasicoherentCategory P ⥤ DT.QuasicoherentCategory P :=
  quasicoherentPullback DT DU P (DU.pullbackAlong f hAcyclic hQuasicoherent) hComponent

/-- The fully K-flat form of pullback on `D`: the bounded restriction is constructed from the
same K-flat derived pullback used on `(Dqc)`. -/
noncomputable def kFlatBoundedPullback
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (f : T ⟶ U)
    (hAcyclic : KFlatPullbackAcyclic DU.tensorResolution (baseChangeMap X f))
    (hQuasicoherent : KFlatResolvedPullbackPreservesQuasicoherentCohomology
      DU.tensorResolution (baseChangeMap X f))
    (hComponent : PullbackPreservesQuasicoherentComponent DT DU P
      (DU.pullbackAlong f hAcyclic hQuasicoherent))
    (hBounded : (DU.pullbackAlong f hAcyclic hQuasicoherent).PreservesBoundedCoherent) :
    DU.BoundedCategory P ⥤ DT.BoundedCategory P :=
  boundedPullback DT DU P (DU.pullbackAlong f hAcyclic hQuasicoherent)
    hComponent hBounded

end KFlatBaseChangeData

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
