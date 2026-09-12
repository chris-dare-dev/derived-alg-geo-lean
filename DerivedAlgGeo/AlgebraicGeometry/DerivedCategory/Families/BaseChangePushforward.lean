/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatBaseChangeFunctors
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.RightDerivedPushforward

/-!
# Pushforward between constructed base-change categories

This file lifts a genuine `RightDerivedPushforward` to `Dqc`, restricts it to intrinsic
bounded-coherent complexes, and then restricts both functors to the K-flat base-change components.
The ambient right-derived universal property remains part of the data throughout.

For a morphism `f : T ⟶ U`, the induced morphism of fibre products is
`X ×_S T ⟶ X ×_S U`; pushforward therefore runs from the component over `T` to the
component over `U`.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange

open CategoryTheory CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S} {f : T ⟶ U}

/-- A genuine right-derived pushforward which preserves quasicoherent cohomology. -/
structure DqcRightDerivedPushforward (f : T ⟶ U) where
  /-- The right-derived pushforward on ambient derived categories. -/
  ambient : RightDerivedPushforward f
  /-- Ambient right-derived pushforward preserves quasicoherent cohomology. -/
  mapsQuasicoherent (E : Dqc.SchemeQuasicoherentDerivedCategory T.left) :
    Dqc.schemeQuasicoherentCohomology U.left (ambient.functor.obj E.obj)

namespace DqcRightDerivedPushforward

/-- Lift a genuine right-derived pushforward to the `Dqc` loci. -/
noncomputable def functor (P : DqcRightDerivedPushforward f) :
    Dqc.SchemeQuasicoherentDerivedCategory T.left ⥤
      Dqc.SchemeQuasicoherentDerivedCategory U.left :=
  (Dqc.schemeQuasicoherentCohomology U.left).lift
    (Dqc.SchemeQuasicoherentDerivedCategory.ι T.left ⋙ P.ambient.functor)
    P.mapsQuasicoherent

/-- Forgetting quasicoherence witnesses recovers the ambient right-derived pushforward. -/
noncomputable def functorCompInclusion (P : DqcRightDerivedPushforward f) :
    P.functor ⋙ Dqc.SchemeQuasicoherentDerivedCategory.ι U.left ≅
      Dqc.SchemeQuasicoherentDerivedCategory.ι T.left ⋙ P.ambient.functor :=
  (Dqc.schemeQuasicoherentCohomology U.left).liftCompιIso
    (Dqc.SchemeQuasicoherentDerivedCategory.ι T.left ⋙ P.ambient.functor)
    P.mapsQuasicoherent

@[simp]
theorem functor_obj_obj (P : DqcRightDerivedPushforward f)
    (E : Dqc.SchemeQuasicoherentDerivedCategory T.left) :
    (P.functor.obj E).obj = P.ambient.functor.obj E.obj :=
  rfl

/-- A `Dqc` right-derived pushforward preserves intrinsic bounded-coherent complexes. -/
def PreservesBoundedCoherent (P : DqcRightDerivedPushforward f) : Prop :=
  ∀ E : Dqc.SchemeBoundedCoherentDqcCategory T.left,
    Dqc.schemeBoundedCoherentCohomology U.left (P.functor.obj E.obj)

/-- Restrict right-derived pushforward to intrinsic bounded-coherent complexes. -/
noncomputable def boundedFunctor (P : DqcRightDerivedPushforward f)
    (h : P.PreservesBoundedCoherent) :
    Dqc.SchemeBoundedCoherentDqcCategory T.left ⥤
      Dqc.SchemeBoundedCoherentDqcCategory U.left :=
  (Dqc.schemeBoundedCoherentCohomology U.left).lift
    (Dqc.SchemeBoundedCoherentDqcCategory.ι T.left ⋙ P.functor) h

/-- Forgetting bounded-coherent witnesses recovers right-derived pushforward on `Dqc`. -/
noncomputable def boundedFunctorCompInclusion (P : DqcRightDerivedPushforward f)
    (h : P.PreservesBoundedCoherent) :
    P.boundedFunctor h ⋙ Dqc.SchemeBoundedCoherentDqcCategory.ι U.left ≅
      Dqc.SchemeBoundedCoherentDqcCategory.ι T.left ⋙ P.functor :=
  (Dqc.schemeBoundedCoherentCohomology U.left).liftCompιIso
    (Dqc.SchemeBoundedCoherentDqcCategory.ι T.left ⋙ P.functor) h

@[simp]
theorem boundedFunctor_obj_obj (P : DqcRightDerivedPushforward f)
    (h : P.PreservesBoundedCoherent)
    (E : Dqc.SchemeBoundedCoherentDqcCategory T.left) :
    ((P.boundedFunctor h).obj E).obj = P.functor.obj E.obj :=
  rfl

end DqcRightDerivedPushforward

namespace KFlatBaseChangeData

/-- The component-level condition that right-derived pushforward preserves `(Dqc)`. -/
def PushforwardPreservesQuasicoherentComponent
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (push : DqcRightDerivedPushforward (baseChangeMap X f)) : Prop :=
  DT.quasicoherentComponent P ≤
    (DU.quasicoherentComponent P).inverseImage push.functor

/-- Right-derived pushforward between the constructed quasicoherent base-change categories. -/
noncomputable def quasicoherentPushforward
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (h : PushforwardPreservesQuasicoherentComponent DT DU P push) :
    DT.QuasicoherentCategory P ⥤ DU.QuasicoherentCategory P :=
  ObjectProperty.liftOfLE push.functor h

/-- Forgetting component witnesses recovers right-derived pushforward on `Dqc`. -/
noncomputable def quasicoherentPushforwardCompInclusion
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (h : PushforwardPreservesQuasicoherentComponent DT DU P push) :
    quasicoherentPushforward DT DU P push h ⋙ (DU.quasicoherentComponent P).ι ≅
      (DT.quasicoherentComponent P).ι ⋙ push.functor :=
  (DU.quasicoherentComponent P).liftCompιIso
    ((DT.quasicoherentComponent P).ι ⋙ push.functor)
    (fun E ↦ h E.obj E.property)

/-- Preservation of the bounded base-change component follows formally from preservation of its
quasicoherent companion and of intrinsic bounded-coherent complexes. -/
theorem pushforward_preservesBoundedComponent
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (hDqc : PushforwardPreservesQuasicoherentComponent DT DU P push)
    (hBounded : push.PreservesBoundedCoherent) :
    DT.boundedComponent P ≤
      (DU.boundedComponent P).inverseImage (push.boundedFunctor hBounded) := by
  intro E hE
  exact hDqc E.obj hE

/-- Right-derived pushforward between the constructed bounded base-change categories. -/
noncomputable def boundedPushforward
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (hDqc : PushforwardPreservesQuasicoherentComponent DT DU P push)
    (hBounded : push.PreservesBoundedCoherent) :
    DT.BoundedCategory P ⥤ DU.BoundedCategory P :=
  ObjectProperty.liftOfLE (push.boundedFunctor hBounded)
    (pushforward_preservesBoundedComponent DT DU P push hDqc hBounded)

/-- Forgetting component witnesses recovers pushforward on intrinsic bounded-coherent loci. -/
noncomputable def boundedPushforwardCompInclusion
    (DT : KFlatBaseChangeData X T) (DU : KFlatBaseChangeData X U)
    (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
    (push : DqcRightDerivedPushforward (baseChangeMap X f))
    (hDqc : PushforwardPreservesQuasicoherentComponent DT DU P push)
    (hBounded : push.PreservesBoundedCoherent) :
    boundedPushforward DT DU P push hDqc hBounded ⋙ (DU.boundedComponent P).ι ≅
      (DT.boundedComponent P).ι ⋙ push.boundedFunctor hBounded :=
  (DU.boundedComponent P).liftCompιIso
    ((DT.boundedComponent P).ι ⋙ push.boundedFunctor hBounded)
    (fun E ↦ pushforward_preservesBoundedComponent DT DU P push hDqc hBounded
      E.obj E.property)

end KFlatBaseChangeData

end


end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange
