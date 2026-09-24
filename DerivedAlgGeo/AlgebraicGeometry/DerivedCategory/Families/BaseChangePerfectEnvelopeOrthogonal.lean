/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatBaseChangeFunctors
import DerivedAlgGeo.CategoryTheory.ObjectProperty.Orthogonal

/-!
# Testing bounded pullback orthogonality on the perfect envelope

The quasicoherent base-change component is the coproduct-and-extension closure
of its perfect envelope. Thus vanishing of maps from perfect-envelope objects
into a pulled-back bounded object extends to maps from the whole quasicoherent
component. The fully faithful bounded-coherent inclusion then reflects the
vanishing needed for the bounded right orthogonal.

The perfect-envelope vanishing is an explicit geometric hypothesis here. This
file does not establish relative Hom base change or derive that hypothesis
from pullback preservation of components.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S} {f : T ⟶ U}
  (DT : DerivedBaseChangeData X T) (DU : DerivedBaseChangeData X U)
  (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
  (pull : DqcLeftDerivedPullback (baseChangeMap X f))

/-- Vanishing against the target perfect envelope suffices for bounded pullback
to carry the source right orthogonal into the target right orthogonal. The
vanishing premise is not supplied by component preservation alone. -/
theorem boundedPullback_rightOrthogonal_of_perfectEnvelope
    (hBounded : pull.PreservesBoundedCoherent)
    (hPerfect :
      ∀ (Y : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left),
        (DU.boundedComponent P).rightOrthogonal Y →
        ∀ (K : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left),
          DT.perfectEnvelope P K →
          ∀ g : K ⟶ pull.functor.obj Y.obj, g = 0) :
    (DU.boundedComponent P).rightOrthogonal ≤
      ((DT.boundedComponent P).rightOrthogonal).inverseImage
        (pull.boundedFunctor hBounded) := by
  intro Y hY
  have hClosure : DT.quasicoherentComponent P ≤
      (ObjectProperty.singleton (pull.functor.obj Y.obj)).leftOrthogonal := by
    change (DT.perfectEnvelope P).coprodClosure.{u} ≤ _
    apply (DT.perfectEnvelope P).coprodClosure_le
      (Q := (ObjectProperty.singleton (pull.functor.obj Y.obj)).leftOrthogonal)
    intro K hK W g hW
    obtain rfl := (ObjectProperty.singleton_iff (pull.functor.obj Y.obj) W).mp hW
    exact hPerfect Y hY K hK g
  intro K g hK
  have hzero :
      (Dqc.SchemeBoundedCoherentDqcCategory.ι (X ⨯ T).left).map g = 0 := by
    exact hClosure K.obj hK _ (by simp)
  exact (Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).fullyFaithfulι.faithful.map_injective
    hzero

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData
