/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangePerfectEnvelopeOrthogonal
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Basic

/-!
# Testing bounded pullback orthogonality on shifted external products

Vanishing of maps from every integer shift of each target external-product
generator extends through the triangulated perfect envelope. The hypothesis is
still geometric: no relative Hom base-change theorem or preservation of right
orthogonals is inferred from component-image preservation.
-/

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData

open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S} {f : T ⟶ U}
  (DT : DerivedBaseChangeData X T) (DU : DerivedBaseChangeData X U)
  (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
  (pull : DqcLeftDerivedPullback (baseChangeMap X f))

/-- Vanishing for all shifts of the external-product generators implies
vanishing for their whole target perfect envelope. The shifted hypothesis is
essential for the triangulated-envelope step. -/
theorem perfectEnvelope_hom_eq_zero_of_shiftedExternalProducts
    (hShifted :
      ∀ (Y : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left),
        (DU.boundedComponent P).rightOrthogonal Y →
        ∀ (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) (n : ℤ)
          (g : ((((DT.externalProduct P).obj F).obj G)⟦n⟧ ⟶
            pull.functor.obj Y.obj)), g = 0) :
    ∀ (Y : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left),
      (DU.boundedComponent P).rightOrthogonal Y →
      ∀ (K : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left),
        DT.perfectEnvelope P K →
        ∀ g : K ⟶ pull.functor.obj Y.obj, g = 0 := by
  intro Y hY K hK g
  let Z : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left :=
    pull.functor.obj Y.obj
  have hGenerators : (DT.shiftedPerfectGenerators P).rightOrthogonal Z := by
    intro V q hV
    rcases hV with ⟨E, n, e, F, G, ⟨eFG⟩⟩
    let eSource : ((((DT.externalProduct P).obj F).obj G)⟦n⟧) ≅ V :=
      ((shiftFunctor (Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left) n).mapIso
        eFG).trans e.symm
    have hzero := hShifted Y hY F G n (eSource.hom ≫ q)
    calc
      q = eSource.inv ≫ (eSource.hom ≫ q) := by simp
      _ = 0 := by simp [hzero]
  have hTargetShifts :
      (ObjectProperty.singleton Z).shiftClosure ℤ ≤
        (DT.shiftedPerfectGenerators P).rightOrthogonal := by
    rw [ObjectProperty.shiftClosure_le_iff]
    intro V hV
    obtain rfl := (ObjectProperty.singleton_iff Z V).mp hV
    exact hGenerators
  have hEnvelope :
      (DT.shiftedPerfectGenerators P).triangEnvelope ≤
        ((ObjectProperty.singleton Z).shiftClosure ℤ).leftOrthogonal := by
    rw [ObjectProperty.triangEnvelope_le_iff]
    intro V hV W q hW
    exact hTargetShifts W hW q hV
  have hKshift : (DT.shiftedPerfectGenerators P).triangEnvelope K := by
    exact (ObjectProperty.monotone_triangEnvelope
      (ObjectProperty.le_shiftClosure (DT.perfectGenerators P))) K hK
  exact hEnvelope K hKshift g
    ((ObjectProperty.le_shiftClosure (ObjectProperty.singleton Z)) Z
      ((ObjectProperty.singleton_iff Z Z).2 rfl))

/-- The shifted-generator test supplies the explicit perfect-envelope
vanishing premise of `boundedPullback_rightOrthogonal_of_perfectEnvelope`. -/
theorem boundedPullback_rightOrthogonal_of_shiftedExternalProducts
    (hBounded : pull.PreservesBoundedCoherent)
    (hShifted :
      ∀ (Y : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left),
        (DU.boundedComponent P).rightOrthogonal Y →
        ∀ (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) (n : ℤ)
          (g : ((((DT.externalProduct P).obj F).obj G)⟦n⟧ ⟶
            pull.functor.obj Y.obj)), g = 0) :
    (DU.boundedComponent P).rightOrthogonal ≤
      ((DT.boundedComponent P).rightOrthogonal).inverseImage
        (pull.boundedFunctor hBounded) :=
  boundedPullback_rightOrthogonal_of_perfectEnvelope DT DU P pull hBounded
    (perfectEnvelope_hom_eq_zero_of_shiftedExternalProducts DT DU P pull hShifted)

end

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData
