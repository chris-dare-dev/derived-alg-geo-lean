import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangePerfectEnvelopeOrthogonal
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeProjectionArrowExtension

/-! Axiom audit and direct clients for the perfect-envelope orthogonality test. -/

#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData.boundedPullback_rightOrthogonal_of_perfectEnvelope

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S} {f : T ⟶ U}
  (DT : DerivedBaseChangeData X T) (DU : DerivedBaseChangeData X U)
  (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
  (pull : DqcLeftDerivedPullback (baseChangeMap X f))
  (hBounded : pull.PreservesBoundedCoherent)
  (hPerfect :
    ∀ (Y : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left),
      (DU.boundedComponent P).rightOrthogonal Y →
      ∀ (K : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left),
        DT.perfectEnvelope P K →
        ∀ g : K ⟶ pull.functor.obj Y.obj, g = 0)

-- The caller supplies only vanishing on the perfect envelope, not `horth`.
example : (DU.boundedComponent P).rightOrthogonal ≤
    ((DT.boundedComponent P).rightOrthogonal).inverseImage
      (pull.boundedFunctor hBounded) :=
  boundedPullback_rightOrthogonal_of_perfectEnvelope DT DU P pull hBounded hPerfect

variable (hDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
  (pU : (DU.boundedComponent P).RightProjectionData)
  (pT : (DT.boundedComponent P).RightProjectionData)
  [(Dqc.schemeBoundedCoherentCohomology (X ⨯ U).left).IsTriangulated]
  [(Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated]
  [(pull.boundedFunctor hBounded).CommShift ℤ]
  [(pull.boundedFunctor hBounded).IsTriangulated]

-- The reduction feeds the existing 4bc mate without a supplied projector iso.
example
    (hU : (DU.boundedComponent P).IsTriangulated)
    (hT : (DT.boundedComponent P).IsTriangulated) :
    pull.boundedFunctor hBounded ⋙ pT.projection ≅
      pU.projection ⋙ boundedPullback DT DU P pull hDqc hBounded :=
  boundedPullbackProjectionMateIso DT DU P pull hDqc hBounded pU pT hU hT
    (boundedPullback_rightOrthogonal_of_perfectEnvelope DT DU P pull hBounded hPerfect)

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData
