import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeShiftedGeneratorOrthogonal
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeProjectionArrowExtension

/-! Axiom audit and direct clients for the shifted external-product test. -/

#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData.perfectEnvelope_hom_eq_zero_of_shiftedExternalProducts
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData.boundedPullback_rightOrthogonal_of_shiftedExternalProducts

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S} {f : T ⟶ U}
  (DT : DerivedBaseChangeData X T) (DU : DerivedBaseChangeData X U)
  (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
  (pull : DqcLeftDerivedPullback (baseChangeMap X f))
  (hBounded : pull.PreservesBoundedCoherent)
  (hShifted :
    ∀ (Y : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left),
      (DU.boundedComponent P).rightOrthogonal Y →
      ∀ (F : SourcePerfectPartCategory X P) (G : CompactDqcFiber T) (n : ℤ)
        (g : ((((DT.externalProduct P).obj F).obj G)⟦n⟧ ⟶
          pull.functor.obj Y.obj)), g = 0)

-- The geometric vanishing is assumed on every integer shift, then extended.
example (Y : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left)
    (hY : (DU.boundedComponent P).rightOrthogonal Y)
    (K : Dqc.SchemeQuasicoherentDerivedCategory (X ⨯ T).left)
    (hK : DT.perfectEnvelope P K) (g : K ⟶ pull.functor.obj Y.obj) :
    g = 0 :=
  perfectEnvelope_hom_eq_zero_of_shiftedExternalProducts DT DU P pull
    hShifted Y hY K hK g

-- The exact 4bg premise is obtained without assuming `horth`.
example : (DU.boundedComponent P).rightOrthogonal ≤
    ((DT.boundedComponent P).rightOrthogonal).inverseImage
      (pull.boundedFunctor hBounded) :=
  boundedPullback_rightOrthogonal_of_shiftedExternalProducts
    DT DU P pull hBounded hShifted

variable (hDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
  (pU : (DU.boundedComponent P).RightProjectionData)
  (pT : (DT.boundedComponent P).RightProjectionData)
  [(Dqc.schemeBoundedCoherentCohomology (X ⨯ U).left).IsTriangulated]
  [(Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated]
  [(pull.boundedFunctor hBounded).CommShift ℤ]
  [(pull.boundedFunctor hBounded).IsTriangulated]

-- The resulting orthogonality feeds the existing projector mate.
example
    (hU : (DU.boundedComponent P).IsTriangulated)
    (hT : (DT.boundedComponent P).IsTriangulated) :
    pull.boundedFunctor hBounded ⋙ pT.projection ≅
      pU.projection ⋙ boundedPullback DT DU P pull hDqc hBounded :=
  boundedPullbackProjectionMateIso DT DU P pull hDqc hBounded pU pT hU hT
    (boundedPullback_rightOrthogonal_of_shiftedExternalProducts
      DT DU P pull hBounded hShifted)

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData
