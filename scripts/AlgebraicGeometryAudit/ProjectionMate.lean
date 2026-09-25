import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.BaseChangeProjectionArrowExtension

/-! Axiom audit and direct bounded-pullback clients for the orthogonal-preservation mate. -/

#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData.boundedPullbackProjectionMateIso
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData.boundedPullbackProjectionMateIso_counit
#print axioms AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData.boundedPullback_fixedTargetArrowExtension_of_orthogonalPreservation

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData

variable {S : Scheme.{u}} {X T U : SchemeBaseChange S} {f : T ⟶ U}
  (DT : DerivedBaseChangeData X T) (DU : DerivedBaseChangeData X U)
  (P : ObjectProperty (Dqc.SchemeQuasicoherentDerivedCategory X.left))
  (pull : DqcLeftDerivedPullback (baseChangeMap X f))
  (hDqc : PullbackPreservesQuasicoherentComponent DT DU P pull)
  (hBounded : pull.PreservesBoundedCoherent)
  (pU : (DU.boundedComponent P).RightProjectionData)
  (pT : (DT.boundedComponent P).RightProjectionData)
  [(Dqc.schemeBoundedCoherentCohomology (X ⨯ U).left).IsTriangulated]
  [(Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated]
  [(pull.boundedFunctor hBounded).CommShift ℤ]
  [(pull.boundedFunctor hBounded).IsTriangulated]

-- The caller provides preservation of the right orthogonal, not a projector iso.
example
    (hU : (DU.boundedComponent P).IsTriangulated)
    (hT : (DT.boundedComponent P).IsTriangulated)
    (horth : (DU.boundedComponent P).rightOrthogonal ≤
      ((DT.boundedComponent P).rightOrthogonal).inverseImage
        (pull.boundedFunctor hBounded)) :
    pull.boundedFunctor hBounded ⋙ pT.projection ≅
      pU.projection ⋙ boundedPullback DT DU P pull hDqc hBounded :=
  boundedPullbackProjectionMateIso DT DU P pull
    hDqc hBounded pU pT hU hT horth

-- The same comparison satisfies the exact counit equation consumed below.
example
    (hU : (DU.boundedComponent P).IsTriangulated)
    (hT : (DT.boundedComponent P).IsTriangulated)
    (horth : (DU.boundedComponent P).rightOrthogonal ≤
      ((DT.boundedComponent P).rightOrthogonal).inverseImage
        (pull.boundedFunctor hBounded))
    (Y : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left) :
    pT.counitApp ((pull.boundedFunctor hBounded).obj Y) =
      (DT.boundedComponent P).ι.map
          (((boundedPullbackProjectionMateIso DT DU P pull hDqc hBounded
            pU pT hU hT horth).app Y).hom) ≫
        ((boundedPullbackCompInclusion DT DU P pull hDqc hBounded).app
          (pU.project Y)).hom ≫
        (pull.boundedFunctor hBounded).map (pU.counitApp Y) :=
  boundedPullbackProjectionMateIso_counit DT DU P pull hDqc hBounded
    pU pT hU hT horth Y

-- The same input now feeds the fixed-target transfer with the counit mate
-- synthesized by the source theorem.
example
    (hU : (DU.boundedComponent P).IsTriangulated)
    (hT : (DT.boundedComponent P).IsTriangulated)
    (horth : (DU.boundedComponent P).rightOrthogonal ≤
      ((DT.boundedComponent P).rightOrthogonal).inverseImage
        (pull.boundedFunctor hBounded))
    (E : DU.BoundedCategory P)
    (hExt : Subobject.FixedTargetArrowExtension
      (pull.boundedFunctor hBounded) ((DU.boundedComponent P).ι.obj E)) :
    Subobject.FixedTargetArrowExtension
      (boundedPullback DT DU P pull hDqc hBounded) E :=
  boundedPullback_fixedTargetArrowExtension_of_orthogonalPreservation DT DU P pull
    hDqc hBounded pU pT hU hT horth E hExt

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData
