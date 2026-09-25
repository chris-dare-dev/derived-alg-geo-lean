/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatBaseChangeFunctors
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.ProjectionArrowExtension
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.ProjectionFunctorMate

/-!
# Conditional fixed-target arrow extension on bounded base-change components

The existing bounded pullback supplies an inclusion comparison, but not a
comparison with chosen right projectors. The first theorem retains a supplied
projector comparison and counit equation. Under triangulatedness and explicit
preservation of the right orthogonal, the later theorems construct both from
the canonical adjunction mate and apply the categorical transfer theorem.

It does not prove that geometric pullback preserves the right orthogonal, that
ambient bounded-coherent arrows descend, or any Noetherianity assertion.
-/

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

/-- An ambient bounded-coherent arrow lift transfers to the bounded
base-change component when pullback commutes, as a mate, with the chosen
right projectors. Both the ambient lift and this commutation are inputs. -/
theorem boundedPullback_fixedTargetArrowExtension_of_ambient
    (projectorIso :
      pull.boundedFunctor hBounded ⋙ pT.projection ≅
        pU.projection ⋙ boundedPullback DT DU P pull hDqc hBounded)
    (counit_compat :
      ∀ Y : Dqc.SchemeBoundedCoherentDqcCategory (X ⨯ U).left,
        pT.counitApp ((pull.boundedFunctor hBounded).obj Y) =
          (DT.boundedComponent P).ι.map ((projectorIso.app Y).hom) ≫
            ((boundedPullbackCompInclusion DT DU P pull hDqc hBounded).app
              (pU.project Y)).hom ≫
            (pull.boundedFunctor hBounded).map (pU.counitApp Y))
    (E : DU.BoundedCategory P)
    (hExt : Subobject.FixedTargetArrowExtension
      (pull.boundedFunctor hBounded) ((DU.boundedComponent P).ι.obj E)) :
    Subobject.FixedTargetArrowExtension
      (boundedPullback DT DU P pull hDqc hBounded) E := by
  exact pU.fixedTargetArrowExtension_of_ambient pT
    (pull.boundedFunctor hBounded)
    (boundedPullback DT DU P pull hDqc hBounded)
    (boundedPullbackCompInclusion DT DU P pull hDqc hBounded)
    projectorIso counit_compat E hExt

section OrthogonalPreservation

variable [(Dqc.schemeBoundedCoherentCohomology (X ⨯ U).left).IsTriangulated]
  [(Dqc.schemeBoundedCoherentCohomology (X ⨯ T).left).IsTriangulated]
  [(pull.boundedFunctor hBounded).CommShift ℤ]
  [(pull.boundedFunctor hBounded).IsTriangulated]

/-- Relative bounded pullback commutes with the chosen component projections
when it carries the source right orthogonal into the target right orthogonal.
This constructs the comparison as an adjunction mate, rather than requiring
the comparison as input. -/
noncomputable def boundedPullbackProjectionMateIso
    (hU : (DU.boundedComponent P).IsTriangulated)
    (hT : (DT.boundedComponent P).IsTriangulated)
    (horth : (DU.boundedComponent P).rightOrthogonal ≤
      ((DT.boundedComponent P).rightOrthogonal).inverseImage
        (pull.boundedFunctor hBounded)) :
    pull.boundedFunctor hBounded ⋙ pT.projection ≅
      pU.projection ⋙ boundedPullback DT DU P pull hDqc hBounded :=
  pU.projectionMateIso pT (pull.boundedFunctor hBounded)
    (boundedPullback DT DU P pull hDqc hBounded)
    (boundedPullbackCompInclusion DT DU P pull hDqc hBounded)
    hU hT horth

/-- The bounded-pullback projector comparison is the mate of the canonical
component-inclusion comparison, with its counit compatibility explicit. -/
theorem boundedPullbackProjectionMateIso_counit
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
  pU.projectionMateIso_counit pT (pull.boundedFunctor hBounded)
    (boundedPullback DT DU P pull hDqc hBounded)
    (boundedPullbackCompInclusion DT DU P pull hDqc hBounded)
    hU hT horth Y

include pU pT in
/-- Orthogonal preservation and an ambient fixed-target arrow lift suffice
for a fixed-target arrow lift on the actual bounded base-change component.
Neither projector commutation nor its counit equation is assumed. -/
lemma boundedPullback_fixedTargetArrowExtension_of_orthogonalPreservation
    (hU : (DU.boundedComponent P).IsTriangulated)
    (hT : (DT.boundedComponent P).IsTriangulated)
    (horth : (DU.boundedComponent P).rightOrthogonal ≤
      ((DT.boundedComponent P).rightOrthogonal).inverseImage
        (pull.boundedFunctor hBounded))
    (E : DU.BoundedCategory P)
    (hExt : Subobject.FixedTargetArrowExtension
      (pull.boundedFunctor hBounded) ((DU.boundedComponent P).ι.obj E)) :
    Subobject.FixedTargetArrowExtension
      (boundedPullback DT DU P pull hDqc hBounded) E := by
  exact boundedPullback_fixedTargetArrowExtension_of_ambient DT DU P pull hDqc hBounded
    pU pT
    (boundedPullbackProjectionMateIso DT DU P pull
      hDqc hBounded pU pT hU hT horth)
    (boundedPullbackProjectionMateIso_counit DT DU P pull hDqc hBounded
      pU pT hU hT horth)
    E hExt

end OrthogonalPreservation

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData
