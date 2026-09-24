/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.DerivedCategory.Families.KFlatBaseChangeFunctors
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.ProjectionArrowExtension

/-!
# Conditional fixed-target arrow extension on bounded base-change components

The existing bounded pullback supplies an inclusion comparison, but not a
comparison with chosen right projectors. Given that projector comparison,
its counit mate equation, and fixed-target arrow extension for the ambient
bounded-coherent pullback, the categorical transfer theorem applies.

This file proves no geometric arrow descent, projector commutation, or
Noetherianity assertion.
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

end AlgebraicGeometry.DerivedCategory.Families.SchemeBaseChange.DerivedBaseChangeData
