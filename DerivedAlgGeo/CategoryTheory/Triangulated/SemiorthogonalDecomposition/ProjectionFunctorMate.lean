/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Mutation
import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Pullback of right projections from orthogonal preservation

For fully faithful component inclusions with chosen right projections, an
inclusion comparison has a canonical mate. If a triangulated functor sends the
source component's right orthogonal into the target component's right
orthogonal, the mate is invertible. Its inverse has the counit compatibility
needed to transfer fixed-target arrow extension.

No orthogonal-preservation assertion for a geometric pullback is made here.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.RightProjectionData

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  (p : P.RightProjectionData) (q : Q.RightProjectionData)
  (F : C ⥤ D) (G : P.FullSubcategory ⥤ Q.FullSubcategory)
  (inc : G ⋙ Q.ι ≅ P.ι ⋙ F)

/-- The canonical mate of the inclusion comparison. Its invertibility is a
separate claim, supplied below by orthogonal preservation. -/
private def projectionMate : p.projection ⋙ G ⟶ F ⋙ q.projection :=
  (mateEquiv p.adjunction q.adjunction) inc.hom

variable (hP : P.IsTriangulated) (hQ : Q.IsTriangulated)
  [F.CommShift ℤ] [F.IsTriangulated]
  (horth : P.rightOrthogonal ≤ (Q.rightOrthogonal).inverseImage F)

include hP hQ horth in
private lemma mappedCounit_isIso (Y : C) :
    IsIso (q.projection.map (F.map (p.counitApp Y))) := by
  let M := p.counitTriangle hP Y
  have hFM : Q.rightOrthogonal (F.obj M.mutation) := horth _ M.mutation_mem
  apply q.projectMap_isIso_of_distinguished hQ
    (F.map (p.counitApp Y)) (F.map M.toMutation)
    (F.map M.connecting ≫ (F.commShiftIso (1 : ℤ)).hom.app (p.projectObj Y))
  · exact F.map_distinguished _ M.distinguished
  · exact hFM

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
omit [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [Preadditive C] [HasShift C ℤ] [Preadditive D] [HasShift D ℤ]
  [F.CommShift ℤ] [F.IsTriangulated] in
private lemma projectionMate_app (Y : C) :
    (projectionMate p q F G inc).app Y =
      q.adjunction.unit.app (G.obj (p.project Y)) ≫
        q.projection.map ((inc.app (p.project Y)).hom) ≫
          q.projection.map (F.map (p.counitApp Y)) := by
  simp [projectionMate, mateEquiv]

include hP hQ horth in
private lemma projectionMate_app_isIso (Y : C) :
    IsIso ((projectionMate p q F G inc).app Y) := by
  letI : Q.ι.Full := Q.fullyFaithfulι.full
  letI : Q.ι.Faithful := Q.fullyFaithfulι.faithful
  letI : IsIso q.adjunction.unit := q.adjunction.unit_isIso_of_L_fully_faithful
  have hunit : IsIso (q.adjunction.unit.app (G.obj (p.project Y))) :=
    NatIso.isIso_app_of_isIso _ _
  have hinc : IsIso (q.projection.map ((inc.app (p.project Y)).hom)) := inferInstance
  have hcounit : IsIso (q.projection.map (F.map (p.counitApp Y))) :=
    mappedCounit_isIso p q F hP hQ horth Y
  rw [projectionMate_app]
  exact IsIso.comp_isIso'
    (f := q.adjunction.unit.app (G.obj (p.project Y)))
    (h := q.projection.map ((inc.app (p.project Y)).hom) ≫
      q.projection.map (F.map (p.counitApp Y)))
    hunit
    (IsIso.comp_isIso'
      (f := q.projection.map ((inc.app (p.project Y)).hom))
      (h := q.projection.map (F.map (p.counitApp Y)))
      hinc hcounit)

/-- A triangulated functor preserving the right orthogonal commutes with the
chosen right projections, by the inverse of the canonical adjunction mate. -/
noncomputable def projectionMateIso :
    F ⋙ q.projection ≅ p.projection ⋙ G := by
  let β := projectionMate p q F G inc
  haveI : IsIso β := (NatTrans.isIso_iff_isIso_app β).2
    (fun Y ↦ projectionMate_app_isIso p q F G inc hP hQ horth Y)
  exact (asIso β).symm

/-- The projector comparison constructed from orthogonal preservation is the
mate of the inclusion comparison, hence obeys the counit equation. -/
theorem projectionMateIso_counit (Y : C) :
    q.counitApp (F.obj Y) =
      Q.ι.map (((projectionMateIso p q F G inc hP hQ horth).app Y).hom) ≫
        (inc.app (p.project Y)).hom ≫ F.map (p.counitApp Y) := by
  let e := projectionMateIso p q F G inc hP hQ horth
  haveI : Epi (Q.ι.map (e.inv.app Y)) := inferInstance
  apply (cancel_epi (Q.ι.map (e.inv.app Y))).mp
  have hm := mateEquiv_counit p.adjunction q.adjunction inc.hom Y
  change Q.ι.map (e.inv.app Y) ≫ q.counitApp (F.obj Y) =
      (inc.app (p.project Y)).hom ≫ F.map (p.counitApp Y) at hm
  change Q.ι.map (e.inv.app Y) ≫ q.counitApp (F.obj Y) =
    Q.ι.map (e.inv.app Y) ≫ Q.ι.map (e.hom.app Y) ≫
      (inc.app (p.project Y)).hom ≫ F.map (p.counitApp Y)
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id,
    Category.id_comp]
  exact hm

end CategoryTheory.ObjectProperty.RightProjectionData
