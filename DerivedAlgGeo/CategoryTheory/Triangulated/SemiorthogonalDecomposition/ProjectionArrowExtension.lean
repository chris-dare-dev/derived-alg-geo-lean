/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.SubobjectEquivalence
import DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Projection
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Fixed-target arrow extension through compatible right projections

An ambient functor's fixed-target arrow extension passes to its restriction
between right-adjoint components when the functor is compatible with
the chosen projections. The comparison below includes both the inclusion
square and the projector square, together with their counit mate equation.
No geometric pullback or projector commutation is constructed here.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.RightProjectionData

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  (p : P.RightProjectionData) (q : Q.RightProjectionData)
  (F : C ⥤ D) (G : P.FullSubcategory ⥤ Q.FullSubcategory)

/-- A mate-compatible comparison between an ambient functor and its
restriction to two chosen right-adjoint components. The inclusion
comparison alone does not imply the projector comparison. -/
structure CompatibleFunctor where
  /-- The restricted functor agrees with the ambient functor after inclusion. -/
  inclusionIso : G ⋙ Q.ι ≅ P.ι ⋙ F
  /-- The ambient functor commutes with the chosen right projectors. -/
  projectionIso : F ⋙ q.projection ≅ p.projection ⋙ G
  /-- The two comparisons commute with the projection counits. -/
  counit_compat (Y : C) :
    q.counitApp (F.obj Y) =
      Q.ι.map ((projectionIso.app Y).hom) ≫
        (inclusionIso.app (p.project Y)).hom ≫ F.map (p.counitApp Y)

namespace CompatibleFunctor

variable {p : P.RightProjectionData} {q : Q.RightProjectionData}
  {F : C ⥤ D} {G : P.FullSubcategory ⥤ Q.FullSubcategory}

set_option backward.isDefEq.respectTransparency false in
/-- Ambient all-arrow extension into an included component target transfers
to the restricted functor when the projection comparison is mate-compatible.
This does not establish either ambient extension or the comparison. -/
theorem fixedTargetArrowExtension_of_ambient
    (H : CompatibleFunctor p q F G)
    (X : P.FullSubcategory)
    (hExt : Subobject.FixedTargetArrowExtension F (P.ι.obj X)) :
    Subobject.FixedTargetArrowExtension G X := by
  letI : P.ι.Full := P.fullyFaithfulι.full
  letI : Q.ι.Full := Q.fullyFaithfulι.full
  letI : Q.ι.Faithful := Q.fullyFaithfulι.faithful
  letI : IsIso q.adjunction.unit :=
    q.adjunction.unit_isIso_of_L_fully_faithful
  intro Z β
  letI : IsIso (q.adjunction.unit.app Z) :=
    NatIso.isIso_app_of_isIso _ _
  obtain ⟨Y, f, e, he⟩ := hExt (Q.ι.map β ≫ (H.inclusionIso.app X).hom)
  let g : p.project Y ⟶ X := P.ι.preimage (p.counitApp Y ≫ f)
  let e' : Z ≅ G.obj (p.project Y) :=
    (@asIso _ _ _ _ (q.adjunction.unit.app Z)
      (NatIso.isIso_app_of_isIso q.adjunction.unit Z)) ≪≫ q.projection.mapIso e ≪≫
      H.projectionIso.app Y
  refine ⟨p.project Y, g, e', ?_⟩
  apply Q.ι.map_injective
  have hg : P.ι.map g = p.counitApp Y ≫ f := P.ι.map_preimage _
  have htriangle : Q.ι.map (q.adjunction.unit.app Z) ≫
      q.counitApp (Q.ι.obj Z) = 𝟙 (Q.ι.obj Z) :=
    q.adjunction.left_triangle_components Z
  have hnat : Q.ι.map (q.projection.map e.hom) ≫
      q.counitApp (F.obj Y) =
        q.counitApp (Q.ι.obj Z) ≫ e.hom :=
    q.adjunction.counit.naturality e.hom
  have hcomm : Q.ι.map (G.map g) ≫ (H.inclusionIso.app X).hom =
      (H.inclusionIso.app (p.project Y)).hom ≫ F.map (P.ι.map g) :=
    H.inclusionIso.hom.naturality g
  have hfactor :
      Q.ι.map (e'.hom ≫ G.map g) ≫ (H.inclusionIso.app X).hom =
        e.hom ≫ F.map f := by
    change Q.ι.map (((asIso (q.adjunction.unit.app Z)).hom ≫
        q.projection.map e.hom ≫ (H.projectionIso.app Y).hom) ≫
        G.map g) ≫ (H.inclusionIso.app X).hom = e.hom ≫ F.map f
    rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    erw [hcomm, hg, F.map_comp]
    calc
      _ = Q.ι.map (q.adjunction.unit.app Z) ≫
          Q.ι.map (q.projection.map e.hom) ≫
          q.counitApp (F.obj Y) ≫ F.map f := by
        simpa only [Category.assoc, asIso_hom] using
          congrArg (fun k => Q.ι.map (q.adjunction.unit.app Z) ≫
            Q.ι.map (q.projection.map e.hom) ≫ k ≫ F.map f)
            (H.counit_compat Y).symm
      _ = Q.ι.map (q.adjunction.unit.app Z) ≫
          q.counitApp (Q.ι.obj Z) ≫ e.hom ≫ F.map f := by
        simpa only [Category.assoc] using
          congrArg (fun k => Q.ι.map (q.adjunction.unit.app Z) ≫
            k ≫ F.map f) hnat
      _ = e.hom ≫ F.map f := by
        simp only [← Category.assoc, htriangle]
        simp
  have hβ : Q.ι.map β ≫ (H.inclusionIso.app X).hom =
      Q.ι.map (e'.hom ≫ G.map g) ≫ (H.inclusionIso.app X).hom := by
    rw [hfactor]
    exact he
  exact (cancel_mono (H.inclusionIso.app X).hom).mp hβ

end CompatibleFunctor

end CategoryTheory.ObjectProperty.RightProjectionData
