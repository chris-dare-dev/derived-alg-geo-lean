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
between right-adjoint components given an inclusion comparison, a projector
comparison, and their counit mate equation. These are explicit premises of
the transfer theorem. No geometric pullback or projector commutation is
constructed here.
-/

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty.RightProjectionData

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  (p : P.RightProjectionData) (q : Q.RightProjectionData)
  (F : C ⥤ D) (G : P.FullSubcategory ⥤ Q.FullSubcategory)

set_option backward.isDefEq.respectTransparency false in
/-- Ambient all-arrow extension into an included component target transfers
to the restricted functor when the inclusion and projection comparisons are
mate-compatible. The projector comparison and counit equation are independent
premises; an inclusion comparison alone does not imply them. -/
theorem fixedTargetArrowExtension_of_ambient
    (inclusionIso : G ⋙ Q.ι ≅ P.ι ⋙ F)
    (projectionIso : F ⋙ q.projection ≅ p.projection ⋙ G)
    (counit_compat : ∀ Y : C,
      q.counitApp (F.obj Y) =
        Q.ι.map ((projectionIso.app Y).hom) ≫
          (inclusionIso.app (p.project Y)).hom ≫ F.map (p.counitApp Y))
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
  obtain ⟨Y, f, e, he⟩ := hExt (Q.ι.map β ≫ (inclusionIso.app X).hom)
  let g : p.project Y ⟶ X := P.ι.preimage (p.counitApp Y ≫ f)
  let e' : Z ≅ G.obj (p.project Y) :=
    (@asIso _ _ _ _ (q.adjunction.unit.app Z)
      (NatIso.isIso_app_of_isIso q.adjunction.unit Z)) ≪≫ q.projection.mapIso e ≪≫
      projectionIso.app Y
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
  have hcomm : Q.ι.map (G.map g) ≫ (inclusionIso.app X).hom =
      (inclusionIso.app (p.project Y)).hom ≫ F.map (P.ι.map g) :=
    inclusionIso.hom.naturality g
  have hfactor :
      Q.ι.map (e'.hom ≫ G.map g) ≫ (inclusionIso.app X).hom =
        e.hom ≫ F.map f := by
    change Q.ι.map (((asIso (q.adjunction.unit.app Z)).hom ≫
        q.projection.map e.hom ≫ (projectionIso.app Y).hom) ≫
        G.map g) ≫ (inclusionIso.app X).hom = e.hom ≫ F.map f
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
            (counit_compat Y).symm
      _ = Q.ι.map (q.adjunction.unit.app Z) ≫
          q.counitApp (Q.ι.obj Z) ≫ e.hom ≫ F.map f := by
        simpa only [Category.assoc] using
          congrArg (fun k => Q.ι.map (q.adjunction.unit.app Z) ≫
            k ≫ F.map f) hnat
      _ = e.hom ≫ F.map f := by
        simp only [← Category.assoc, htriangle]
        simp
  have hβ : Q.ι.map β ≫ (inclusionIso.app X).hom =
      Q.ι.map (e'.hom ≫ G.map g) ≫ (inclusionIso.app X).hom := by
    rw [hfactor]
    exact he
  exact (cancel_mono (inclusionIso.app X).hom).mp hβ

end CategoryTheory.ObjectProperty.RightProjectionData
