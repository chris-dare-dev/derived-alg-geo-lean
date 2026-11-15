/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import DerivedAlgGeo.CategoryTheory.Bicategory.Functor.Cat.ULift

/-!
# Descent for universe lifts

The universe lift `F.ulift.{w₁, w₂}` of a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`
has the same descent theory as `F`: descent data of `F` and of `F.ulift` are equivalent,
compatibly with restriction from the base. Hence `F.ulift` is a prestack (a stack) exactly
when `F` is.

## Main definitions

* `Pseudofunctor.DescentData.uliftEquivalence F f`: the equivalence
  `F.DescentData f ≌ (F.ulift.{w₁, w₂}).DescentData f`, which applies
  `Pseudofunctor.ulift.objEquivalence` componentwise.
* `Pseudofunctor.toDescentDataCompUliftFunctorIso F f`: restriction to descent data commutes
  with the lift.

## Main results

* `Pseudofunctor.isPrestack_ulift_iff`: `F.ulift` is a prestack exactly when `F` is.
* `Pseudofunctor.isStack_ulift_iff`: `F.ulift` is a stack exactly when `F` is.

## Implementation notes

`F` and `F.ulift` take values in different bicategories `Cat.{v', u'}` and
`Cat.{max v' w₁, max u' w₂}`, so no strong transformation relates them and
`Pseudofunctor.isStack_iff_of_isEquivalence` does not apply. The descent-data equivalence is
built directly. Its unit and counit have identity components, because the fibrewise
equivalence `ULiftHomULiftCategory.equiv` has strict inverses on objects and morphisms. The
stack condition is then compared one covering sieve at a time, as in
`DerivedAlgGeo/CategoryTheory/Sites/Descent/IsStack.lean`.

## References

* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W): equivalences over the
  base transport morphism sheaves and effectiveness of descent.

## Tags

descent data, stack, prestack, universe lift
-/

universe w₁ w₂ t v' u' v u

namespace CategoryTheory.Pseudofunctor

open Opposite Bicategory LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

namespace DescentData

/-- Lift a descent datum of `F` to one of `F.ulift`, componentwise along
`Pseudofunctor.ulift.objEquivalence`. -/
@[simps]
def uliftFunctor : F.DescentData f ⥤ (F.ulift.{w₁, w₂}).DescentData f where
  obj D :=
    { obj i := (ulift.objEquivalence.{w₁, w₂} F _).functor.obj (D.obj i)
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        (ulift.objEquivalence.{w₁, w₂} F _).functor.map (D.hom q f₁ f₂ hf₁ hf₂)
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [← D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
        dsimp only [pullHom]
        rw [ulift.mapComp'_hom_app, ulift.mapComp'_inv_app]
        rfl
      hom_self Y q i g hg := by
        rw [D.hom_self q g hg]
        exact (ulift.objEquivalence.{w₁, w₂} F (.mk (op Y))).functor.map_id _
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        congrArg (ulift.objEquivalence.{w₁, w₂} F (.mk (op Y))).functor.map
          (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) }
  map {D₁ D₂} φ :=
    { hom i := (ulift.objEquivalence.{w₁, w₂} F _).functor.map (φ.hom i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        congrArg (ulift.objEquivalence.{w₁, w₂} F (.mk (op Y))).functor.map
          (φ.comm q f₁ f₂ hf₁ hf₂) }

/-- Lower a descent datum of `F.ulift` to one of `F`, componentwise along
`Pseudofunctor.ulift.objEquivalence`. -/
@[simps]
def uliftInverse : (F.ulift.{w₁, w₂}).DescentData f ⥤ F.DescentData f where
  obj D :=
    { obj i := (ulift.objEquivalence.{w₁, w₂} F _).inverse.obj (D.obj i)
      hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        (ulift.objEquivalence.{w₁, w₂} F _).inverse.map (D.hom q f₁ f₂ hf₁ hf₂)
      pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
        rw [← D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂]
        dsimp only [pullHom]
        rw [ulift.mapComp'_hom_app, ulift.mapComp'_inv_app]
        rfl
      hom_self Y q i g hg := by
        rw [D.hom_self q g hg]
        exact (ulift.objEquivalence.{w₁, w₂} F (.mk (op Y))).inverse.map_id _
      hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ :=
        congrArg (ulift.objEquivalence.{w₁, w₂} F (.mk (op Y))).inverse.map
          (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃) }
  map {D₁ D₂} φ :=
    { hom i := (ulift.objEquivalence.{w₁, w₂} F _).inverse.map (φ.hom i)
      comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
        congrArg (ulift.objEquivalence.{w₁, w₂} F (.mk (op Y))).inverse.map
          (φ.comm q f₁ f₂ hf₁ hf₂) }

/-- Descent data of `F` and of its universe lift `F.ulift` are equivalent. The unit and
counit are identities. -/
@[simps! functor inverse]
def uliftEquivalence : F.DescentData f ≌ (F.ulift.{w₁, w₂}).DescentData f :=
  Equivalence.mk (uliftFunctor F f) (uliftInverse F f) (Iso.refl _) (Iso.refl _)

end DescentData

/-- The gluing morphisms of the restriction of a lifted object are the lifts of the gluing
morphisms of the restriction. -/
lemma toDescentData_ulift_obj_hom (M : F.obj (.mk (op S))) {Y : C} (q : Y ⟶ S) {i₁ i₂ : ι}
    (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (((F.ulift.{w₁, w₂}).toDescentData f).obj
        ((ulift.objEquivalence.{w₁, w₂} F _).functor.obj M)).hom q f₁ f₂ hf₁ hf₂ =
      (ulift.objEquivalence.{w₁, w₂} F (.mk (op Y))).functor.map
        (((F.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂) := by
  change ((F.ulift.{w₁, w₂}).mapComp' (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc _).inv.toNatTrans.app
      _ ≫ ((F.ulift.{w₁, w₂}).mapComp' (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc _).hom.toNatTrans.app
      _ = _
  rw [ulift.mapComp'_inv_app, ulift.mapComp'_hom_app]
  rfl

/-- Restriction to descent data commutes with the universe lift: the square formed by
`Pseudofunctor.DescentData.uliftEquivalence` and `Pseudofunctor.ulift.objEquivalence` commutes
up to an isomorphism with identity components. -/
@[simps!]
def toDescentDataCompUliftFunctorIso :
    F.toDescentData f ⋙ (DescentData.uliftEquivalence.{w₁, w₂} F f).functor ≅
      (ulift.objEquivalence.{w₁, w₂} F (.mk (op S))).functor ⋙
        (F.ulift.{w₁, w₂}).toDescentData f :=
  NatIso.ofComponents
    (fun M ↦ DescentData.isoMk (fun i ↦ Iso.refl _) (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
      erw [Functor.map_id, Functor.map_id, Category.id_comp, Category.comp_id]
      exact toDescentData_ulift_obj_hom F f M q f₁ f₂ hf₁ hf₂))
    (fun φ ↦ by
      ext i
      exact (Category.comp_id _).trans (Category.id_comp _).symm)

private lemma isPrestackFor_ulift_iff {S : C} (R : Sieve S) :
    (F.ulift.{w₁, w₂}).IsPrestackFor R.arrows ↔ F.IsPrestackFor R.arrows := by
  let e := toDescentDataCompUliftFunctorIso.{w₁, w₂} F (fun (a : R.arrows.category) ↦ a.obj.hom)
  let a := ulift.objEquivalence.{w₁, w₂} F (.mk (op S))
  let b := DescentData.uliftEquivalence.{w₁, w₂} F (fun (a : R.arrows.category) ↦ a.obj.hom)
  simp only [isPrestackFor_iff]
  refine ⟨fun ⟨h⟩ ↦ ⟨?_⟩, fun ⟨h⟩ ↦ ⟨?_⟩⟩
  · exact Functor.FullyFaithful.ofCompFaithful (G := b.functor)
      ((a.fullyFaithfulFunctor.comp h).ofIso e.symm)
  · exact (a.fullyFaithfulInverse.comp ((h.comp b.fullyFaithfulFunctor).ofIso e)).ofIso
      (a.invFunIdAssoc _)

private lemma isStackFor_ulift_iff {S : C} (R : Sieve S) :
    (F.ulift.{w₁, w₂}).IsStackFor R.arrows ↔ F.IsStackFor R.arrows := by
  let e := toDescentDataCompUliftFunctorIso.{w₁, w₂} F (fun (a : R.arrows.category) ↦ a.obj.hom)
  simp only [isStackFor_iff]
  refine ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩
  · have := Functor.isEquivalence_of_iso e.symm
    exact Functor.isEquivalence_of_comp_right _
      (DescentData.uliftEquivalence.{w₁, w₂} F _).functor
  · have := Functor.isEquivalence_of_iso e
    exact Functor.isEquivalence_of_comp_left
      (ulift.objEquivalence.{w₁, w₂} F (.mk (op S))).functor _

/-- Descent of morphisms is unchanged by the universe lift. -/
theorem isPrestack_ulift_iff (J : GrothendieckTopology C) :
    (F.ulift.{w₁, w₂}).IsPrestack J ↔ F.IsPrestack J :=
  ⟨fun _ ↦ .of_isPrestackFor fun _ R hR ↦
      (isPrestackFor_ulift_iff F R).1 ((F.ulift.{w₁, w₂}).isPrestackFor' R hR),
    fun _ ↦ .of_isPrestackFor fun _ R hR ↦
      (isPrestackFor_ulift_iff F R).2 (F.isPrestackFor' R hR)⟩

/-- Being a stack is unchanged by the universe lift: [Stacks Project, Tag 042W] applied to the
fibrewise equivalences `Pseudofunctor.ulift.objEquivalence`, across universes. No hypothesis
beyond the base being locally discrete is needed. -/
theorem isStack_ulift_iff (J : GrothendieckTopology C) :
    (F.ulift.{w₁, w₂}).IsStack J ↔ F.IsStack J :=
  ⟨fun _ ↦ .of_isStackFor fun _ R hR ↦
      (isStackFor_ulift_iff F R).1 ((F.ulift.{w₁, w₂}).isStackFor' R hR),
    fun _ ↦ .of_isStackFor fun _ R hR ↦
      (isStackFor_ulift_iff F R).2 (F.isStackFor' R hR)⟩

end CategoryTheory.Pseudofunctor
