/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.Algebra.Homology.SpectralSequence.FiniteStripTotal
import DerivedAlgGeo.Algebra.Homology.TotalComplex
import Mathlib.Algebra.Homology.BifunctorFlip
import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Finite-support bifunctor maps and colimits of cochain totals

Mathlib's `HomologicalComplex.mapBifunctorMap` is a map between direct-sum totals.
When the fixed input complex has finitely supported terms, a columnwise
quasi-isomorphism criterion for literal bicomplex totals applies to this map.
The same literal total preserves a diagram-shape colimit in either varying slot
when the corresponding partial bifunctor preserves it termwise.

## Main definitions

This module introduces no new public definitions; it studies Mathlib's existing
`HomologicalComplex.mapBifunctorMap` and `CategoryTheory.Functor.map₂CochainComplex`.

## Main results

* `HomologicalComplex.quasiIso_mapBifunctorMap_id_left_of_finite_support_of_column_quasiIso` passes
  quasi-isomorphic mapped columns in the second input to a quasi-isomorphism
  of literal totals under finite term support in the first.
* `HomologicalComplex.quasiIso_mapBifunctorMap_id_right_of_finite_support_of_column_quasiIso`
  fixes finite support in the second input and maps the first by signed flip.
* `CategoryTheory.Functor.map₂CochainComplex_obj_preservesColimitsOfShape` and
  `CategoryTheory.Functor.map₂CochainComplex_flip_obj_preservesColimitsOfShape`
  preserve a colimit in either varying slot from termwise preservation by the
  corresponding partial bifunctor.

## Implementation notes

The fixed complex supplies the finite horizontal support strip for both
bicomplexes. The finite-strip total-map criterion needs columnwise evidence
only inside it; the right-slot result uses naturality of Mathlib's signed flip.
For colimits, two evaluations reduce the mapped bicomplex to the partial
base functor at each bidegree. The existing total-functor colimit theorem
then applies; private natural isomorphisms identify its composite with
Mathlib's literal cochain map₂ functor in each slot.

## References

These results extend Mathlib's `HomologicalComplex.mapBifunctorMap` and use
`HomologicalComplex₂.totalMap_quasiIso_of_finiteStrip`. The colimit results use
`HomologicalComplex₂.totalFunctor_preservesColimitsOfShape`.

## Tags

bifunctor, cochain complex, quasi-isomorphism, finite support, colimit
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace HomologicalComplex

open ComplexShape

set_option backward.isDefEq.respectTransparency false

/-- Finite term support in the first complex lets columnwise quasi-isomorphisms
pass through Mathlib's literal bifunctor total map. Only columns within the
support interval need quasi-isomorphism evidence. The second map is unrestricted;
the bounds concern terms, not cohomology. -/
theorem quasiIso_mapBifunctorMap_id_left_of_finite_support_of_column_quasiIso
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Abelian D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex C₁ ℤ) {L M : CochainComplex C₂ ℤ} (f : L ⟶ M)
    [HasMapBifunctor K L F (up ℤ)] [HasMapBifunctor K M F (up ℤ)]
    (a b : ℤ)
    (hLower : ∀ p, p < a → IsZero (K.X p))
    (hUpper : ∀ p, b < p → IsZero (K.X p))
    (hcol : ∀ p, a ≤ p → p ≤ b →
      QuasiIso (((F.obj (K.X p)).mapHomologicalComplex (up ℤ)).map f)) :
    QuasiIso (mapBifunctorMap (𝟙 K) f F (up ℤ)) := by
  let B := F.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)
  have ht := HomologicalComplex₂.totalMap_quasiIso_of_finiteStrip
    ((B.obj K).map f) a b
    (fun p q hp => by
      rcases hp with hpa | hpb
      · exact (F.flip.obj (L.X q)).map_isZero (hLower p hpa)
      · exact (F.flip.obj (L.X q)).map_isZero (hUpper p hpb))
    (fun p q hp => by
      rcases hp with hpa | hpb
      · exact (F.flip.obj (M.X q)).map_isZero (hLower p hpa)
      · exact (F.flip.obj (M.X q)).map_isZero (hUpper p hpb))
    (fun p hpa hpb => hcol p hpa hpb)
  change QuasiIso (HomologicalComplex₂.total.map
    ((B.map (𝟙 K)).app L ≫ (B.obj K).map f) (up ℤ))
  rw [B.map_id, NatTrans.id_app, Category.id_comp]
  exact ht

/-- Signed flipping turns finite term support in the second complex into the
left-slot criterion, without a symmetric monoidal structure. Only supported
columns need quasi-isomorphism evidence. -/
theorem quasiIso_mapBifunctorMap_id_right_of_finite_support_of_column_quasiIso
    {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Abelian D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex C₂ ℤ) {L M : CochainComplex C₁ ℤ} (f : L ⟶ M)
    [HasMapBifunctor L K F (up ℤ)] [HasMapBifunctor M K F (up ℤ)]
    (a b : ℤ)
    (hLower : ∀ p, p < a → IsZero (K.X p))
    (hUpper : ∀ p, b < p → IsZero (K.X p))
    (hcol : ∀ p, a ≤ p → p ≤ b →
      QuasiIso (((F.flip.obj (K.X p)).mapHomologicalComplex (up ℤ)).map f)) :
    QuasiIso (mapBifunctorMap f (𝟙 K) F (up ℤ)) := by
  haveI := quasiIso_mapBifunctorMap_id_left_of_finite_support_of_column_quasiIso
    F.flip K f a b hLower hUpper hcol
  have hnat := mapBifunctorFlipIso_hom_naturality f (𝟙 K) F (up ℤ)
  apply (quasiIso_iff_comp_left (mapBifunctorFlipIso L K F (up ℤ)).hom _).mp
  rw [← hnat]
  infer_instance

end HomologicalComplex

namespace CategoryTheory.Functor

open ComplexShape

universe u₁ u₂ u₃ v₁ v₂ v₃ w z

set_option backward.isDefEq.respectTransparency false in
private theorem bicomplex_left
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₂] [HasColimitsOfShape J D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ X, PreservesColimitsOfShape J (F.obj X)]
    (K : CochainComplex C₁ ℤ) :
    PreservesColimitsOfShape J
      ((F.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro p
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro q
  change PreservesColimitsOfShape J
    (HomologicalComplex.eval C₂ (up ℤ) q ⋙ F.obj (K.X p))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem bicomplex_right
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₁] [HasColimitsOfShape J D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ Y, PreservesColimitsOfShape J (F.flip.obj Y)]
    (K : CochainComplex C₂ ℤ) :
    PreservesColimitsOfShape J
      ((F.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).flip.obj K) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro p
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro q
  change PreservesColimitsOfShape J
    (HomologicalComplex.eval C₁ (up ℤ) p ⋙ F.flip.obj (K.X q))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private def totalIso_left
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasCountableCoproducts D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex C₁ ℤ) :
    (F.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj K ⋙
      HomologicalComplex₂.totalFunctor D (up ℤ) (up ℤ) (up ℤ) ≅
    F.map₂CochainComplex.obj K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp [HomologicalComplex.mapBifunctorMap])

set_option backward.isDefEq.respectTransparency false in
private def totalIso_right
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasCountableCoproducts D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    (K : CochainComplex C₂ ℤ) :
    (F.mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).flip.obj K ⋙
      HomologicalComplex₂.totalFunctor D (up ℤ) (up ℤ) (up ℤ) ≅
    F.map₂CochainComplex.flip.obj K :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros
    simp [HomologicalComplex.mapBifunctorMap])

/-- Fixing the first cochain complex in Mathlib's literal bifunctor total
preserves colimits of shape `J` when each partial base functor does. The
countable coproducts construct every diagonal total; no exactness or homology
preservation is required. -/
theorem map₂CochainComplex_obj_preservesColimitsOfShape
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasCountableCoproducts D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₂] [HasColimitsOfShape J D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ X, PreservesColimitsOfShape J (F.obj X)]
    (K : CochainComplex C₁ ℤ) :
    PreservesColimitsOfShape J (F.map₂CochainComplex.obj K) := by
  letI := bicomplex_left (J := J) F K
  exact preservesColimitsOfShape_of_natIso (totalIso_left F K)

/-- Fixing the second cochain complex preserves colimits of shape `J` when
the corresponding partial functors in the first slot do. This is the
flipped-slot counterpart for the same literal direct-sum total. -/
theorem map₂CochainComplex_flip_obj_preservesColimitsOfShape
    {C₁ : Type u₁} [Category.{v₁} C₁] [HasZeroMorphisms C₁]
    {C₂ : Type u₂} [Category.{v₂} C₂] [HasZeroMorphisms C₂]
    {D : Type u₃} [Category.{v₃} D] [Preadditive D] [HasCountableCoproducts D]
    {J : Type w} [Category.{z} J]
    [HasColimitsOfShape J C₁] [HasColimitsOfShape J D]
    (F : C₁ ⥤ C₂ ⥤ D) [F.PreservesZeroMorphisms]
    [∀ X, (F.obj X).PreservesZeroMorphisms]
    [∀ Y, PreservesColimitsOfShape J (F.flip.obj Y)]
    (K : CochainComplex C₂ ℤ) :
    PreservesColimitsOfShape J (F.map₂CochainComplex.flip.obj K) := by
  letI := bicomplex_right (J := J) F K
  exact preservesColimitsOfShape_of_natIso (totalIso_right F K)

end CategoryTheory.Functor
